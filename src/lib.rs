//! Stable-address slot map with permanent links and shared insertion.
//! Shared reads return the value and its atomic link. Exclusive table access
//! permits replacing the entire tuple; unsafe shared access only borrows T mutably.
//! ```compile_fail
//! use pi_slot::{DefaultKey, SlotMap};
//! let map = SlotMap::<DefaultKey, u32>::new();
//! map.insert(1);
//! map.iter().next().unwrap().1.0 = 2;
//! ```
//! ```compile_fail
//! use pi_slot::{DefaultKey, SlotMap};
//! let mut map = SlotMap::<DefaultKey, u32>::new();
//! let key = map.insert(1);
//! let value = map.get(key).unwrap();
//! map.remove(key);
//! println!("{value:?}");
//! ```

#[cfg(test)]
#[path = "../tests/support/private.rs"]
mod private_tests;

use std::cell::UnsafeCell;
use std::fmt::{self, Debug, Formatter};
use std::marker::PhantomData;
use std::mem::{size_of, MaybeUninit};
use std::ops::{Index, IndexMut};
use std::ptr;
use std::sync::atomic::Ordering;

use pi_arr::SegmentedArr;
pub use pi_key::{DefaultKey, Key, KeyData};
use pi_share::ShareU32;
pub use pi_share::ShareU64;

const NULL_FULL: u64 = u64::MAX;
const MAX_SLOTS: u32 = u32::MAX - 32;
const MAX_LIVE: u32 = u32::MAX - 1;

// Select from the actual dependency type, including Cargo feature unification.
trait ShareMode {
    type Marker;
}
impl ShareMode for std::sync::atomic::AtomicU32 {
    type Marker = ();
}
impl ShareMode for pi_share::atomic::AtomicCell<u32> {
    type Marker = std::rc::Rc<()>;
}

struct Slot<T> {
    entry: UnsafeCell<MaybeUninit<(T, ShareU64)>>,
    version: ShareU32,
    single_thread: PhantomData<<ShareU32 as ShareMode>::Marker>,
}

// Only the payload field changes under shared access. The link is initialized
// before publication and is never moved/rebuilt while late observers can exist.
// The actual-type marker still prevents Send/Sync when pi_share selects RC.
#[cfg(not(feature = "rc"))]
unsafe impl<T: Send + Sync> Sync for Slot<T> {}

impl<T> Slot<T> {
    fn entry_ptr(&self) -> *mut (T, ShareU64) {
        self.entry.get().cast::<(T, ShareU64)>()
    }

    fn value_ptr(&self) -> *mut T {
        // Raw field projection does not assert initialization of T/the tuple.
        unsafe { ptr::addr_of_mut!((*self.entry_ptr()).0) }
    }

    fn link(&self) -> &ShareU64 {
        // Every allocated slot has an initialized link, even FREE/DEAD slots.
        unsafe { &*ptr::addr_of!((*self.entry_ptr()).1) }
    }
}

impl<T> Default for Slot<T> {
    fn default() -> Self {
        let slot = Self {
            entry: UnsafeCell::new(MaybeUninit::uninit()),
            version: ShareU32::new(1),
            single_thread: PhantomData,
        };
        // Initialize only tuple.1. No T::default and no reference to the tuple.
        // Default may move the empty shell before its containing bucket is published.
        unsafe {
            ptr::write(
                ptr::addr_of_mut!((*slot.entry_ptr()).1),
                ShareU64::new(NULL_FULL),
            )
        };
        slot
    }
}

impl<T> Drop for Slot<T> {
    fn drop(&mut self) {
        let version = self.version.load(Ordering::Relaxed);
        let panic = if live(version) {
            self.version.store(version + 1, Ordering::Relaxed);
            // Slot destruction is exclusive; LIVE is the only ownership marker.
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| unsafe {
                ptr::drop_in_place(self.value_ptr());
            }))
            .err()
        } else {
            None
        };
        // MaybeUninit does not drop its fields. Also drop RC's atomic object,
        // independently of T initialization and even if T's destructor panics.
        unsafe { ptr::drop_in_place(ptr::addr_of_mut!((*self.entry_ptr()).1)) };
        if let Some(payload) = panic {
            std::panic::resume_unwind(payload);
        }
    }
}

fn live(version: u32) -> bool {
    version >= 2 && version & 1 == 0
}

fn full_id(index: u32, version: u32) -> u64 {
    (u64::from(version) << 32) | u64::from(index)
}

fn checked_key<K: Key>(index: u32, version: u32) -> K {
    let data = KeyData::from_ffi(full_id(index, version));
    assert_eq!(
        (data.index(), data.version()),
        (index, version),
        "KeyData encoding must preserve full generation"
    );
    let key = K::from(data);
    assert_eq!(
        key.data(),
        data,
        "SlotMap Key must preserve both index and version"
    );
    key
}

/// Stable addresses, full index32/version32 keys, no T: Default requirement.
/// Keys belong to their originating map; there is no additional map identity.
/// Default atomics allow shared insertion/reading when K and T support Send/Sync.
/// This is not a strictly lock-free container: bucket allocation can lock.
pub struct SlotMap<K: Key = DefaultKey, T = ()> {
    slots: SegmentedArr<Slot<T>>,
    head: ShareU64,
    nextindex: ShareU32,
    // LIVE plus short pre-publication reservations; never cumulative.
    count: ShareU64,
    key: PhantomData<K>,
    single_thread: PhantomData<<ShareU32 as ShareMode>::Marker>,
}

// An empty, detached candidate owns no T. User key callbacks may unwind or
// reenter the map: rollback consumes a generation, never republishes its old id.
struct Candidate<'a, K: Key, T> {
    map: &'a SlotMap<K, T>,
    slot: &'a Slot<T>,
    index: u32,
    version: u32,
    armed: bool,
}
impl<K: Key, T> Drop for Candidate<'_, K, T> {
    fn drop(&mut self) {
        if self.armed {
            self.map.recycle(self.slot, self.index, self.version);
        }
    }
}

impl<K: Key, T> Default for SlotMap<K, T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K: Key, T> Drop for SlotMap<K, T> {
    fn drop(&mut self) {
        let mut first_panic = None;
        let end = self
            .slots
            .contiguous_len()
            .saturating_add(MAX_SLOTS as usize + 1);
        // Remove all payload ownership before the segmented storage destroys
        // its buckets. One user's panic must not skip later buckets/links.
        for segment in self.slots.segments(0..end) {
            for slot in segment {
                let version = slot.version.load(Ordering::Relaxed);
                if !live(version) {
                    continue;
                }
                slot.version.store(version + 1, Ordering::Relaxed);
                // Exclusive destruction and LIVE prove T initialization.
                let value = unsafe { ptr::read(slot.value_ptr()) };
                if let Err(payload) =
                    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| drop(value)))
                {
                    if first_panic.is_none() {
                        first_panic = Some(payload);
                    } else {
                        std::mem::forget(payload);
                    }
                }
            }
        }
        if let Some(payload) = first_panic {
            std::panic::resume_unwind(payload);
        }
    }
}

impl<K: Key, T> SlotMap<K, T> {
    /// Empty map, without constructing T.
    pub fn new() -> Self {
        Self::with_capacity(0)
    }

    /// Preallocate initialized empty shells. Panics above the index limit.
    pub fn with_capacity(capacity: usize) -> Self {
        assert!(
            capacity <= MAX_SLOTS as usize,
            "SlotMap capacity exceeds index limit"
        );
        Self {
            slots: SegmentedArr::with_capacity(capacity),
            head: ShareU64::new(NULL_FULL),
            nextindex: ShareU32::new(0),
            count: ShareU64::new(0),
            key: PhantomData,
            single_thread: PhantomData,
        }
    }

    fn claim(&self) -> Candidate<'_, K, T> {
        loop {
            let head = self.head.load(Ordering::Acquire);
            if head != NULL_FULL {
                // Only head is dereferenced, never the edge before a successful
                // CAS. A late observer may read arbitrary LIVE user link bits.
                // The allocation outlives every observer; its atomic is permanent.
                let index = head as u32;
                let slot = self.slots.get(index as usize).expect("FREE slot allocated");
                let next = slot.link().load(Ordering::Relaxed);
                if self
                    .head
                    .compare_exchange(head, next, Ordering::AcqRel, Ordering::Acquire)
                    .is_err()
                {
                    continue;
                }
                // Successful CAS proves this FREE incarnation never detached
                // between head/edge reads. No one else can change its version.
                let version = (head >> 32) as u32;
                let candidate = Candidate {
                    map: self,
                    slot,
                    index,
                    version: version + 1,
                    armed: true,
                };
                assert_eq!(
                    slot.version.load(Ordering::Acquire),
                    version,
                    "FREE generation mismatch"
                );
                return candidate;
            }
            let index = self.nextindex.load(Ordering::Acquire);
            assert!(index < MAX_SLOTS, "SlotMap index limit exhausted");
            // Allocate BEFORE claiming the index, so allocation unwind cannot
            // strand an unallocated candidate. Competing allocators share a bucket.
            let pointer = self.slots.load_alloc_ptr(index as usize);
            if self
                .nextindex
                .compare_exchange(index, index + 1, Ordering::AcqRel, Ordering::Acquire)
                .is_ok()
            {
                // Initialized stable shell, no mutable reference to Slot.
                let slot = unsafe { &*pointer };
                return Candidate {
                    map: self,
                    slot,
                    index,
                    version: 2,
                    armed: true,
                };
            }
        }
    }

    fn recycle(&self, slot: &Slot<T>, index: u32, live_version: u32) {
        let version = live_version + 1;
        // Empty T, permanent atomic remains initialized. Last generation is DEAD.
        slot.version.store(version, Ordering::Release);
        if live_version == MAX_LIVE {
            return;
        }
        let id = full_id(index, version);
        let mut head = self.head.load(Ordering::Acquire);
        loop {
            slot.link().store(head, Ordering::Relaxed);
            match self
                .head
                .compare_exchange_weak(head, id, Ordering::AcqRel, Ordering::Acquire)
            {
                Ok(_) => break,
                Err(current) => head = current,
            }
        }
    }

    /// Shared insertion with link=0. May run alongside safe reads/iteration.
    pub fn insert(&self, value: T) -> K {
        self.insert_with_link(value, 0)
    }

    /// Shared insertion. Index exhaustion or unrepresentable/panicking keys
    /// panic before T initialization; rollback consumes a generation.
    pub fn insert_with_link(&self, value: T, link: u64) -> K {
        let mut candidate = self.claim();
        let key = checked_key::<K>(candidate.index, candidate.version);
        // Reserve only after all user callbacks succeeded. This counter is
        // bounded by the finite slot population, not lifetime insertions.
        // Failure unwinds the empty candidate before T initialization.
        let mut count = self.count.load(Ordering::Relaxed);
        loop {
            assert!(
                count < u64::from(MAX_SLOTS),
                "SlotMap live counter exhausted"
            );
            match self.count.compare_exchange_weak(
                count,
                count + 1,
                // Publish prior index claims to len() before it observes count.
                Ordering::Release,
                Ordering::Relaxed,
            ) {
                Ok(_) => break,
                Err(current) => count = current,
            }
        }
        // No fallible/user operations between reservation and LIVE publication.
        unsafe { ptr::write(candidate.slot.value_ptr(), value) };
        candidate.slot.link().store(link, Ordering::Relaxed);
        candidate
            .slot
            .version
            .store(candidate.version, Ordering::Release);
        candidate.armed = false;
        key
    }

    /// Exclusive insertion alias with link=0.
    pub fn set(&mut self, value: T) -> K {
        self.insert(value)
    }
    /// Exclusive insertion alias with the specified link.
    pub fn set_with_link(&mut self, value: T, link: u64) -> K {
        self.insert_with_link(value, link)
    }

    /// Quiescent exact LIVE count; concurrent calls may include a brief insertion
    /// reservation or a value whose removal is not yet accounted for. No underflow.
    pub fn len(&self) -> usize {
        self.count.load(Ordering::Acquire) as usize
    }
    /// Index high-water mark, including failed candidates and retired slots.
    pub fn max(&self) -> u32 {
        self.nextindex.load(Ordering::Acquire)
    }
    /// Approximate concurrently, exact when quiescent.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Allocated slot storage plus Self, excluding indirect T allocations and
    /// allocator metadata. Scans segments; approximate during concurrent growth.
    pub fn mem_size(&self) -> usize {
        let end = self.slots.capacity_for_len(self.max() as usize);
        let count: usize = self.slots.segments(0..end).map(|slice| slice.len()).sum();
        count
            .saturating_mul(size_of::<Slot<T>>())
            .saturating_add(size_of::<Self>())
    }

    fn find(&self, data: KeyData) -> Option<&Slot<T>> {
        if !live(data.version()) || data.index() >= self.max() {
            return None;
        }
        let slot = self.slots.get(data.index() as usize)?;
        (slot.version.load(Ordering::Acquire) == data.version()).then_some(slot)
    }

    /// Read a matching LIVE tuple. The shared link supports atomic operations.
    pub fn get(&self, key: K) -> Option<&(T, ShareU64)> {
        let slot = self.find(key.data())?;
        // Acquire observed both initialized fields; safe removal requires &mut self.
        Some(unsafe { &*slot.entry_ptr() })
    }

    /// Exclusive tuple access, including replacement of the atomic object.
    pub fn get_mut(&mut self, key: K) -> Option<&mut (T, ShareU64)> {
        let slot = self.find(key.data())?;
        // Exclusive table access excludes late pop observers and all other borrows.
        Some(unsafe { &mut *slot.entry_ptr() })
    }

    /// Shared-table access to exclusive T and shared permanent link.
    /// # Safety
    /// T must be exclusively borrowed for the entire returned lifetime, without
    /// conflicting get/iter/replace/remove. Synchronize across threads. All returned
    /// references (including link) must end before removal or table destruction.
    /// Atomic-only link access may coexist; RC permits single-thread access only.
    #[allow(clippy::mut_from_ref)]
    pub unsafe fn get_shared(&self, key: K) -> Option<(&mut T, &ShareU64)> {
        let slot = self.find(key.data())?;
        // Only T is mutably borrowed, never the whole tuple or Slot.
        Some((unsafe { &mut *slot.value_ptr() }, slot.link()))
    }

    /// Unchecked shared read.
    /// # Safety
    /// Key must denote an initialized LIVE slot in this map. No conflicting
    /// payload modification/removal during the returned lifetime.
    pub unsafe fn get_unchecked(&self, key: K) -> &(T, ShareU64) {
        let slot = unsafe { self.slots.get_unchecked(key.data().index() as usize) };
        slot.version.load(Ordering::Acquire);
        unsafe { &*slot.entry_ptr() }
    }

    /// Unchecked exclusive tuple access.
    /// # Safety
    /// Key must denote an initialized LIVE slot in this map.
    pub unsafe fn get_unchecked_mut(&mut self, key: K) -> &mut (T, ShareU64) {
        let slot = unsafe { self.slots.get_unchecked(key.data().index() as usize) };
        slot.version.load(Ordering::Acquire);
        unsafe { &mut *slot.entry_ptr() }
    }

    /// Unchecked shared-table exclusive T access.
    /// # Safety
    /// Valid LIVE key and the full get_shared lifetime/synchronization contract.
    #[allow(clippy::mut_from_ref)]
    pub unsafe fn get_shared_unchecked(&self, key: K) -> (&mut T, &ShareU64) {
        let slot = unsafe { self.slots.get_unchecked(key.data().index() as usize) };
        slot.version.load(Ordering::Acquire);
        (unsafe { &mut *slot.value_ptr() }, slot.link())
    }

    /// Remove and return T, invalidating the key.
    pub fn remove(&mut self, key: K) -> Option<T> {
        unsafe { self.remove_shared(key) }
    }
    /// Remove and return T and a snapshot of the user link.
    pub fn remove_with_link(&mut self, key: K) -> Option<(T, u64)> {
        unsafe { self.remove_shared_with_link(key) }
    }

    /// Shared removal without destroying the permanent atomic object.
    /// # Safety
    /// The target slot has no outstanding references (including link), conflicting
    /// readers/writers or iterators scanning it. External synchronization is required
    /// across threads. Internal late FREE observers are permitted by the protocol.
    pub unsafe fn remove_shared(&self, key: K) -> Option<T> {
        unsafe { self.remove_shared_with_link(key) }.map(|(value, _)| value)
    }

    /// Shared removal with link snapshot.
    /// # Safety
    /// Same complete exclusion/lifetime contract as remove_shared.
    pub unsafe fn remove_shared_with_link(&self, key: K) -> Option<(T, u64)> {
        let data = key.data();
        let slot = self.find(data)?;
        let link = slot.link().load(Ordering::Relaxed);
        slot.version.store(data.version() + 1, Ordering::Release);
        // Exclusive payload contract and LIVE prove initialized T. Only T moves.
        let value = unsafe { ptr::read(slot.value_ptr()) };
        // Each LIVE publication reserved one count. Decrement before publishing
        // FREE, so reuse cannot accumulate reservations beyond the slot population.
        self.count.fetch_sub(1, Ordering::Relaxed);
        self.recycle(slot, data.index(), data.version());
        Some((value, link))
    }

    /// Replace T only, preserving version and link. Old T on success, new T on error.
    pub fn replace(&mut self, key: K, value: T) -> Result<T, T> {
        unsafe { self.replace_shared(key, value) }
    }
    /// Replace T and link bits, returning the old/new pair on success/error.
    pub fn replace_with_link(&mut self, key: K, value: T, link: u64) -> Result<(T, u64), (T, u64)> {
        unsafe { self.replace_shared_with_link(key, value, link) }
    }

    /// Shared replacement of T only; permanent link and generation are unchanged.
    /// # Safety
    /// No conflicting payload references, modification, removal or scanning.
    /// Cross-thread access requires synchronization. Atomic link operations may coexist.
    pub unsafe fn replace_shared(&self, key: K, value: T) -> Result<T, T> {
        let Some(slot) = self.find(key.data()) else {
            return Err(value);
        };
        // Only T moves, under the caller's payload exclusion guarantee.
        Ok(unsafe { ptr::replace(slot.value_ptr(), value) })
    }

    /// Shared replacement with an old link snapshot; never replaces the atomic object.
    /// # Safety
    /// replace_shared's payload contract, plus no concurrent user link operations
    /// during this operation. Internal late FREE observers remain permitted.
    pub unsafe fn replace_shared_with_link(
        &self,
        key: K,
        value: T,
        link: u64,
    ) -> Result<(T, u64), (T, u64)> {
        let Some(slot) = self.find(key.data()) else {
            return Err((value, link));
        };
        let old_link = slot.link().load(Ordering::Relaxed);
        let old = unsafe { ptr::replace(slot.value_ptr(), value) };
        slot.link().store(link, Ordering::Relaxed);
        Ok((old, old_link))
    }

    /// Weakly consistent Acquire scan with frozen max upper bound, not a snapshot.
    pub fn iter(&self) -> Iter<'_, K, T> {
        Iter {
            map: self,
            next: 0,
            end: self.max(),
        }
    }
    /// Exclusive tuple iteration; each index appears once and references may coexist.
    pub fn iter_mut(&mut self) -> IterMut<'_, K, T> {
        IterMut {
            end: self.max(),
            slots: &mut self.slots,
            next: 0,
            borrow: PhantomData,
        }
    }
}

impl<K: Key, T> Index<K> for SlotMap<K, T> {
    type Output = (T, ShareU64);
    fn index(&self, key: K) -> &Self::Output {
        self.get(key).expect("invalid SlotMap key")
    }
}
impl<K: Key, T> IndexMut<K> for SlotMap<K, T> {
    fn index_mut(&mut self, key: K) -> &mut Self::Output {
        self.get_mut(key).expect("invalid SlotMap key")
    }
}
impl<K: Key, T: Debug> Debug for SlotMap<K, T> {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        formatter.debug_map().entries(self.iter()).finish()
    }
}

/// Read-only weak scan, with frozen index upper bound.
pub struct Iter<'a, K: Key, T> {
    map: &'a SlotMap<K, T>,
    next: u32,
    end: u32,
}
impl<'a, K: Key, T> Iterator for Iter<'a, K, T> {
    type Item = (K, &'a (T, ShareU64));
    fn next(&mut self) -> Option<Self::Item> {
        while self.next < self.end {
            let index = self.next;
            self.next += 1;
            let slot = self.map.slots.get(index as usize)?;
            let version = slot.version.load(Ordering::Acquire);
            if live(version) {
                let key = checked_key(index, version);
                // Acquire proves both tuple fields initialized; unsafe callers
                // must exclude conflicting payload changes/removal while scanning.
                return Some((key, unsafe { &*slot.entry_ptr() }));
            }
        }
        None
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some((self.end - self.next) as usize))
    }
}

/// Exclusive unique-index scan, without mutable references to LIVE slots.
pub struct IterMut<'a, K: Key, T> {
    slots: *mut SegmentedArr<Slot<T>>,
    next: u32,
    end: u32,
    borrow: PhantomData<&'a mut SlotMap<K, T>>,
}
impl<'a, K: Key, T> Iterator for IterMut<'a, K, T> {
    type Item = (K, &'a mut (T, ShareU64));
    fn next(&mut self) -> Option<Self::Item> {
        while self.next < self.end {
            let index = self.next;
            self.next += 1;
            // Exclusive table borrow stays alive; shared Slot accesses touch
            // metadata outside UnsafeCell, not any previously returned tuple.
            let slot = unsafe { (&*self.slots).get(index as usize)? };
            let version = slot.version.load(Ordering::Acquire);
            if live(version) {
                let key = checked_key(index, version);
                return Some((key, unsafe { &mut *slot.entry_ptr() }));
            }
        }
        None
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some((self.end - self.next) as usize))
    }
}
