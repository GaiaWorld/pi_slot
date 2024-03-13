use core::fmt::*;
use core::marker::PhantomData;
use core::mem::ManuallyDrop;
use std::mem::replace;
use std::ops::{DerefMut, Index, IndexMut, Range};
use std::sync::atomic::Ordering;

use pi_append_vec::AppendVec;
use pi_key_alloter::*;
use pi_null::Null;
use pi_share::ShareU32;

/// Thread-safe slotmap
#[derive(Default)]
pub struct SlotMap<K: Key, V> {
    alloter: KeyAlloter,
    map: KeyMap<K, V>,
}

impl<K: Key, V> SlotMap<K, V> {
    /// Creates an empty [`SlotMap`] with the given capacity and a custom key
    /// type.
    ///
    /// The slot map will not reallocate until it holds at least `capacity`
    /// elements.
    ///
    /// # Examples
    ///
    /// ```
    /// # use pi_slot::*;
    /// use pi_key_alloter::*;
    /// new_key_type! {
    ///     struct MessageKey;
    /// }
    /// let messages = SlotMap::with_capacity(3);
    /// let welcome: MessageKey = messages.insert("Welcome");
    /// let good_day = messages.insert("Good day");
    /// let hello = messages.insert("Hello");
    /// ```
    #[inline(always)]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            alloter: KeyAlloter::new(0),
            map: KeyMap::with_capacity(capacity),
        }
    }
    #[inline(always)]
    pub fn new() -> Self {
        Self::with_capacity(0)
    }

    /// Returns the number of elements in the slot map.
    ///
    /// # Examples
    ///
    /// ```
    /// # use pi_slot::*;
    /// use pi_key_alloter::*;
    /// let sm = SlotMap::with_capacity(10);
    /// sm.insert("len() counts actual elements, not capacity");
    /// let key: DefaultKey = sm.insert("removed elements don't count either");
    /// sm.remove(key);
    /// assert_eq!(sm.len(), 1);
    /// ```
    #[inline(always)]
    pub fn len(&self) -> usize {
        self.alloter.len()
    }
    /// Returns the number of elements in the slot map.
    ///
    /// # Examples
    ///
    /// ```
    /// # use pi_slot::*;
    /// use pi_key_alloter::*;
    /// let sm = SlotMap::with_capacity(10);
    /// sm.insert("len() counts actual elements, not capacity");
    /// let key: DefaultKey = sm.insert("removed elements don't count either");
    /// sm.remove(key);
    /// assert_eq!(sm.max(), 2);
    /// ```
    #[inline(always)]
    pub fn max(&self) -> u32 {
        self.alloter.max()
    }
    /// Returns if the slot map is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// # use pi_slot::*;
    /// use pi_key_alloter::*;
    /// let sm = SlotMap::new();
    /// let key: DefaultKey = sm.insert("dummy");
    /// assert_eq!(sm.is_empty(), false);
    /// sm.remove(key);
    /// assert_eq!(sm.is_empty(), true);
    /// ```
    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
    /// 分配一个Key, 后面要求一定要用set_value设置Value，否则remove时回收Key会失败，另外，再没有插入数据期间，如果进行迭代，也是没有该key的
    #[inline(always)]
    pub unsafe fn alloc_key(&self) -> K {
        self.alloter.alloc(2, 2).into()
    }
    #[inline(always)]
    pub unsafe fn set_value(&self, k: K, v: V) -> std::result::Result<Option<V>, V> {
        self.map.insert(k, v)
    }
    /// Returns [`true`] if the slot map contains `key`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use pi_slot::*;
    /// use pi_key_alloter::*;
    /// let sm = SlotMap::new();
    /// let key: DefaultKey = sm.insert(42);
    /// assert_eq!(sm.contains_key(key), true);
    /// sm.remove(key);
    /// assert_eq!(sm.contains_key(key), false);
    /// ```
    #[inline(always)]
    pub fn contains_key(&self, k: K) -> bool {
        self.map.contains_key(k)
    }
    /// Inserts a value into the slot map. Returns a unique key that can be used
    /// to access this value.
    ///
    /// # Panics
    ///
    /// Panics if the number of elements in the slot map equals
    /// 2<sup>32</sup> - 2.
    ///
    /// # Examples
    ///
    /// ```
    /// # use pi_slot::*;
    /// use pi_key_alloter::*;
    /// let sm = SlotMap::new();
    /// let key: DefaultKey = sm.insert(42);
    /// assert_eq!(sm[key], 42);
    /// ```
    #[inline(always)]
    pub fn insert(&self, v: V) -> K {
        let k = unsafe { self.alloc_key() };
        assert!(self.map.insert(k, v).is_ok());
        k
    }
    /// Removes a key from the slot map, returning the value at the key if the
    /// key was not previously removed.
    ///
    /// # Examples
    ///
    /// ```
    /// # use pi_slot::*;
    /// use pi_key_alloter::*;
    /// let sm = SlotMap::new();
    /// let key: DefaultKey = sm.insert(42);
    /// assert_eq!(sm.remove(key), Some(42));
    /// assert_eq!(sm.remove(key), None);
    /// ```
    #[inline(always)]
    pub fn remove(&self, k: K) -> Option<V> {
        let r = self.map.remove(k);
        if r.is_some() {
            self.alloter.recycle(k.data());
        }
        r
    }
    /// Returns a reference to the value corresponding to the key.
    ///
    /// # Examples
    ///
    /// ```
    /// # use pi_slot::*;
    /// use pi_key_alloter::*;
    /// let sm = SlotMap::new();
    /// let key: DefaultKey = sm.insert("bar");
    /// assert_eq!(sm.get(key), Some(&"bar"));
    /// sm.remove(key);
    /// assert_eq!(sm.get(key), None);
    /// ```
    #[inline(always)]
    pub fn get(&self, k: K) -> Option<&V> {
        self.map.get(k)
    }

    /// Returns a reference to the value corresponding to the key without
    /// version or bounds checking.
    ///
    /// # Safety
    ///
    /// This should only be used if `contains_key(key)` is true. Otherwise it is
    /// potentially unsafe.
    ///
    /// # Examples
    ///
    /// ```
    /// # use pi_slot::*;
    /// use pi_key_alloter::*;
    /// let mut sm = SlotMap::new();
    /// let key: DefaultKey = sm.insert("bar");
    /// assert_eq!(unsafe { sm.get_unchecked(key) }, &"bar");
    /// sm.remove(key);
    /// // sm.get_unchecked(key) is now dangerous!
    /// ```
    #[inline(always)]
    pub unsafe fn get_unchecked(&self, k: K) -> &V {
        self.map.get_unchecked(k)
    }

    /// Returns a mutable reference to the value corresponding to the key.
    ///
    /// # Examples
    ///
    /// ```
    /// # use pi_slot::*;
    /// use pi_key_alloter::*;
    /// let mut sm = SlotMap::new();
    /// let key: DefaultKey = sm.insert(3.5);
    /// if let Some(x) = sm.get_mut(key) {
    ///     *x += 3.0;
    /// }
    /// assert_eq!(sm[key], 6.5);
    /// ```
    #[inline(always)]
    pub fn get_mut(&mut self, k: K) -> Option<&mut V> {
        self.map.get_mut(k)
    }

    /// Returns a mutable reference to the value corresponding to the key
    /// without version or bounds checking.
    ///
    /// # Safety
    ///
    /// This should only be used if `contains_key(key)` is true. Otherwise it is
    /// potentially unsafe.
    ///
    /// # Examples
    ///
    /// ```
    /// # use pi_slot::*;
    /// use pi_key_alloter::*;
    /// let mut sm = SlotMap::new();
    /// let key: DefaultKey = sm.insert("foo");
    /// unsafe { *sm.get_unchecked_mut(key) = "bar" };
    /// assert_eq!(sm[key], "bar");
    /// sm.remove(key);
    /// // sm.get_unchecked_mut(key) is now dangerous!
    /// ```
    #[inline(always)]
    pub unsafe fn get_unchecked_mut(&mut self, k: K) -> &mut V {
        self.map.get_unchecked_mut(k)
    }
    /// Inserts a value into the slot map. Returns a unique key that can be used
    /// to access this value.
    ///
    /// # Panics
    ///
    /// Panics if the number of elements in the slot map equals
    /// 2<sup>32</sup> - 2.
    ///
    /// # Examples
    ///
    /// ```
    /// # use pi_slot::*;
    /// use pi_key_alloter::*;
    /// let mut sm = SlotMap::new();
    /// let key: DefaultKey = sm.set(42);
    /// assert_eq!(sm[key], 42);
    /// ```
    #[inline(always)]
    pub fn set(&mut self, v: V) -> K {
        let k = unsafe { self.alloc_key() };
        assert!(self.map.set(k, v).is_ok());
        k
    }
    /// Returns a mutable reference to the value corresponding to the key.
    ///
    /// # Examples
    ///
    /// ```
    /// # use pi_slot::*;
    /// use pi_key_alloter::*;
    /// let sm = SlotMap::new();
    /// let key: DefaultKey = sm.insert(3.5);
    /// if let Some(x) = sm.load(key) {
    ///     *x += 3.0;
    /// }
    /// assert_eq!(sm[key], 6.5);
    /// ```
    #[inline(always)]
    pub fn load(&self, k: K) -> Option<&mut V> {
        self.map.load(k)
    }

    /// Returns a mutable reference to the value corresponding to the key
    /// without version or bounds checking.
    ///
    /// # Safety
    ///
    /// This should only be used if `contains_key(key)` is true. Otherwise it is
    /// potentially unsafe.
    ///
    /// # Examples
    ///
    /// ```
    /// # use pi_slot::*;
    /// use pi_key_alloter::*;
    /// let sm = SlotMap::new();
    /// let key: DefaultKey = sm.insert("foo");
    /// unsafe { *sm.load_unchecked(key) = "bar" };
    /// assert_eq!(sm[key], "bar");
    /// sm.remove(key);
    /// ```
    #[inline(always)]
    pub unsafe fn load_unchecked(&self, k: K) -> &mut V {
        self.map.load_unchecked(k)
    }
    /// An iterator visiting all key-value pairs in arbitrary order. The
    /// iterator element type is `(K, &'a V)`.
    ///
    /// This function must iterate over all slots, empty or not. In the face of
    /// many deleted elements it can be inefficient.
    ///
    /// # Examples
    ///
    /// ```
    /// # use pi_slot::*;
    /// use pi_key_alloter::*;
    /// let sm = SlotMap::new();
    /// let k0: DefaultKey = sm.insert(0);
    /// let k1: DefaultKey = sm.insert(1);
    /// let k2: DefaultKey = sm.insert(2);
    ///
    /// for (k, v) in sm.iter() {
    ///     println!("key: {:?}, val: {}", k, v);
    /// }
    /// ```
    #[inline(always)]
    pub fn iter(&self) -> Iter<'_, K, V> {
        self.map.iter(0..self.alloter.max() as usize)
    }
    /// Returns an iterator over the array at the given range.
    ///
    /// Values are yielded in the form `(index, Entry)`.
    ///
    /// # Examples
    ///
    /// ```
    /// let arr = pi_arr::arr![1, 2, 4, 6];
    /// let mut iterator = arr.slice(1..3);
    ///
    /// let r = iterator.next().unwrap();
    /// assert_eq!(*r, 2);
    /// let r = iterator.next().unwrap();
    /// assert_eq!(*r, 4);
    /// assert_eq!(iterator.next(), None);
    /// ```
    pub fn slice(&self, mut range: Range<usize>) -> Iter<'_, K, V> {
        let len = self.max() as usize;
        if range.end > len {
            range.end = len;
        }
        self.map.iter(range)
    }
    /// 扩容
    #[inline(always)]
    pub fn reserve(&mut self, additional: usize) {
        self.map.reserve(self.len() + additional);
    }
    
    /// 整理方法
    pub fn collect_key(&self) -> Drain {
        self.alloter.collect(2)
    }
    /// 整理方法
    pub unsafe fn collect_value(&self, tail: u32, free: KeyData) {
        self.map.collect_value(tail, free)
    }
}
impl<K: Key, V> Index<K> for SlotMap<K, V> {
    type Output = V;

    #[inline(always)]
    fn index(&self, index: K) -> &Self::Output {
        self.map.index(index)
    }
}
impl<K: Key, V> IndexMut<K> for SlotMap<K, V> {
    #[inline(always)]
    fn index_mut(&mut self, index: K) -> &mut Self::Output {
        self.map.index_mut(index)
    }
}
impl<K: Key, V: Debug> Debug for SlotMap<K, V> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        f.debug_struct("SlotMap")
            .field("alloter", &self.alloter)
            .field("map", &KeyMapFormatter::new(&self.map, self.alloter.max() as usize))
            .finish()
    }
}

#[derive(Default)]
pub struct KeyMap<K: Key, V> {
    arr: AppendVec<Slot<V>>,
    _k: PhantomData<K>,
}
impl<K: Key, V> KeyMap<K, V> {
    /// Creates an empty [`KeyMap`] with the given capacity and a custom key
    /// type.
    ///
    /// The slot map will not reallocate until it holds at least `capacity`
    /// elements.
    ///
    /// # Examples
    ///
    /// ```
    /// # use pi_slot::*;
    /// use pi_key_alloter::*;
    /// new_key_type! {
    ///     struct MessageKey;
    /// }
    /// let mut messages = SlotMap::with_capacity(3);
    /// let mut km = KeyMap::with_capacity(3);
    /// let welcome: MessageKey = messages.insert("Welcome");
    /// km.insert(welcome, "Welcome1");
    /// let good_day = messages.insert("Good day");
    /// km.insert(good_day, "Good day1");
    /// let hello = messages.insert("Hello");
    /// km.insert(hello, "Hello1");
    /// ```
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            arr: AppendVec::with_capacity(capacity),
            _k: PhantomData,
        }
    }
    pub fn contains_key(&self, k: K) -> bool {
        let kd = k.data();
        match self.arr.get_i(kd.index() as usize) {
            Some(s) => s.ver(Ordering::Relaxed) == kd.version(),
            None => false,
        }
    }
    /// Inserts a value into the slot map. Returns a unique key that can be used
    /// to access this value.
    ///
    /// # Panics
    ///
    /// Panics if the number of elements in the slot map equals
    /// 2<sup>32</sup> - 2.
    ///
    /// # Examples
    ///
    /// ```
    /// # use pi_slot::*;
    /// let sm = SlotMap::new();
    /// let key = sm.insert(42);
    /// assert_eq!(sm[key], 42);
    /// ```
    #[inline(always)]
    pub fn insert(&self, k: K, v: V) -> std::result::Result<Option<V>, V> {
        let kd = k.data();
        let e = self.arr.load_alloc(kd.index() as usize, 1);
        Self::update(kd, v, e)
    }
    /// Removes a key from the slot map, returning the value at the key if the
    /// key was not previously removed.
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// # use pi_slot::*;
    /// let sm = SlotMap::new();
    /// let key = sm.insert(42);
    /// assert_eq!(sm.remove(key), Some(42));
    /// assert_eq!(sm.remove(key), None);
    /// ```
    pub fn remove(&self, k: K) -> Option<V> {
        let kd = k.data();
        match self.arr.load_i(kd.index() as usize) {
            Some(e) => {
                let v = e.ver(Ordering::Relaxed);
                if v == kd.version() {
                    let r = unsafe { Some(e.take()) };
                    e.set_ver(v + 1, Ordering::Relaxed);
                    r
                } else {
                    None
                }
            }
            _ => None,
        }
    }
    /// Returns a reference to the value corresponding to the key.
    ///
    /// # Examples
    ///
    /// ```
    /// # use pi_slot::*;
    /// let sm = SlotMap::new();
    /// let key = sm.insert("bar");
    /// assert_eq!(sm.get(key), Some(&"bar"));
    /// sm.remove(key);
    /// assert_eq!(sm.get(key), None);
    /// ```
    #[inline(always)]
    pub fn get(&self, k: K) -> Option<&V> {
        let kd = k.data();
        match self.arr.get_i(kd.index() as usize) {
            Some(s) if s.ver(Ordering::Acquire) == kd.version() => Some(unsafe { s.get_unchecked() }),
            _ => None,
        }
    }

    /// Returns a reference to the value corresponding to the key without
    /// version or bounds checking.
    ///
    /// # Safety
    ///
    /// This should only be used if `contains_key(key)` is true. Otherwise it is
    /// potentially unsafe.
    ///
    /// # Examples
    ///
    /// ```
    /// # use pi_slot::*;
    /// let sm = SlotMap::new();
    /// let key = sm.insert("bar");
    /// assert_eq!(unsafe { sm.get_unchecked(key) }, &"bar");
    /// sm.remove(key);
    /// // sm.get_unchecked(key) is now dangerous!
    /// ```
    #[inline(always)]
    pub unsafe fn get_unchecked(&self, k: K) -> &V {
        self.arr
            .get_unchecked(k.data().index() as usize)
            .get_unchecked()
    }

    /// Returns a mutable reference to the value corresponding to the key.
    ///
    /// # Examples
    ///
    /// ```
    /// # use pi_slot::*;
    /// let mut sm = SlotMap::new();
    /// let key = sm.insert(3.5);
    /// if let Some(x) = sm.get_mut(key) {
    ///     *x += 3.0;
    /// }
    /// assert_eq!(sm[key], 6.5);
    /// ```
    #[inline(always)]
    pub fn get_mut(&mut self, k: K) -> Option<&mut V> {
        let kd = k.data();
        match self.arr.get_mut_i(kd.index() as usize) {
            Some(s) if s.ver(Ordering::Relaxed) == kd.version() => Some(unsafe { s.get_unchecked_mut() }),
            _ => None,
        }
    }

    /// Returns a mutable reference to the value corresponding to the key
    /// without version or bounds checking.
    ///
    /// # Safety
    ///
    /// This should only be used if `contains_key(key)` is true. Otherwise it is
    /// potentially unsafe.
    ///
    /// # Examples
    ///
    /// ```
    /// # use pi_slot::*;
    /// let mut sm = SlotMap::new();
    /// let key = sm.insert("foo");
    /// unsafe { *sm.get_unchecked_mut(key) = "bar" };
    /// assert_eq!(sm[key], "bar");
    /// sm.remove(key);
    /// // sm.get_unchecked_mut(key) is now dangerous!
    /// ```
    #[inline(always)]
    pub unsafe fn get_unchecked_mut(&mut self, k: K) -> &mut V {
        self.arr
            .get_unchecked_mut(k.data().index() as usize)
            .get_unchecked_mut()
    }
    /// Inserts a value into the slot map. Returns a unique key that can be used
    /// to access this value.
    ///
    /// # Panics
    ///
    /// Panics if the number of elements in the slot map equals
    /// 2<sup>32</sup> - 2.
    ///
    /// # Examples
    ///
    /// ```
    /// # use pi_slot::*;
    /// let mut sm = SlotMap::new();
    /// let key = sm.set(42);
    /// assert_eq!(sm[key], 42);
    /// ```
    #[inline(always)]
    pub fn set(&mut self, k: K, v: V) -> std::result::Result<Option<V>, V> {
        let kd = k.data();
        let e = self.arr.load_alloc(kd.index() as usize, 1);
        Self::update(kd, v, e)
    }
    fn update(kd: KeyData, v: V, s: &mut Slot<V>) -> std::result::Result<Option<V>, V> {
        let ver = s.ver(Ordering::Relaxed);
        if is_older_version(kd.version(), ver) {
            return Err(v);
        }
        if check_null(ver) {
            s.value.value = ManuallyDrop::new(v);
            s.set_ver(kd.version(), Ordering::Release);
            Ok(None)
        } else {
            let dest = unsafe { DerefMut::deref_mut(&mut s.value.value) };
            let r = Ok(Some(replace(dest, v)));
            s.set_ver(kd.version(), Ordering::Release);
            r
        }
    }
    /// Returns a mutable reference to the value corresponding to the key.
    /// todo 应该加个Entry，drop时，set_ver(Ordering::Release)
    /// # Examples
    ///
    /// ```
    /// # use pi_slot::*;
    /// let sm = SlotMap::new();
    /// let key = sm.insert(3.5);
    /// if let Some(x) = sm.load(key) {
    ///     *x += 3.0;
    /// }
    /// assert_eq!(sm[key], 6.5);
    /// ```
    #[inline(always)]
    pub fn load(&self, k: K) -> Option<&mut V> {
        let kd = k.data();
        match self.arr.load_i(kd.index() as usize) {
            Some(s) if s.ver(Ordering::Acquire) == kd.version() => Some(unsafe { s.get_unchecked_mut() }),
            _ => None,
        }
    }

    /// Returns a mutable reference to the value corresponding to the key
    /// without version or bounds checking.
    ///
    /// # Safety
    ///
    /// This should only be used if `contains_key(key)` is true. Otherwise it is
    /// potentially unsafe.
    ///
    /// # Examples
    ///
    /// ```
    /// # use pi_slot::*;
    /// let sm = SlotMap::new();
    /// let key = sm.insert("foo");
    /// unsafe { *sm.index_unchecked_mut(key) = "bar" };
    /// assert_eq!(sm[key], "bar");
    /// sm.remove(key);
    /// // sm.index_unchecked_mut(key) is now dangerous!
    /// ```
    #[inline(always)]
    pub unsafe fn load_unchecked(&self, k: K) -> &mut V {
        self.arr
            .load_unchecked(k.data().index() as usize)
            .get_unchecked_mut()
    }
    /// An iterator visiting all key-value pairs in arbitrary order. The
    /// iterator element type is `(K, &'a V)`.
    ///
    /// This function must iterate over all slots, empty or not. In the face of
    /// many deleted elements it can be inefficient.
    ///
    /// # Examples
    ///
    /// ```
    /// # use pi_slot::*;
    /// let sm = SlotMap::new();
    /// let k0 = sm.insert(0);
    /// let k1 = sm.insert(1);
    /// let k2 = sm.insert(2);
    ///
    /// for (k, v) in sm.iter() {
    ///     println!("key: {:?}, val: {}", k, v);
    /// }
    /// ```
    #[inline(always)]
    pub fn iter(&self, range: Range<usize>) -> Iter<'_, K, V> {
        Iter {
            iter: self.arr.slice_raw(range),
            vec_capacity: self.arr.vec_capacity(),
            _k: PhantomData,
        }
    }
    /// 扩容到指定容量
    pub fn reserve(&mut self, capacity: usize) {
        let additional = if capacity <= self.arr.vec_capacity() {
            return
        }else{
            capacity - self.arr.vec_capacity()
        };
        self.arr.collect_raw(self.arr.vec_capacity(), additional, 1);
    }
    /// 整理方法
    pub unsafe fn collect_value(&self, tail: u32, free: KeyData) {
        let e = self.arr.load_alloc(tail as usize, 1);
        e.set_ver(1, Ordering::Relaxed);
        let value = e.take();
        let hole = self.arr.load_alloc(free.index() as usize, 1);
        hole.set_ver(free.version(), Ordering::Relaxed);
        std::ptr::write(&mut hole.value.value, ManuallyDrop::new(value));
    }
}

impl<K: Key, V> Index<K> for KeyMap<K, V> {
    type Output = V;

    #[inline(always)]
    fn index(&self, index: K) -> &Self::Output {
        self.get(index).expect("no element found at index {index}")
    }
}
impl<K: Key, V> IndexMut<K> for KeyMap<K, V> {
    #[inline(always)]
    fn index_mut(&mut self, index: K) -> &mut Self::Output {
        self.get_mut(index)
            .expect("no element found at index_mut {index}")
    }
}


#[inline(always)]
fn check_null(v: u32) -> bool {
    v & 1 == 1
}

union SlotUnion<T> {
    none: (),
    value: ManuallyDrop<T>,
}

struct Slot<T> {
    value: SlotUnion<T>,
    version: ShareU32, // 因为有迭代，所以外部插入时，是先插入再更新版本，保证迭代的安全
}
impl<T> Slot<T> {
    #[inline]
    pub fn get(&self) -> Option<&T> {
        if self.is_null() {
            None
        } else {
            unsafe { Some(&self.value.value) }
        }
    }
    #[inline]
    pub unsafe fn get_unchecked(&self) -> &T {
        &self.value.value
    }
    #[inline]
    pub unsafe fn get_unchecked_mut(&mut self) -> &mut T {
        &mut self.value.value
    }
    #[inline]
    unsafe fn take(&mut self) -> T {
        ManuallyDrop::take(&mut self.value.value)
    }
    fn ver(&self, order: Ordering) -> u32 {
        self.version.load(order)
    }
    fn set_ver(&mut self, v: u32, order: Ordering) {
        self.version.store(v, order)
    }
}

impl<T> Null for Slot<T> {
    #[inline(always)]
    fn null() -> Self {
        Slot {
            value: SlotUnion { none: () },
            version: ShareU32::new(1),
        }
    }
    #[inline(always)]
    fn is_null(&self) -> bool {
        check_null(self.ver(Ordering::Relaxed))
    }
}
impl<T> Default for Slot<T> {
    #[inline]
    fn default() -> Slot<T> {
        Self::null()
    }
}
impl<T> Drop for Slot<T> {
    fn drop(&mut self) {
        if core::mem::needs_drop::<T>() && !self.is_null() {
            // This is safe because we checked that we're not null.
            unsafe {
                ManuallyDrop::drop(&mut self.value.value);
            }
        }
    }
}
impl<T: Debug> Debug for Slot<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        f.debug_tuple("Slot")
            .field(&self.get())
            .field(&self.version)
            .finish()
    }
}

struct KeyMapFormatter<'a, K: Key, V> {
    map: &'a KeyMap<K, V>,
    len: usize,
}
impl<'a, K: Key, V: Debug>  KeyMapFormatter<'a, K, V> {
    fn new(map: &'a KeyMap<K, V>, len: usize) -> Self{
        Self{map, len}
    }
}

impl<'a, K: Key, V: Debug> Debug for KeyMapFormatter<'a, K, V> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        f.debug_list().entries(self.map.iter(0..self.len)).finish()
    }
}
pub struct Iter<'a, K: Key, V> {
    iter: pi_arr::Iter<'a, Slot<V>>,
    vec_capacity: usize,
    _k: PhantomData<fn(K) -> K>,
}
impl<'a, K: Key, V> Iterator for Iter<'a, K, V> {
    type Item = (K, &'a mut V);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(e) = self.iter.next() {
            let ver = e.ver(Ordering::Relaxed);
            if check_null(ver) {
                continue;
            }
            let start = self.iter.start();
            let index = if start.bucket < 0 {
                start.entry - 1
            }else{
                self.vec_capacity + pi_arr::Location::index(start.bucket as u32, start.entry) - 1
            };
            let ffi = (u64::from(ver) << 32) | u64::from(index as u32);
            return Some((KeyData::from_ffi(ffi).into(), unsafe { &mut e.value.value }));
        }
        None
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        let (_min, max) = self.iter.size_hint();
        (0, max)
    }
}

#[cfg(test)]
mod tests {
    use crate::*;

    #[test]
    fn test() {
        new_key_type! {
            struct MessageKey;
        }
        let sm = SlotMap::with_capacity(3);
        let welcome: MessageKey = sm.insert("Welcome");
        let good_day = sm.insert("Good day");
        let hello = sm.insert("Hello");
        sm.remove(welcome);
        assert_eq!(sm.len(), 2);
        assert_eq!(sm.max(), 3);
        assert_eq!(sm.remove(good_day).unwrap(), "Good day");
        assert_eq!(sm.remove(hello).unwrap(), "Hello");
        assert_eq!(sm.contains_key(hello), false);
        assert_eq!(sm.is_empty(), true);
        let hello1 = sm.insert("Hello");
        assert_eq!(sm.contains_key(hello1), true);
        assert_eq!(sm[hello1], "Hello");
        assert_eq!(sm.get(welcome), None);
        assert_eq!(sm.get(hello), None);
        assert_eq!(unsafe { sm.get_unchecked(hello1) }, &"Hello");
        *sm.load(hello1).unwrap() = "Hello1";
        assert_eq!(sm[hello1], "Hello1");
        for (k, v) in sm.iter() {
            println!("key: {:?}, val: {}", k, v);
        }
        assert_eq!(sm.max(), 3);
        for (k, v) in sm.collect_key() {
            unsafe {
                sm.collect_value(k, v);
            }
        }
        assert_eq!(sm[hello1], "Hello1");
        assert_eq!(sm.max(), 1);
    }
}
