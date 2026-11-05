#!/usr/bin/env bash
# Run: bash scripts/test-tsan.sh (actual x86_64 Linux, rustup, cc required).
# Only user-level Rust installation; no system configuration changes.
set -euo pipefail
readonly toolchain=nightly-2026-08-17
readonly target=x86_64-unknown-linux-gnu
readonly suite_timeout=900s
root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd -- "$root"
mkdir -p target/tsan
run_dir=$(mktemp -d "$root/target/tsan/run-XXXXXXXX")

# Every pipeline is synchronous. Never print PASS inside a logging pipeline:
# the outer tee may still fail after the producer has finished successfully.
run() {
    local rc
    printf '\nCOMMAND:'
    printf ' %q' "$@"
    printf '\n'
    if "$@"; then rc=0; else rc=$?; fi
    printf 'COMMAND_EXIT=%s\n' "$rc"
    if (( rc == 124 || rc == 137 )); then
        printf 'TIMEOUT_OR_KILL: command exceeded timeout or was killed (exit=%s).\n' "$rc"
    fi
    return "$rc"
}
logged() {
    local path=$1
    shift
    local -a codes
    # Disable errexit only around this pipeline to capture BOTH statuses.
    # run handles command failure explicitly, including when called in an if.
    if run "$@" 2>&1 | tee "$path"; then
        codes=("${PIPESTATUS[@]}")
    else
        codes=("${PIPESTATUS[@]}")
    fi
    printf 'CAPTURE command_exit=%s tee_exit=%s log=%s\n' "${codes[0]}" "${codes[1]}" "$path"
    if (( codes[1] != 0 )); then
        printf 'LOG_WRITE_FAILED=%s\n' "$path" >&2
        return 74
    fi
    return "${codes[0]}"
}

# Parse the harness summary, require every listed test to have an actual ok line,
# and reject zero tests, ignored/filtered tests, duplicates, and missing results.
verify_execution() {
    local listing=$1 output=$2
    awk '
        FNR == NR {
            if ($0 ~ /: test$/) {
                name = substr($0, 1, length($0) - 6)
                if (name in listed) bad = 1
                listed[name] = 1
                expected++
            }
            next
        }
        /^test .* \.\.\. ok$/ {
            name = substr($0, 6, length($0) - 12)
            if (!(name in listed) || ++seen[name] != 1) bad = 1
            passed++
        }
        /^test result:/ {
            summaries++
            if ($0 !~ /^test result: ok\. [0-9]+ passed; 0 failed; 0 ignored; 0 measured; 0 filtered out;/ || $4 != expected) bad = 1
        }
        END {
            for (name in listed) if (seen[name] != 1) bad = 1
            if (expected < 1 || passed != expected || summaries != 1 || bad) {
                print "HARNESS_VERIFICATION_FAILED: expected=" expected ", ok_lines=" passed ", summaries=" summaries
                exit 1
            }
            print "HARNESS_VERIFIED: " passed " actually executed; zero ignored/filtered/failed"
        }
    ' "$listing" "$output"
}

main() {
    printf 'UTC=%s\nTARGET=%s\nTOOLCHAIN=%s\nSUITE_TIMEOUT=%s (kill-after=10s)\n' "$(date -u +%FT%TZ)" "$target" "$toolchain" "$suite_timeout"
    run uname -a
    if [[ $(uname -s) != Linux || $(uname -m) != x86_64 ]]; then
        printf 'BLOCKED: requires actual x86_64 Linux; no tests ran.\n'
        return 2
    fi
    for command in rustup cc grep tee awk timeout; do
        if ! command -v "$command" >/dev/null; then
            printf 'BLOCKED: missing %s; no tests ran.\n' "$command"
            return 2
        fi
    done
    export LC_ALL=C
    # Rebuild std and all target-side Rust dependencies. Explicit --target
    # excludes host macros/build scripts. rustc supplies its bundled runtime;
    # external-clangrt is only appropriate when linking an external runtime.
    unset CARGO_ENCODED_RUSTFLAGS CARGO_ENCODED_RUSTDOCFLAGS
    unset RUSTC_WRAPPER RUSTC_WORKSPACE_WRAPPER
    unset CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS
    unset CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUNNER
    export CARGO_TARGET_DIR="$run_dir/build"
    export CARGO_INCREMENTAL=0
    export CARGO_TERM_COLOR=never
    export RUSTFLAGS='-Zsanitizer=thread -Cdebuginfo=2 -Cforce-frame-pointers=yes'
    export RUSTDOCFLAGS="$RUSTFLAGS"
    export TSAN_OPTIONS='halt_on_error=1:exitcode=66:symbolize=1'
    export RUST_TEST_THREADS=4
    export RUST_BACKTRACE=1
    printf 'RUSTFLAGS=%s\nTSAN_OPTIONS=%s\nRUST_TEST_THREADS=%s\nCARGO_TARGET_DIR=%s\n' "$RUSTFLAGS" "$TSAN_OPTIONS" "$RUST_TEST_THREADS" "$CARGO_TARGET_DIR"
    run rustup toolchain install "$toolchain" --profile minimal --component rust-src
    run rustc +"$toolchain" -vV
    run cargo +"$toolchain" -V
    run cc --version
    local -a guarded_required=(
        concurrent_reader_sees_only_fully_initialized_first_publication
        concurrent_reuse_publishes_new_value_nonzero_link_and_complete_bits
        release_acquire_publishes_non_atomic_value_link_and_bits_each_round
        two_competitors_have_one_winner_held_until_both_attempts_finish
    )
    local -a slot_map_required=(
        fresh_index_cas_retry_rechecks_limits_one_and_two
        concurrent_length_stays_bounded_by_successful_insertions
        small_mpmc_transfers_unique_keys_before_shared_removal
        parallel_insert_and_iteration_publish_complete_strings
    )
    local -a lib_required=(
        claim_cas_failure_reports_actual_claimed_without_retry
        claim_cas_failure_reports_actual_bits_without_retry
        claim_cas_failure_reports_actual_next_generation_without_retry
        late_pop_reads_live_arbitrary_link_then_rejects_old_head
        claimed_remove_orders_move_free_link_count_without_callbacks_or_drops
        hook_panic_is_deferred_until_removal_restores_storage_invariants
    )
    local failed=0 profile suite listing output name rc
    local -a profile_args suite_args args required
    for profile in debug release; do
        profile_args=()
        if [[ $profile == release ]]; then profile_args=(--release); fi
        for suite in lib guarded slot_map; do
            suite_args=(--test "$suite")
            required=("${guarded_required[@]}")
            case $suite in
                lib) suite_args=(--lib); required=("${lib_required[@]}") ;;
                slot_map) required=("${slot_map_required[@]}") ;;
            esac
            args=(cargo +"$toolchain" test --locked -Zbuild-std --target "$target"
                --no-default-features "${suite_args[@]}" "${profile_args[@]}")
            listing="$run_dir/$profile-$suite-list.log"
            output="$run_dir/$profile-$suite-test.log"
            if logged "$listing" timeout --verbose --kill-after=10s "$suite_timeout" "${args[@]}" -- --list --format=pretty; then
                :
            else
                rc=$?
                printf 'SUITE_LIST_FAILED=%s/%s exit=%s\n' "$profile" "$suite" "$rc"
                failed=1
                continue
            fi
            for name in "${required[@]}"; do
                # Private lib tests have module-qualified names. Require exactly
                # one matching test; verify_execution later checks its actual ok.
                if ! awk -v name="$name" '
                    $0 == name ": test" || (length($0) > length(name) + 7 && substr($0, length($0) - length(name) - 7) == "::" name ": test") { n++ }
                    END { exit (n != 1) }
                ' "$listing"; then
                    printf 'MISSING_OR_DUPLICATE_REQUIRED_TEST=%s\n' "$name"
                    failed=1
                fi
            done
            # No filters, rc, include-ignored, or nocapture: pretty result lines
            # remain parseable; a declared ignored test makes validation fail.
            if logged "$output" timeout --verbose --kill-after=10s "$suite_timeout" "${args[@]}" -vv -- --test-threads=4 --format=pretty; then
                if verify_execution "$listing" "$output"; then
                    printf 'SUITE_VERIFIED=%s/%s\n' "$profile" "$suite"
                else
                    failed=1
                fi
            else
                rc=$?
                printf 'SUITE_FAILED=%s/%s exit=%s\n' "$profile" "$suite" "$rc"
                failed=1
            fi
        done
    done
    if (( failed )); then
        printf 'TSAN_RESULT=FAIL_OR_BLOCKED (inspect command exits and logs)\n'
        return 1
    fi
    printf 'VALIDATION_COMPLETE: six suites verified; awaiting final log status.\n'
}

# A subshell retains errexit inside main; do not call main in an if/|| context.
# Disable it only in the parent to collect the synchronous pipeline statuses.
set +e
( set -e; main ) 2>&1 | tee "$run_dir/run.log"
codes=("${PIPESTATUS[@]}")
set -e
rc=${codes[0]}
if (( codes[1] != 0 )); then rc=74; fi
# Final metadata also uses a waited, checked tee. A logging failure is fatal.
set +e
printf 'SCRIPT_EXIT=%s\nMAIN_EXIT=%s\nTOTAL_TEE_EXIT=%s\nLOG_DIR=%s\n' "$rc" "${codes[0]}" "${codes[1]}" "$run_dir" | tee -a "$run_dir/run.log"
final_codes=("${PIPESTATUS[@]}")
set -e
if (( final_codes[0] != 0 || final_codes[1] != 0 )); then rc=74; fi
if (( rc == 0 )); then
    # All tee processes have exited and closed their logs before this message.
    printf 'TSAN_RESULT=PASS (lib/guarded/slot_map, default debug/release; all logs closed)\n'
else
    printf 'TSAN_RESULT=NOT_PASSED exit=%s\n' "$rc" >&2
fi
exit "$rc"
