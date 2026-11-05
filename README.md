# php2shell-chase

The smallest Rust model of one PHP2Shell bug, verified with [Verus](https://github.com/verus-lang/verus). This version **chases the bug**: it writes down the property the bug breaks and asks Verus to prove it after every way a request can end.

Companion repos: [php2shell-plain](https://github.com/avrevic/php2shell-plain) (Verus, not chasing), [php2shell-lean-chase](https://github.com/avrevic/php2shell-lean-chase) and [php2shell-lean-plain](https://github.com/avrevic/php2shell-lean-plain) (Lean 4).

## The property

```rust
/// A published `PS(id)` points to bytes the current request heap still owns.
pub open spec fn ps_id_live(worker: Worker, heap: RequestHeap) -> bool
```

The heap carries a ghost `generation` that ends with the request (erased at compile time). A pointer is live only if it was made in the current generation. C has no such tag. Writing it down is the part that targets this bug.

## Result

| Function | PHP | Verus |
|---|---|---|
| `publish_session_id` | `MULTIPART_EVENT_FILE_START` | verified |
| `request_end_normal` | `MULTIPART_EVENT_END` | verified |
| `request_end_fatal_oom` | OOM, `zend_bailout` | **failed: postcondition `ps_id_live` not satisfied** |
| `request_end_fatal_oom_fixed` | OOM with the fix (clear globals first) | verified |
| `upload_progress_cleanup` | next request, cookie | verified, given `ps_id_live` |

```
error: postcondition not satisfied
    |
    |     ensures ps_id_live(out.0, out.1),
    |             ^^^^^^^^^^^^^^^^^^^^^^^^ failed this postcondition
verification results:: 8 verified, 1 errors
```

Verus points at the exact edge, the fatal out-of-memory path, and the fixed edge proves. **With the property written down, the flaw is found.**

## The PHP feature being modelled

[PHP2Shell](https://www.wiz.io/blog/php2shell-php-rce), CVE-2026-109618, "remote process-memory disclosure". This is the session upload-progress path and nothing else:

1. `MULTIPART_EVENT_FILE_START`: during multipart parse, before normal request init, PHP allocates the session id on the request heap and publishes it in the worker global `PS(id)`.
2. Normal end: `php_rshutdown_session_globals` clears `PS(id)`, then the request heap is destroyed.
3. Fatal out-of-memory: `zend_bailout` (a `longjmp`) skips that clear. The heap is destroyed anyway, and `PS(id)` keeps pointing into it.
4. The next request on the same worker reaches upload-progress cleanup, trusts `PS(id)` (pointer + length) and copies those bytes into the `PHPSESSID` cookie.

`Worker.ps_id` is `PS(id)`. `RequestHeap` is the `emalloc` arena. The C pointer is an offset and a length into it.

## Run it

```sh
probe-verus setup            # installs Verus and its Rust toolchain
cargo verus verify           # Verus
probe-verus extract --with-spec-text .   # VeriLib probe output in .verilib/probes/
```
