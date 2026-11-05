//! PHP2Shell, session upload-progress (CVE-2026-109618), smallest Rust model, verified with Verus.
//!
//! This crate CHASES the bug: it states the property the bug breaks and asks Verus to prove it
//! after every way a request can end.
//!
//! The PHP feature, and only it:
//! 1. `MULTIPART_EVENT_FILE_START`: during multipart parse, before normal request init, the
//!    session id is allocated on the request heap and published in the worker global `PS(id)`.
//! 2. Normal end: `php_rshutdown_session_globals` clears `PS(id)`, then the heap is destroyed.
//! 3. Fatal out-of-memory: `zend_bailout` (a longjmp) skips step 2's clear; the heap is destroyed
//!    anyway, and `PS(id)` keeps pointing into it.
//! 4. The next request on the same worker reaches upload-progress cleanup, trusts `PS(id)`
//!    (pointer + length) and copies those bytes into the `PHPSESSID` cookie.
//!
//! The request heap carries a ghost generation that ends with the request. A pointer is only
//! live if it was made in the current generation. This is the one thing C does not track.

use vstd::prelude::*;

verus! {

/// The request heap: PHP's per-request `emalloc` arena (`Zend/zend_alloc.c`).
/// Everything a request allocates lives here and dies together when the request ends.
///
/// `generation` is the one addition C does not have: a ghost counter (erased at compile
/// time, never executed) naming which request owns this heap. It is what lets the spec say
/// "this pointer belongs to a request that is already over". Without it, a freed slot and a
/// reused slot look the same, which is exactly why C cannot see the bug.
pub struct RequestHeap {
    pub bytes: Vec<u8>,
    /// Which request this heap belongs to. Ghost: erased at compile time.
    pub generation: Ghost<nat>,
}

/// `zend_string *` stored in `PS(id)`: where the bytes are, and which request made them.
#[derive(Clone, Copy)]
/// The value of `PS(id)`: in PHP a `zend_string *`, here an offset and a length into the
/// request heap, plus the ghost generation of the request that allocated it.
/// A real pointer cannot be modelled in safe Rust across requests (the borrow checker rejects
/// a reference that outlives its heap), so an index stands in for it. The bug survives the
/// change from pointer to index; that is the point of the model.
pub struct SessionId {
    pub off: usize,
    pub len: usize,
    pub generation: Ghost<nat>,
}

/// One PHP worker process (an FPM or Apache child). It serves many requests in turn, and its
/// globals outlive every one of them. `ps_id` stands for `PS(id)`, the session module's
/// current session id. Other fields of the same kind exist in PHP (`BG(unserialize)`,
/// `EG(last_fatal_error_backtrace)`); the write-up's other bugs follow the same pattern.
pub struct Worker {
    pub ps_id: Option<SessionId>,
}

/// THE PROPERTY. A published `PS(id)` points to bytes that the current request heap still
/// owns: same generation, and inside the heap.
///
/// This is the only line in the crate written with the bug in mind, and it is general: it is
/// the ordinary rule "a long-lived global must not point into short-lived memory". Every
/// request-ending function below must re-establish it in its `ensures`. Verus fails exactly
/// where it does not hold.
pub open spec fn ps_id_live(worker: Worker, heap: RequestHeap) -> bool {
    match worker.ps_id {
        Some(id) => id.generation@ == heap.generation@ && id.off + id.len <= heap.bytes.len(),
        None => true,
    }
}

impl RequestHeap {
    /// A fresh request heap, generation 0. Verified.
    pub fn new() -> (heap: RequestHeap)
        ensures heap.bytes.len() == 0,
    {
        RequestHeap { bytes: Vec::new(), generation: Ghost(0) }
    }

    /// End of a request (`shutdown_memory_manager` in PHP): every allocation dies and the next
    /// request gets a new generation. The postcondition records both facts, so callers can reason
    /// that anything pointing at the old generation is dead. Verified.
    pub fn destroy(self) -> (heap: RequestHeap)
        ensures
            heap.bytes.len() == 0,
            heap.generation@ == self.generation@ + 1,
    {
        RequestHeap { bytes: Vec::new(), generation: Ghost(self.generation@ + 1) }
    }
}

/// PHP: the session upload-progress handler (`ext/session/session.c`, the RFC 1867 callback)
/// on `MULTIPART_EVENT_FILE_START`. It runs during multipart parsing, before normal request
/// init, allocates the session id on the request heap and stores it in `PS(id)`.
///
/// Ensures `ps_id_live`: right after publishing, the pointer is good. Verified.
pub fn publish_session_id(worker: Worker, heap: RequestHeap, sid: u8) -> (out: (Worker, RequestHeap))
    requires heap.bytes.len() < usize::MAX,
    ensures
        ps_id_live(out.0, out.1),
        out.1.generation@ == heap.generation@,
{
    let mut heap = heap;
    let mut worker = worker;
    let off = heap.bytes.len();
    heap.bytes.push(sid);
    worker.ps_id = Some(SessionId { off, len: 1, generation: Ghost(heap.generation@) });
    (worker, heap)
}

/// PHP: `php_rshutdown_session_globals`, which clears the session globals (`PS(id)`
/// included). This is the call the bug skips. Verified: afterwards `ps_id` is `None`.
pub fn rshutdown_session_globals(worker: Worker) -> (out: Worker)
    ensures out.ps_id is None,
{
    let mut worker = worker;
    worker.ps_id = None;
    worker
}

/// PHP: `MULTIPART_EVENT_END`, the normal end. Clear `PS(id)` first, then free the heap.
/// The order matters: the global is gone before the memory it pointed to.
/// Verified: `ps_id_live` holds afterwards (vacuously, `ps_id` is `None`).
pub fn request_end_normal(worker: Worker, heap: RequestHeap, sid: u8) -> (out: (Worker, RequestHeap))
    requires heap.bytes.len() < usize::MAX,
    ensures ps_id_live(out.0, out.1),
{
    let (worker, heap) = publish_session_id(worker, heap, sid);
    let worker = rshutdown_session_globals(worker);
    (worker, heap.destroy())
}

/// THE BUG (CVE-2026-109618). The request runs out of memory inside the upload window. PHP
/// raises a fatal error and calls `zend_bailout`, a `longjmp` straight to the request's outer
/// frame. `php_rshutdown_session_globals` never runs, but the heap is still freed. `PS(id)`
/// keeps pointing into a generation that no longer exists.
///
/// Verus: FAILED, "postcondition not satisfied" on `ps_id_live`. This is the only failing
/// function in the crate, and it is exactly the edge PHP fixed. The failure is the finding.
pub fn request_end_fatal_oom(worker: Worker, heap: RequestHeap, sid: u8) -> (out: (Worker, RequestHeap))
    requires heap.bytes.len() < usize::MAX,
    ensures ps_id_live(out.0, out.1),
{
    let (worker, heap) = publish_session_id(worker, heap, sid);
    (worker, heap.destroy())
}

/// The same out-of-memory edge with the fix: clear the worker globals before the request heap
/// is freed, on the bailout path too. PHP's patch fixes the class at its core rather than per
/// global; this models its effect on `PS(id)`. Verified, which shows the spec is not simply
/// unprovable on every fatal path.
pub fn request_end_fatal_oom_fixed(worker: Worker, heap: RequestHeap, sid: u8) -> (out: (Worker, RequestHeap))
    requires heap.bytes.len() < usize::MAX,
    ensures ps_id_live(out.0, out.1),
{
    let (worker, heap) = publish_session_id(worker, heap, sid);
    let worker = rshutdown_session_globals(worker);
    (worker, heap.destroy())
}

/// PHP: the next request on the same worker reaches the upload-progress cleanup before session
/// init resets `PS(id)`, trusts the pointer and length, and URL-encodes those bytes into the
/// `PHPSESSID` response cookie. After the bug, those bytes belong to another request: the
/// memory disclosure.
///
/// Requires `ps_id_live`. Under it the read is in bounds and returns this request's own
/// bytes. Verified. The requirement can only be met if every earlier request end
/// re-established it, which the bug edge does not.
pub fn upload_progress_cleanup<'a>(worker: &Worker, heap: &'a RequestHeap) -> (cookie: &'a [u8])
    requires ps_id_live(*worker, *heap),
{
    match worker.ps_id {
        Some(id) => vstd::slice::slice_subrange(heap.bytes.as_slice(), id.off, id.off + id.len),
        None => &[],
    }
}

} // verus!
