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

/// The request heap (`emalloc` arena). `destroy` is the end of a request.
pub struct RequestHeap {
    pub bytes: Vec<u8>,
    /// Which request this heap belongs to. Ghost: erased at compile time.
    pub generation: Ghost<nat>,
}

/// `zend_string *` stored in `PS(id)`: where the bytes are, and which request made them.
#[derive(Clone, Copy)]
pub struct SessionId {
    pub off: usize,
    pub len: usize,
    pub generation: Ghost<nat>,
}

/// Process-lifetime globals of one PHP worker. `ps_id` is `PS(id)`.
pub struct Worker {
    pub ps_id: Option<SessionId>,
}

/// The spec: a published `PS(id)` points to bytes the current request heap still owns.
pub open spec fn ps_id_live(worker: Worker, heap: RequestHeap) -> bool {
    match worker.ps_id {
        Some(id) => id.generation@ == heap.generation@ && id.off + id.len <= heap.bytes.len(),
        None => true,
    }
}

impl RequestHeap {
    pub fn new() -> (heap: RequestHeap)
        ensures heap.bytes.len() == 0,
    {
        RequestHeap { bytes: Vec::new(), generation: Ghost(0) }
    }

    /// End of a request: every allocation dies; the next request starts a new generation.
    pub fn destroy(self) -> (heap: RequestHeap)
        ensures
            heap.bytes.len() == 0,
            heap.generation@ == self.generation@ + 1,
    {
        RequestHeap { bytes: Vec::new(), generation: Ghost(self.generation@ + 1) }
    }
}

/// `MULTIPART_EVENT_FILE_START`: allocate the id on the request heap and publish it in `PS(id)`.
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

/// `php_rshutdown_session_globals`.
pub fn rshutdown_session_globals(worker: Worker) -> (out: Worker)
    ensures out.ps_id is None,
{
    let mut worker = worker;
    worker.ps_id = None;
    worker
}

/// `MULTIPART_EVENT_END`: clear the globals, then the heap dies.
pub fn request_end_normal(worker: Worker, heap: RequestHeap, sid: u8) -> (out: (Worker, RequestHeap))
    requires heap.bytes.len() < usize::MAX,
    ensures ps_id_live(out.0, out.1),
{
    let (worker, heap) = publish_session_id(worker, heap, sid);
    let worker = rshutdown_session_globals(worker);
    (worker, heap.destroy())
}

/// THE BUG. Out of memory in the same window: `zend_bailout` skips
/// `php_rshutdown_session_globals`, the heap is destroyed anyway. Verus cannot prove the
/// postcondition: `PS(id)` points into a heap generation that no longer exists.
pub fn request_end_fatal_oom(worker: Worker, heap: RequestHeap, sid: u8) -> (out: (Worker, RequestHeap))
    requires heap.bytes.len() < usize::MAX,
    ensures ps_id_live(out.0, out.1),
{
    let (worker, heap) = publish_session_id(worker, heap, sid);
    (worker, heap.destroy())
}

/// The same fatal edge with the fix: clear the worker globals before the heap is freed.
pub fn request_end_fatal_oom_fixed(worker: Worker, heap: RequestHeap, sid: u8) -> (out: (Worker, RequestHeap))
    requires heap.bytes.len() < usize::MAX,
    ensures ps_id_live(out.0, out.1),
{
    let (worker, heap) = publish_session_id(worker, heap, sid);
    let worker = rshutdown_session_globals(worker);
    (worker, heap.destroy())
}

/// The next request: upload-progress cleanup copies `PS(id)` into the `PHPSESSID` cookie.
/// Given `ps_id_live`, the read is in bounds and returns this request's own bytes.
pub fn upload_progress_cleanup<'a>(worker: &Worker, heap: &'a RequestHeap) -> (cookie: &'a [u8])
    requires ps_id_live(*worker, *heap),
{
    match worker.ps_id {
        Some(id) => vstd::slice::slice_subrange(heap.bytes.as_slice(), id.off, id.off + id.len),
        None => &[],
    }
}

} // verus!
