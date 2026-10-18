# Separate local reader revision 2

This revision rereads the complete original local raw-resource evidence. It never runs or modifies Lean, the producer, the 372 frozen source inputs, the original reader, the workflow or any older scope. The mathematical source manifest remains 582008527e7b22047496b0e0a462a96415575047d804d1340f11021034b46f41 (364 theorem /186 model /135 controls).

The frozen producer renders every EXECUTION.runtime value with str(v), including actual_executables. The original local reader compared that recorded string to the PRE_AUDIT.binaries object. This is a reader format mismatch, not a kernel failure. The original reader failure and all original evidence must be retained.

The sole core-reader patch requires the local field to have exactly Python string type and exactly equal str(pre['binaries']). There is no literal_eval, eval or arbitrary type compatibility. The local wrapper additionally compares pre.binaries to the current official D-pinned actual executables verified by the storage/runtime guard. All source, freshness, stage-command, whole-closure, exact-control, canonical-axiom and pre/post checks are unchanged. The hosted portable_binary_inputs branch remains an object comparison.

READER_HASHES.json binds these execution/reader files independently. MINIMAL_DIFF.patch and PROVENANCE.json identify the original frozen recipe. The selftest constructs fixture EXECUTION files by executing the exact source-bound producer serialization statement with controlled fixture parameters, covering both local and hosted branches. All such fixtures are explicitly synthetic and do not constitute a CI or new kernel run.

Commands from the frozen audit directory:

    python3 verification/reader-local-v2/verify_local_v2.py verification/raw-resource-TIMESTAMP
    python3 verification/reader-local-v2/selftest_v2.py verification/raw-resource-TIMESTAMP
    python3 verification/reader-local-v2/seal_local_v2.py verification/raw-resource-TIMESTAMP

Report the outcomes separately: mathematical kernel/135 controls, original local reader format failure, and independently bound local-reader-v2 full-data reread. A producer PASS alone is not artifact acceptance. Hosted CI has its own actual-run and download checks using the unchanged frozen branch.
