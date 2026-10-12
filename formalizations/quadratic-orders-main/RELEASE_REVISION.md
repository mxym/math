# Release tooling revision 2

This revision changes release tools, documentation and the public evidence selection only. All 1,256 received Lean source files remain byte-for-byte unchanged. The original Main certificate and its 125,368-constant empty-kernel replay are unchanged.

Independent final-copy review of the first candidate identified incomplete terminal recording/rechecking of fresh sidecars, audit-helper artifacts and run logs in the new public wrapper. It did not identify a changed mathematical source or a failed original Main proof. Revision 2 records and revalidates those bindings, records selected official inputs, checks exact loaded-module coverage, rechecks source/toolchain inputs at completion, and adds a complete run-output digest seal and read-only integrity checker. It also includes the final full 8,132-module object/sidecar evidence from the independent audit.

The new output checker reports artifact integrity, not a fresh theorem check. Its negative controls invoke the real public CLI with clearly synthetic artifact fixtures. The actual complete public fresh-source run has a separate completion receipt; neither a helper smoke nor these controls substitutes for that run.

The archive remains source-only and does not publish itself. Public writes and a successful final-copy gate are separate steps.
