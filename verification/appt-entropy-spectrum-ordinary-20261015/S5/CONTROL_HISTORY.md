# Actual execution and finding history

This new output directory concerns only the phase-5 sublinear-rigidity scope. Previous phase-4 and publication-review directories remain frozen.

1. Owner ZIP and PAPER were copied/hash-checked; the ZIP was safely extracted in this reviewer-owned directory. No failure occurred. `INITIAL_CAPTURE.json` retains the exact archive member list.
2. Reviewer-authored `verify_inputs.py` ran once and passed at 2026-10-15T13:29:12.105358+00:00. It checks all 28 extracted files against the exact manifest/source map, including 15 scientific inputs and unchanged author result UTC. It executes no author/Git/Lean code.
3. Reviewer-authored `run_independent_checks.py` ran once, in `runs/20261015T133349.443900Z`. Both positive jobs returned zero and passed. Six negative-control children returned one at their intended false mathematical assertions. Their real tracebacks were individually read. All exact copied helper/harness bytes and stdout/stderr are retained.
4. There was no unexpected reviewer-program failure, mathematical source finding, author revision, or source correction. The negative-control AssertionErrors are expected actual failures of false variants, not failures hidden behind a summary PASS.
5. The author 18-case helper/result was read and hash-verified only. The reviewer did not execute it; its UTC 2026-10-15T13:16:32.941162+00:00 remains unchanged. The author's two earlier nonmathematical failures remain literally present in the owner ATTEMPT_LEDGER.

No Lean execution, audit expansion, source edit, Git mutation, new subagent, root-tree write, publication action, or outside communication occurred.
