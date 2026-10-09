# ECQC replay CI repair — 2026-10-09

The failed main-branch run [37899224209](https://github.com/mxym/math/actions/runs/37899224209)
passed the four mathematical/negative-control replay programs and failed only
at the final `sha256sum --check SHA256SUMS` step. The pure-state package had
outdated hashes for `QUTRIT_EXACT.md`, `README.md`, `paper.tex`, and `paper.pdf`.
The stabilizer package separately had an outdated `README.md` hash.

Git history identifies the changes: commit `54ad09a` added the completed qutrit
Lean correspondence and rebuilt the pure-state paper; commit `7961515` added
DOI metadata to both READMEs. Neither commit refreshed the manifests. The DOI
indexing omission was made during this agent's preceding publication turn.

All six exact replay programs were rerun in copied directories. Their source
bytes still equal the frozen v1 commit `c0a1085`; all passed, including the
eleven pure-state negative controls and the stabilizer checkers' corrupted
inputs. Both TeX sources were rebuilt and their normalized extracted PDF text
matches the stored PDFs. The pure-state bibliography has one underfull box;
the final build has no unresolved references or overfull boxes. This is a
targeted reproduction audit, not a new full mathematical review or Lean replay.

The corrected workflow checks both packages, verifies source hashes before
execution, reruns the exact programs, and checks hashes again afterward.
Assertions and negative tests are retained. Tag pushes no longer run the
moving branch workflow; branch pushes, pull requests, and manual dispatch
remain covered. Historical failed runs and immutable v1 snapshots remain
visible. The maintenance release supplies corrected reproducible archives;
the papers and checker algorithms themselves are unchanged.

- `LOCAL_REPLAY.json`: pre-repair mismatches, six replay exit codes, and PDF checks.
- `FAILED_HASH_STEP.log`: relevant lines from the original GitHub failure.
- `*-*.py.log`: literal replay output.
- [Maintenance release](https://github.com/mxym/math/releases/tag/ecqc-exact-replay-integrity-v1.1).

The original DOI attachment-level hashes remain valid: the stale manifests
inside the source bundles are a separate defect. A patch archival version
can replace the internal manifest without rewriting the original records.
