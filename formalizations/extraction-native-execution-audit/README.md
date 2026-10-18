This independent scope is fixed to mathematical Git commit `8b78ef1ea7c16af0bb98ae8fb6bb97ac3272ee78`.

It selects 33 theorem roots, 53 actual model definitions/inductives and 33 same-type forged-proof controls. The final nine concrete assembled roots are all included. All actual local imports and package configurations are frozen; unused TM2 and later outer-list modules are excluded. Existing 4378/605/340/372 scopes and all their tracked audit evidence are byte protected by a separate manifest. No old scope is enlarged.

Run `python3 reproduce.py --check-only` and `python3 selftest.py` without Lean. Run `python3 reproduce.py --fresh` locally only on the guarded D worktree; all owned package build directories are rebuilt independently while only pinned external dependencies share the Mathlib cache. The global build lock serializes local builds. Strict type/model export and kernel invocations use `-j1 -M4000`, and `LEAN_NUM_THREADS=1`; no memory increase is automatic.

The runner positively replays the complete theorem/model dependency closure into an empty trust-zero kernel. Every selected theorem is then forged with `True.intro` while retaining its exact type and universe parameters; its actual type dependencies are first positively replayed and rejection must be the kernel type mismatch naming that root. All model types and closed Core Expr definition bodies are exported and SHA256 bound; inductives export types, mutual group and constructor names and their complete kernel declarations remain in the replay closure.

The new workflow produces a separately named artifact. A separate job downloads it and runs the portable strict reader. Selftests include empty axiom sets and typed executable objects, malformed legacy strings, drift, missing controls, altered memory arguments, body/invocation changes, duplicate JSON keys and unsafe paths. Selftest fixtures are marked regression data and never count as mathematical verification.

No result is certified merely by freezing metadata. See SOURCE_REVIEW.md for the independently read source chain and the exact partial cost interpretation.
