C17 complete Lean counterexample

Start with RESULT.json, SEMANTIC_REVIEW.txt, and records/PrintInterfaces.log.
The three source modules are in sources/ and must be built in this order:
  CycleColoring, ChromaticPolynomial, LogConcavityCounterexample.

Pinned tools:
  Lean 4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52
  mathlib d13f23b723b8a846827a245b89c10fc7d3f11612
lakefile.toml and lean-toolchain describe a normal Lake project. The independently
recorded run used direct Lean commands and a fresh private output directory,
reusing only the pinned dependencies' build cache. The command log records the
actual compiler, options, sources, outputs, times, and exit codes.

The evidence package places the original final run at ../fresh-verification and
the independent driver/checker at ../verifier. It includes source snapshots,
compiled outputs for provenance, an inventory of all 98 owned declarations,
their complete dependency graph, the empty-kernel replay summary, the rejected
invalid-proof control, and source/build/log SHA256 manifests. Existing compiled
outputs are evidence artifacts, not inputs to a new fresh verification.

To repeat with an already prepared pinned environment:
  1. In verifier/config/environment.json, set toolchain_path and packages_root to
     your local exact-version installation/checkouts. Preserve all commit pins.
     Every listed package must be at its pinned commit with a clean tracked tree
     and have its dependency cache populated. Only official Lean/mathlib sources
     are needed; no user account credentials are required.
  2. Create verifier/locks and verifier/tasks if absent. In a separate copy of
     formalization/verify.json, set source_dir to the absolute sources directory.
     Preserve module names, order, audit scope, roots, and source hashes.
  3. Run python3 verifier/bin/leanctl.py doctor, then
     python3 verifier/bin/leanctl.py verify /absolute/path/to/your/verify.json.
The driver refuses wrong commits or input hashes, serializes runs under its
lock, snapshots sources, fresh-compiles every owned module, checks all owned
declarations and their closure, starts from mkEmptyEnvironment 0, and runs an
invalid-proof negative control. It never installs tools or downloads packages.

For the normal Lake build alone, use the pinned lean-toolchain and lakefile.toml.
That is a convenient compilation route, but is not a replacement for the full
independent audit and empty-kernel replay described above.

The public evidence profile removes internal collaboration identifiers from two
environment-config copies and regenerates their enclosing SHA manifests. Its
PUBLIC_PROFILE.json records the exact transformed files and preserves the hash
of the unmodified execution archive. All proof source bytes, compiled outputs,
audit code, logs, mathematical references, and proof-result data are unchanged.

Scope is the C17 disproof under the standard endpoint-retaining zero-extension
convention. C12, the infinite family, the cycle classification, alternate endpoint
conventions, and claims of publication priority are not formalized here.
