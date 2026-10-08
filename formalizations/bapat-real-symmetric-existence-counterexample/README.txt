Complete real symmetric INTEGER Bapat counterexample — Lean source and verification evidence

Theorem: BapatRealExistence.exists_integer_real_symmetric_counterexample
See formalization/sources/BapatIntegerCounterexample.lean and formalization/RESULT.json.
There exist a finite N>4, an integer symmetric matrix B whose real cast is positive
definite and non-diagonal, with negative q-permanent derivative at q=1, and rational
0<q0<q1<1 with P(q1)<P(q0). The q-permanent uses the ordinary full inversion statistic.
No explicit dimension bound or numerical witness matrix is asserted.

67 owned modules were freshly compiled in a new build directory, with every owned
module audited. See fresh-verification/manifest/replay-summary.json for the exact
counts and empty-kernel trust-level-0 replay result. Full expected/actual standard
axiom signatures, declaration inventories, closure graphs, command records,
source hashes, cache stability guard and invalid-proof rejection control are retained.
Old partial/foundational runs are not substituted for this verification.

Source and proof-route correspondence: formalization/SEMANTIC_REVIEW.txt.
Mathematical source commit: 2509263c1028d6814658174b2830a3d658e76c1c in mxym/math.
The direct Gaussian Gini evaluation and endpoint-sign proof of non-diagonality
are documented alternatives to corresponding reference arguments.

Reproduction:
Provide an existing official Lean 4.34.1 toolchain (commit
5045d0056413266e57c625dcd7c365b10e377c52), the official mathlib checkout at
d13f23b723b8a846827a245b89c10fc7d3f11612, and every pinned official dependency
checkout in verifier/config/environment.json, including their matching compiled
library caches. Each package is a direct child of PACKAGES_ROOT, named as in that
configuration. Do not use previously built Bapat oleans in the search path.

  python3 reproduce.py --toolchain TOOLCHAIN --packages-root PACKAGES_ROOT --output NEW_OUTPUT

NEW_OUTPUT must not already exist. The adapter relocates only paths, copies the
unchanged verifier and controls, and runs a fresh verification with the supplied
source hashes. It does not install, download, build dependencies, mutate their
checkouts or request credentials. The verifier checks official commit pins and
rejects tracked modifications. Published execution records replace private absolute paths and thread identifiers with
role placeholders. reproduce.py supplies actual relocated paths for a new execution.
PUBLICATION_PROJECTION.json records original/projected hashes; ORIGINAL_FILES.json
and ORIGINAL_SHA256SUMS preserve the original private delivery manifest bytes.

No toolchain binaries, dependency caches, generated oleans or credentials are included.
This is the public projection of the completed proof package. It does not itself
certify a subsequent publisher's uploaded bytes.
