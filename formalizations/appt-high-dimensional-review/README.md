# Independent APPT mathematical review and Lean work

**In-progress verification workspace. The draft Lean modules in this checkpoint have not yet completed compilation. No new high-dimensional result is labelled formally verified here.**

The sources use the existing actual complex density-matrix and all-global-unitary APPT definitions from the unchanged qutrit package. The current formalization target is the arbitrary-dimensional physical witness, including the partial-transpose convention bridge and the least-diagonal star estimate needed by the entropy proof. The counterexample SOS and rational purity gaps are kept separate from the still-unclosed generic quantum sufficiency bridge.

Pinned toolchain: Lean 4.34.1; Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612. The bounded build runner records failed attempts as failures. Existing proof/manuscript and immutable release sources are not changed. There is no claim of external peer review or whole-result Lean verification.
