# Hydrological tree identifiability — partial Lean formalization

**Partial formalization; NOT the all-tree Jacobian theorem, its conjecture
corollaries, cancellation classification, or positive-fiber enumeration.**

This initial development checkpoint establishes actual finite-dimensional
polynomial coefficient spaces and their affine Frechet derivatives, and the
repeated-block determinant identity used by the proposed gluing proof. The
polynomial-gluing derivative and the connection to the actual tree compartment
matrix still have to be proved. No finite checker or assumed Jacobian is used
as a substitute for those missing bridges.

Lean 4.34.1 and Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 are pinned.
The first two source modules compiled on the initial WSL development host;
independent CI and hash-bound replay evidence are being established separately.
Only completed run receipts certify their own exact source bytes.

No completion Release, DOI, external peer review, or priority claim is made.
Yongxian Zhang (张永贤), School of Computer Science and Engineering,
South China University of Technology. mxymmxym1@gmail.com.
ORCID 0009-0000-3864-3536. No external funding; AI-assisted development.
Existing repository and third-party notices remain in force. Original additions
retain all rights not otherwise granted by an applicable existing license.
