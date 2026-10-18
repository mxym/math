# Finite-library synthesis boundary

The manuscript's `prop:pure-circuit` and author addendum v3 remain the exact
target. The new original-wire recursion establishes their continuous-library
circuit, final local discard, integer yield, gate growth and uniform stability.

The primary external SK reference is Dawson and Nielsen,
[The Solovay–Kitaev algorithm, v2](https://arxiv.org/pdf/quant-ph/0505030),
23 August 2005. Its instruction sets are finite, inverse closed, and generate
a dense subgroup of SU(d). The qubit algorithm uses a fixed initial net, a
balanced commutator decomposition, and recursive corrections. Its word-length
recurrence multiplies by five and gives a logarithmic exponent near 3.97.
The discussion on PDF page 7 explicitly excludes finite-precision arithmetic
costs from that analysis. Thus this reference alone does not discharge the
manuscript's bit-complexity claim.

No external SK theorem is imported into Lean, and no axiom or calibration
certificate is supplied. `CommutatorError.lean` proves cancellation and an
actual operator-norm perturbation bound. `FiniteNet.lean` and
`SpecialUnitaryNet.lean` derive a uniform fixed finite net from inverse closure,
density and proved compactness of the actual SU(2) matrix group.
`BalancedCommutator.lean` constructs the balanced decomposition with explicit
square-root plane rotations and internally proved quaternion-form conjugacy.
No effective net-search algorithm or complete finite-precision SK compiler is
yet provided.
