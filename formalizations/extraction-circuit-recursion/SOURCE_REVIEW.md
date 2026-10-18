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
`SKSynthesis.lean` then proves a literal finite-word recursion with error
`2^-p` and length `C*(p+1)^5`. `FinitePrecision.lean` connects its actual words
to the original extraction circuit, its overall phase and actual local
discard. The later numerical modules implement finite rational net selection,
conditioned factor oracles and a complete relative-oracle word recursion
with the same error and length endpoint. Turing bit complexity is not yet
proved.

`EFFECTIVE_MODEL.md` records the necessary finite descriptions and precision
interfaces. The original proposition does explicitly assume an efficiently
computable library; that assumption is stronger than this package's
finite-library gate-count existence theorem. `OccupationArithmetic.lean` and
`DyadicPrecision.lean` add integer-mass arithmetic and an integer precision
schedule without claiming that the remaining classical algorithm exists
under the theorem's weaker hypotheses.
