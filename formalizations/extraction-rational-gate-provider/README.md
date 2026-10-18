# Concrete binary provider for rational fifths

This separate author checkpoint constructs finite little-endian binary output
for the rational coordinates needed by a possible concrete fixed gate library.
It is not part of any previously frozen manuscript or independent audit.

`Fifths.lean` implements an explicit five-state transition table. No division,
real number or approximation oracle occurs in that executable transition/run.
Every transition emits one bit by cons and reuses the stored output tail.
For initial state a in {0,1,2,3,4}, after p transitions the actual output value is
floor(a*2^p/5), its length is p, and the retained remainder is (a*2^p)%5.
The division/modulus occur only in the correctness theorems. `Steps` describes
the actual table transitions; `run_steps` constructs a p-transition execution.

`SignedFifths.lean` retains the sign as data, builds the binary denominator
2^p as p zero bits followed by one, and proves the signed approximation error
is strictly below 2^(-p), also after casting to real numbers. The numerator
and denominator output lengths sum to 2p+1, excluding the sign bit. These are
19 named theorems, indexed in ROOTS.txt; no caller correctness certificate is
required. Check.lean exercises the actual program at all five states and small
precisions, and ProofCheck.lean reports every theorem type and axiom set.

The operational claim is the stated finite-state/output interface. It does not
charge Int/Nat materialization, canonical trimming, input-clock construction,
all compiler structures or machine runtime. In particular a count of output
bits is not substituted for those costs. The sign representation may retain
negative zero and the numerator may contain high zero bits; the forthcoming
native Word packet bridge must normalize them and count that work separately.

This checkpoint has ordinary Lean author checks only until its report records
an aggregate build. It has no independent empty-kernel replay or forged-proof
controls. A whole compiler bit-time theorem is still open. A concrete SU(2)
library, its inverse/density theorem, and the final numerical compiler provider
bridge are separate obligations; no new universality result is claimed here.
Lean 4.34.1 and Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 are pinned.
Shared dependencies and all outputs are on the verified D-backed data mount.
