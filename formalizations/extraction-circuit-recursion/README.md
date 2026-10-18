# Original-wire occupation recursion

Status: **BUILD_ONLY**. Lean 4.34.1 and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

This independent extension leaves the earlier 41-module/227-root
`extraction-circuit-completion` milestone and all older audit scopes unchanged.

`compressionCircuit k` is one literal list of existing-wire one-qubit gates
and CNOTs, on `originalWireCount k = 2*k` original qubits. Its definition
executes the previous circuit on the original suffix and then applies one
common occupation step to the fresh pair and the compact code. The remaining
original wires are spectators. No initialized ancillary input is assumed.

The compiled theorem `compressionCircuit_action` proves the all-k recursion
on every actual normalized `bitOccupation` vector. The previous-stage action
is discharged by induction, including the zero-copy base case.
`compressionCircuit_matrix` and `compressionCircuit_coherent` retain all
coherences. `compressionCircuit_purePower` applies the same word to the actual
unknown iid tensor amplitudes in the explicit original paired-bit convention.

The code occupies a prefix of `2 * clog_4(binomial(k+3,3))` qubits and the
remaining original qubits are zero. `compressionCircuit_length` binds the
actual recursively assembled list length to the sum of stage budgets, and
`compressionCircuit_polynomial_bound` proves the explicit bound

```
20480*k*(k+2)^6*(6*clog_2(k+3)+2)^2 + 100*k^2.
```

`extractionCircuit k` appends literal H/CNOT operations on the freed original
zero pairs. `extractionOutput_purePower` proves exact standard Bell output from
every normalized unknown pure iid input after the explicit product family of
local discard Kraus operators. The output has `bellPairYield k = k-encodingPairs k`
Bell pairs. `pairwiseCoordinates_physical` connects the chosen bit coordinates
to physical copywise Alice/Bob coordinates through separate local digit maps;
`readoutCoordinates` then splits each party's original qubits locally.
`extractionCircuit_polynomial_bound` binds the displayed bound to this complete
actual word, including Bell preparation.

`bellPairYield_floor` identifies the yield with exactly
`floor(k - (1/2)*log_2(r_k))`. `bellPairYield_cPPT_maximal` applies the existing
physical cPPT converse to exclude any larger uniform exact integer output,
including arbitrary global unitaries. `extractionCircuit_isBigO` proves
`O(k^7 * log_2(k+3)^2)` for the actual final word.

`bitPurePower_copywiseInput` connects the input to the literal tensor density
in the existing explicit copywise coordinates. `extractionOutput_robust` and
its overall-phase version retain fidelity at least `1-2*delta` for an actual
matrix approximation of the final circuit. `compiledExtraction_fidelity`
derives that bound from per-gate error `delta/G` for any supplied literal
replacement compiler; `compiledExtraction_length` counts its actual words.
These are conditional stability/counting lemmas, and do not assert the
existence of a finite-library compiler.

The exact continuous-library circuit and finite-library synthesis existence,
including their physical output and gate counts, are now proved here.
Effective classical angle evaluation and finite-precision running time remain
open; the complete manuscript is not thereby fully formalized.
The SK continuation now proves the commutator perturbation bound
`4*delta*epsilon + 2*epsilon^2` directly from actual matrix algebra, and derives
a fixed finite approximation net from inverse-closed universality and proved
SU(2) compactness. `su2_balanced_commutator` constructs the actual balanced
decomposition, with both factor distances at most the square root of the
target distance from identity. Degenerate intertwiners are handled explicitly.
`su2_synthesis_dyadic` closes the actual finite-word recursion: for every
precision p and SU(2) target, inverse-closed universality implies a literal
library word of length at most `C*(p+1)^5` and operator error at most `2^-p`.
The net, balanced decomposition and correction bounds are all internally
proved. This conservative exponent 5 is sufficient for the manuscript.
`finiteLibrary_extraction` connects that theorem through actual U(2) phase
representatives and dimension-independent single-wire norm bounds to the same
complete original-wire extraction program. For every delta>0 it constructs an
actual word b using only the fixed finite library and CNOT, with operator
error at most delta up to its harmless total phase and output fidelity at
least `1-2*delta` under the same local discard channel. Its actual length obeys

```
length(b) <= C*G(k)*(log_2(max(1,G(k)/delta))+2)^5,
G(k) = length(extractionCircuit k).
```

The constant C depends only on the finite inverse-closed universal library.
No net, calibration or synthesis conclusion is supplied as a premise.
Classical bit complexity remains open; see
`SOURCE_REVIEW.md` and `EFFECTIVE_MODEL.md`. The latter distinguishes the
manuscript's effective-library assumption from the weaker hypotheses of the
proved gate-count existence theorem, and records the required finite-input,
net-selection, numerical-stability and bit-cost interfaces.
`OccupationArithmetic.lean` proves integer-ratio identities, nonzero-mass
lower bounds and the exact rational square-root coefficients of the actual
merge angles; these supply arithmetic support without a running-time claim.
`DyadicPrecision.lean` gives the finite integer request
`p + clog_2(max(1,G(k)))` and proves an actual library word with error at most
`2^-p`, fidelity at least `1-2*2^-p` and actual length at most
`C*G(k)*(p+clog_2(max(1,G(k)))+1)^5`. Only the precision budget is computable
here; selection of the approximating word remains an existence theorem.
`RationalSelection.lean` implements a choice-free finite rational argmin and
proves that score error at most eta increases the selected true distance by
at most 2*eta. The subsequent modules supply its actual numerical scores
and an internally derived fixed table; their Turing bit costs remain open.
`ConditionedConjugacy.lean` supplies four explicit Pauli frames. Their
intertwiner masses sum to `8*(1-r^2)`. Rational approximate mass selection
then gives a normalization denominator at least half a positive residual
stopping threshold. The actual chart conjugator and its conjugacy action
are proved. Subsequent modules implement the conditioned oracle formulas.
`OracleArithmetic.lean` implements rational-output oracle addition, negation,
bounded multiplication and inversion with explicit input precision schedules.
`OracleSqrt.lean` implements square-root approximation with natural floor
and the actual integer square-root routine, proves its error, and bounds its
dyadic numerator. `HalfAngleEvaluation.lean` gives finite rational programs
for both sine and cosine of the actual rational-occupation merging angle
divided by `2^n`. They make no input-oracle calls, use exactly `n+1` integer
square roots and `2*n` rational arithmetic nodes, and return dyadic outputs
with numerator at most `2^(p+1)`. At the actual active-register width their
largest square-root precision is at most `16*(k+3)^3*(p+2)`. These are actual
program/error/operation-count results. They do not yet attach descriptions
to every gate of the extraction compiler or prove Turing bit costs of the
arithmetic subroutines.
`QuaternionOracles.lean` composes stored four-coordinate numerical packets
for actual SU(2) word products, with input query precision at most
`p+4*length(w)` and exactly `length(w)` gate-packet requests in the explicit
schedule. `NetOracle.lean` computes rational squared-distance scores and
proves their error, then implements the online fixed-table selector with
base error at most `1/288`. `PrecomputedNet.lean` derives the offline table
internally by enumerating all words below a fixed library-dependent bound
obtained from universality. Its `numericalBase_exists` needs only correctness
of the numerical input oracles online. A concrete integer-packet / `2^p`
dyadic entry interface and its numerator-size bound are included. These
results close numerical base selection.
`ConditionedOracleSelection.lean` now implements the chart-mass scoring and
overlapping rational residual stopping branches. `BalancedReference.lean`
computes the actual reference-axis factor oracles. The normalized
intertwiner and its SU(2) entry oracle are proved in
`NormalizedIntertwinerOracle.lean`, using the derived positive denominator
bound and the implemented inverse/square-root precision schedules.
`ConditionedFactors.lean` closes the complete numerical factor routine:
above a dyadic stopping threshold it emits two entry oracles whose exact
SU(2) values form the target commutator and obey the required balance bound.
No decomposition certificate is supplied as a premise.
`NumericalCorrection.lean` and `NumericalSK.lean` now close the complete
relative-oracle numerical word recursion. `numericalSU2Synthesis_dyadic`
uses only a fixed finite word table, an explicit inverse-label table,
dyadic gate/target entry packets and integer p online. The actual computed
word has length at most `C*(p+1)^5` and operator error at most `2^-p`.
No exact-real target, classical choice or unimplemented commutator primitive
occurs in this online program. All factor and stopping correctness is
derived internally. The stopping exponent at the selected depth is at most
`8*(p+1)+40`. This is correctness of an explicit finite oracle program;
aggregate query/precision bounds, provider costs and Turing bit costs remain
separate obligations. Original gate-description binding, phase normalization
and a computable occupation encoding are also still required to turn the
original extraction family into a uniform classical synthesis algorithm.
The finite embedding
and real gate construction are still `noncomputable`; this package makes no
classical running-time claim.

Reproduction uses the shared pinned dependency without copying Mathlib.
On the current workspace, run the storage-verifying, shared-lock wrapper:

```
wsl -d Ubuntu-22.04 -- python3 /mnt/d/math/tmp/extraction-resume-20261018/worker_build.py /mnt/lean-research-d/worktrees/extraction-lean-protocol-20261016 formalizations/extraction-circuit-recursion
```

The ordinary build and all 292 root type/axiom prints passed with 3863 jobs in
`D:/math/tmp/extraction-resume-20261018/build-logs/20261018T173344763419Z-extraction-circuit-recursion.log`.
No independent empty-kernel replay or forged-proof control is claimed.
