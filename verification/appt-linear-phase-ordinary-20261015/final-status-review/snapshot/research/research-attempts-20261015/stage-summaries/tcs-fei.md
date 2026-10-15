# Complete classical FEI: stage outcome and remaining mathematical gates

Author: Yongxian Zhang (张永贤), South China University of Technology. No external funding. OpenAI assisted research, computation and drafting. Original material all rights reserved; third-party results retain their attribution.

## Full target and outcome

The target throughout this stage is the unrestricted uniform-cube Fourier Entropy–Influence conjecture:

\[
\exists C<\infty\ \forall n\ge0\ \forall f:\{\pm1\}^n\to\{\pm1\},
\quad H(f)=\sum_S\widehat f(S)^2\log_2\frac1{\widehat f(S)^2}
\le C\sum_S|S|\widehat f(S)^2=C I(f).
\]

**This full target remains unproved and unrefuted here. New major solutions:0.** The stage did not substitute Fourier min-entropy, a quantum analogue, bounded dimension, a fixed function class, a better finite constant, or a dimension-dependent bound. Failure of a proposed intermediate lemma is not a global impossibility result.

The initial and follow-up primary screens found current restricted results and lower-bound improvements, but did not identify a complete classical FEI solution in the bounded discovery scope actually inspected. The current primary optimization entry still labels finiteness of the universal constant open. This is a bounded collision check, not an exhaustive priority certificate or an independent audit of every third-party proof.

## Exact mathematical content retained

The following material is written out with its actual proof scope. Apart from the separately frozen Han packet, these notes have not had independent ordinary review. None is being entered as a newly solved major conjecture.

| Material | Established within the written argument | Boundary |
|---|---|---|
| `ENTROPY_SPLIT_AND_OPEN_GATE.md` | Exact restriction identity `Delta_i H=Q_i+J_i`; conservative divergence bound and a sufficient adaptive induction gate | No universal adaptive `Q_i/I_i` bound proved |
| `TRUE_ENTROPY_GATE_EQUIVALENCES.md` | Standard scalar convexity gives `J_i<=(2/ln2)I_i`; full FEI, a global `sum Q_i` gate and an adaptive `Q_i` gate have equivalent finite-constant existence | An equivalent full-target formulation is still open |
| `MINIMUM_BASIS_REFORMULATION.md` | Linear input changes and character multiplication give the same-constant equivalent inequality `H<=C M`; exact matroid rank-profile formula for `M` | No uniform entropy estimate by this minimum basis cost |
| `CONCENTRATION_GATES_AND_QUANTIFIERS.md` | A uniform linear log-support bound carrying subexponentially small mass would imply full FEI by a finite-alphabet Chernoff/tensor argument | The needed uniform concentration hypothesis is not established |
| `MULTISCALE_PARAMETER_BARRIER.md` | Under the explicitly retained cutoff/coefficient assumptions, retuning KKLMS Theorem6.6 coefficients with `C2<=1/d,C3<=1` forces `ln C1>=4800d ln d` | Only that positive-coefficient optimization is blocked; not every proof of FEI |
| `BENT_SINGLE_FLIP_OBSTRUCTION.md` | A specified selector coordinate has true entropy-increment/influence ratio diverging with core dimension | Other coordinates remain available to adaptive induction |
| `LOCALIZED_SELECTOR_COST_BARRIER.md` | Distinct one-point selector replication incurs core influence; the selectors' total `Q` is charged to that cost | Arbitrary core conditional entropies remain uncontrolled; no global refutation |
| `PRODUCT_SPECTRA_AND_OPEN_STABILITY.md` | Exact independent squared spectral coordinates of a Boolean function reduce to even-dimensional bent support after character centering | Already within the known partially bent class; no quantitative stability theorem |
| `BALANCED_GATE_ATTACK.md` | Known composition identity and the balancing function `z f(x)` give the same-constant equivalence between full FEI and a uniform balanced-gate bound `H/(I-1)` | The timed search provides neither an unbounded family nor that uniform upper bound |
| `MULTIPLICATION_ENTROPY_ROUTE_REJECTED.md` | Explicit8-variable functions satisfy `H(fg)>H(f)+H(g)` with exactly additive influence; full spectra and a strict integer-power comparison prove the sign | Refutes a proposed intermediate subadditivity lemma, not FEI |
| `TRUE_ENTROPY_OF_PROXY_COUNTEREXAMPLE.md` | The Han-family true `Q_i/I_i` converges by a summable analytic majorant; an exact rational depth10 certificate gives every coordinate `Q_i/I_i>101/25` | Excludes constant4 only; it does not give an unbounded true-entropy family |

The initial scalar entropy prototype omitted the entropy of the total nonempty mass. Its false values were rejected by independent full-truth-table controls at depth2. `INITIAL_SCALAR_FORMULA_ENTROPY.*` is preserved as explicitly superseded discovery history. The corrected `scalar_formula_entropy.py` includes both mass-normalization terms and agrees with full truth tables at the listed finite depths. The computed entropy increment ratio near6.600846 is not the family's global FEI ratio and is not a new universal-constant lower bound.

## Separately reviewed auxiliary question

The exact all-coordinate negative answer to Han's Question3.1 is preserved in immutable `han-q31-review-v1/` and `han-q31-review-v2/`. It concerns an absolute Fourier-overlap proxy, with a homogeneous monotone read-once family making that proxy divided by influence diverge at every essential coordinate. The parent reports an independent mathematical PASS; source-bound integration and any final index wording belong to the parent. This phase does not mutate either frozen packet or count the result as complete FEI.

Version2 corrects one source-map count: the title-query Atom response contained29 entries;100 was the requested maximum. The mathematical manuscript and control bytes are unchanged from version1. Both versions remain preserved, with their exact manifests and a recorded metadata diff.

## Computational evidence and its limits

Exact integer Walsh transforms, complete truth tables and physical edge comparisons support the explicitly small constructions and finite controls. The final8-variable multiplication obstruction has a pure integer strict entropy comparison. The depth10 true-entropy certificate uses exact rational coefficients and rigorous logarithm enclosures of a proved recurrence; it does not enumerate a1024-variable truth table.

Finite adaptive scans, all4-bit multiplication-pair controls, symmetric-function probes and signed-power/gradient checks use floating entropy rankings. Their finite coverage is recorded in their JSON files. Absence of a counterexample in a finite search supplies no arbitrary-dimensional theorem. The4-bit pair scan uses the entropy cap to prune pairs but does not provide interval certificates for every floating comparison.

The biased-product projection experiment completed4998 initializations and103712 projection updates. It preserves actual complete Boolean witnesses with integer Walsh/Parseval checks, but uses floating sign projection and entropy ranking. It proves neither global infeasibility nor a uniform obstruction. Its large raw evidence stays in the local auxiliary directory, with a compact summary and hash in the repository.

The balanced-gate pair-flip search explores a known O'Donnell–Tan composition direction. It completed900 seconds with44487431 proposed and1485227 accepted updates; the largest retained floating amplification score was6.352536055727036, below the current primary project's stated lower bound6.521845710923046575. Each retained candidate has a full Boolean truth table, exact integer Walsh and physical influence replay. Entropy rankings are floating. It establishes neither an exhaustive optimum, an unbounded family nor a new lower-bound record. The historical printed seed was not used after its literal reconstruction failed a direct balance control; the actual starting seed is independently specified in the script.

No Lean formalization, extension of an existing Lean audit, external submission, push, publication or Release was performed by this role.

## What remains mathematically open here

A finite dimension-independent true conditional-entropy gate, the equivalent minimum-basis estimate, or the stated genuinely linear concentration hypothesis would close the full target. None follows from the auxiliary proxy counterexample, exact product classification, finite gate search or the old multiscale coefficient estimate. The stage therefore ends with the complete original conjecture explicitly unclosed, while preserving the narrower arguments for later review.
