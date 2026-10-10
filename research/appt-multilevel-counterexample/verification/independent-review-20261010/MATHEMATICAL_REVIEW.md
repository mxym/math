# Independent-pass mathematical review and formal coverage ledger

Baseline: `4248c2b2d4cad94d4269def3158b414352e1a40b`.
This is a fresh verification pass over the working arguments, not external peer review.
It is not blanket approval or complete Lean certification of every earlier research result.
No new conjecture exploration or preprint preparation is included in this pass.

## Definitions and the physical core

The source APPT definition is retained literally from
`formalizations/appt-qutrit-purity/APPT/Quantum/Basic.lean`: it quantifies over
all complex global unitary matrices and asserts positive semidefiniteness of
their partially transposed conjugates. Density means PSD and actual matrix trace
one; purity is the real part of the matrix trace square. No necessary spectral
inequality replaces this hypothesis in the new physical Lean roots.

The notes transpose the second factor, while that library transposes the first.
For every matrix, these outputs are full transposes of each other. Ordinary
transpose preserves complex Hermitian positive semidefiniteness. The new
`absolutelyPPT_right_iff` proves the convention equivalence rather than assuming it.

The pairwise Hadamard construction is defined on every finite ordered square
corner, not just a qutrit corner. It is extended by identity to a rectangular
system. Conjugation of a diagonal matrix gives the real witness with diagonal
`2*d(i,i)` and off-diagonal `d(i,j)-d(j,i)` for i<j. Its PSD follows by taking
an actual principal submatrix of an actual APPT partial transpose. Arbitrary
permutations are implemented by unitary permutation matrices. The actual
Hermitian eigenvalue diagonal inherits APPT by spectral unitary conjugation.
This is the intended route for the first major formal checkpoint.

## Mathematical steps rederived in this pass

1. The all-unitary counterexample argument really is sufficient: for every
   Schmidt witness W and every projection Q, `Tr(QW)` is bounded below by the
   sum of all negative eigenvalues, and the vector term is bounded below by
   `-s1*s2`. The dimension-uniform SOS then gives positivity. Nesting the vector
   inside the projection is used for its spectrum, not for that lower estimate.
   The exact trace/purity calculations and both strict rational gaps were rerun.
   A complete Lean Schmidt-decomposition/projection-trace sufficiency bridge
   remains an obligation; the scalar SOS alone does not discharge it.
2. The unrestricted upper argument uses different valid unitaries for different
   edge rearrangements of the SAME eigenvalue list. Top R, bottom R, and the
   next m bottom slots are disjoint because m^2<=mn. The triangular row estimate
   and the complete-background cross term were independently expanded. The
   centered-variance normalization does not assume a flat spectrum. The sorted
   slot-assignment existence and row-by-row combinatorics still need Lean proofs.
3. The entropy star must use the least eigenvalue on the central diagonal and
   shift the positive-edge slots by one. Its leaf/center slots consume 2m-1 of
   the S=m(m+1)/2 bottom slots; the remaining S-(2m-1)=R-(m-1) slots match the
   remaining edges. This verifies disjointness and retains the factor 1-beta1.
   Replacing this by the older four-unit bound would lose the nonlinear control.
4. The nonlinear entropy-head argument uses f(-y)/y^2<=1/(2-y), a positive
   quartic certificate, and the modified star. Its endpoint cases y=0 and y=1
   are distinct and valid. Tail Taylor estimates are applied only after a
   uniform small-contrast bound; the pivot correction `D*f(t-1)` is retained.
   This pass does not label the logarithmic inequalities or their sum as already
   Lean-proved merely because the polynomial certificate compiles.
5. The graph lower constructions require one common amplitude measure across
   finitely many scales, summable edge weights for countable forests, and nested
   lower flags for quantum necessity. Positive slack is inserted before the
   dimension limit; the level count is increased only afterwards. These were
   checked as essential hypotheses. Their compactness/forest proofs and the
   diagonal-selection theorem remain outside the current formal checkpoint.
6. The exact rectangular formula is claimed only for n>=m^3-m-2. The early branch
   of its outer-polytope relaxation is not APPT and cannot certify a maximum.
   The integer rank uses the strictly better ceiling in the odd-parity case.
   The exact checker was replayed, but convex-hull and all-vertex optimization
   have not yet been translated into Lean.

No contradiction was found in these rederived steps. That does not close the
remaining mathematical or formal checks for the full asymptotic, rigidity,
exact-maximum, or Renyi theorems.

## Main-result / lemma / Lean correspondence

| Working result | Essential bridge or lemma | Current formal boundary |
|---|---|---|
| Multilevel counterexample | General Schmidt spectrum, projection trace lower bounds, SOS, trace normalization | SOS and rational comparisons targeted; full physical sufficiency not yet closed |
| Unrestricted purity upper bound | All-permutation actual eigenvalue witness, edge rearrangements, variance inequality | Physical witness and star targeted; sorted combinatorics and final moment bound remain |
| Sharp purity lower bound | Uniform multiscale graph bound, nested flags, positive margin, limits | Written review only; no Lean claim |
| Exact rectangular maximum and equality | Outer-polytope vertex classification, exact parity comparison, physical attainment | Written review plus exact checker replay; no end-to-end Lean claim |
| Phase/outlier rigidity | Retained defects, PSD Cauchy-Schwarz, limiting spectral measures | Physical PSD ingredients targeted; limiting rigidity remains |
| Entropy/Renyi minima | Modified physical star, nonlinear head, tail estimates, uniform limits | Modified PSD star and quartic targeted; logarithms and final optimization remain |
| Two-ended flat construction | Common graph limit, two-sided PT control, centering, limit order | Written review only; no Lean claim |

The current physical roots concern arbitrary finite dimensions and actual
matrices. Their hypotheses still explicitly describe the selected diagonal
slots; a separate combinatorial permutation lemma is needed to instantiate
them with the fully sorted least-eigenvalue assignment in the notes.

The companion collective-negativity, state-aware extraction and universal-Schur
papers have NOT received a complete new review in this checkpoint. Their old
ancillary checks or the qutrit Lean certificate do not certify these later claims.

## Execution evidence and audit policy

`ANCILLARY_REPLAY.json` and the sixteen literal logs record all eight existing
checkers run normally and with Python assertions disabled. Outputs agree in each
pair. This is a fresh execution of old algorithms, not independent verification
of unbounded mathematical assertions. The first local Lean import exhausted the
resource-limited VPS path; the failed attempt is retained as a timeout. Subsequent
CI elaboration failures are retained and repaired, not converted to proof success.

The Lean acceptance gate is a complete build of each selected root followed by a
transitive declaration replay from `mkEmptyEnvironment 0`, an axiom allow-list of
`propext`, `Classical.choice`, and `Quot.sound`, and deliberate proof corruption
with the original theorem type left unchanged. No main-result completion is
announced before its own full mathematical dependency chain crosses this gate.
