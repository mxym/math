# Research selection and progress — 10 October 2026

## Publication checkpoint

The preceding qutrit task was already complete when this continuation began.
The following were inspected live, not inferred from an old progress message:

- Immutable proof release `appt-qutrit-purity-complete-v1`, publication commit
  `2fc3f25179cf1128c4bccbde65fd3a07c093ad6d`.
- Immutable manuscript release `appt-qutrit-purity-preprint-v1`, publication
  commit `773ea1615c3a99a248720be6385b8ec8ad7f640a`.
- Published Zenodo preprint DOI `10.5281/zenodo.23269470`, classified as a
  preprint, dated 9 October 2026. The metadata-corrected DOI version preserves
  the same paper and source archive bytes. The manuscript has no arXiv ID and
  is not represented as peer reviewed.

Repository `main` was initially checked at `c8cc0a8`; its README, SOLVED_PROBLEMS
and RESEARCH indexes were read. Main was checked again before publication to
preserve concurrent work. No tracked or applicable parent AGENTS.md was found.
The previously active spin-alignment worktree contained no independent result
on that problem, and was not changed. Published proof and manuscript sources
were not changed by this continuation.

## Candidate screening

### Absolute PPT versus absolute separability

This remains a major spectral entanglement question for both local dimensions
at least three. A direct entangled-APPT search using standard witnesses would
need to overcome existing limitations: Arunachalam, Johnston and Russo,
*Is absolute separability determined by the partial transpose?*,
arXiv:1405.5853, show that several familiar entanglement criteria do not detect
entanglement within APPT. Merely retrying those criteria was not selected as the
main task. A later deduction below does settle containment of a specified inner
polytope in AS; it does not settle APPT=AS.

Source: https://arxiv.org/abs/1405.5853

### Compatible-marginal spin alignment

The unrestricted strong majorization conjecture was already disproved by
Song and Chen, arXiv:2603.25410v1; it is not a new open target. Their **Conjecture
2** requires every subsystem state to be a marginal of one common global
state and remains a different question. The original entropy minimization
conjecture is also distinct from the false unrestricted majorization statement.

We tested the compatible problem with graph-state distributions and alternating
pure-state/Ky-Fan/mixture optimization. Historical raw reports are retained in
`discovery/`; all optimizer outputs are discovery-only. There were 1,280, 2,000,
and 1,638 graph-state LP chains for 4, 5, and 6 qubits respectively, and 1,000
and 588 general pure-state trials for 3 and 4 qubits. The largest reported
positive discrepancy in the latter was about 2e-15, not a counterexample.
The attempted three-qutrit run did not complete and is not included as a result.

This was not a systematic exhaustion. Wall-time-limited searches are not exactly
reproducible in trial count, and no nontrivial positive theorem resulted from
them. We stopped expanding that numerical search after it supplied neither a
candidate exact witness nor a structural lemma. It is parked, not declared
solved or refuted.

Sources: https://arxiv.org/html/2603.25410v1 (Conjecture 2);
https://arxiv.org/abs/2307.06894 (original stronger formulations and special cases).

### Arbitrary-dimension APPT maximal purity — selected

Ahiable--Kothakonda--Winter Conjecture 6.7, arXiv:2608.03390v1, predicts the
exact maximum over all dimensions. The completed project resolves its qutrit
maximal-value/attainment instance; the unrestricted higher-local-dimension
question is not supplied by that Lean release.

This target was selected because it concerns a complete dimension-uniform
extremal law, has direct spectral/physical meaning, and now admits provable
structural progress rather than just improved numerical values. The aim remains
the full conjecture or a rigorously certified counterexample.

## Results obtained in this cycle

**Theorem A** closes the entire two-eigenvalue class for every `3<=m<=n`, with
all multiplicities and both exact candidate spectra. The important step is a
three-regime argument: sparse negative-subspace tests for few high eigenvalues;
a sharp contrast constraint and integer rank optimization in the middle;
and complementary positive-subspace tests plus an explicit positive polynomial
for the large high-eigenvalue multiplicities. The `D=9,l=2` exception is checked
by a nonuniform Schmidt vector, not discarded.

**Theorem B** also treats a genuine multi-level class: all APPT spectra with
smallest-eigenvalue multiplicity at least `D-m+1`. A weighted-star Schmidt test
bounds the squared Euclidean length of all exceptional eigenvalue contrasts.
This gives the sharp rank-one-spike purity without assuming two levels.

**Theorem C** proves the whole inscribed Gershgorin polytope is absolutely
separable. This answers the specified containment question discussed in
Section 7 of the source paper, by combining its vertex structure with existing
separability criteria. It is identified as a deduction from existing inputs,
not a new prediction of their criteria or a proof of APPT=AS.

The candidate value in Theorem A was already conjectured in the source paper;
no first-prediction or exhaustive novelty claim is made here.

## Failed relaxation and next mathematical obstruction

A vertex search in the relaxation defined only by maximally entangled test
vectors found `(3,2,1,...,1)/(D+3)`. We then discarded numerical feasibility
as proof and derived exact certificates: it satisfies every equal-Schmidt-rank
linear inequality but has a negative physical partial-transpose quadratic form.
In dimension 16 it even exceeds the conjectured maximum in that relaxation.
This rules out closing the conjecture by that relaxation alone.

The remaining core target is an inequality for genuinely multi-level spectra
outside Theorem B, starting with local dimension four. We have not proved
that all APPT spectra are convex combinations of two-level APPT spectra;
assuming that would make an invalid proof. The next serious attempt must
produce either a physical-test-supported multi-level inequality or a candidate
that survives an exact all-unitary APPT criterion and exact purity comparison.

## Reassessment rules

A direction is retained for concrete mathematical progress: a proved reduction,
a falsifiable structural mechanism, an exact certificate, or a candidate with
an independently checkable verification route. More random restarts alone do
not qualify. If the multi-level attempt yields only the same two-level witnesses
or relaxations already refuted above, its approach must change; simply enlarging
the parameter sweep is not the research objective. Independent alternatives
include the compatible-marginal conjecture, but only with a new argument rather
than repetition of this cycle's inconclusive search.

All new theorems in this directory are written analytic proofs, not Lean
formalizations. The symbolic checks and regression counts are explicitly
auxiliary. No partial result here is labeled as a complete higher-dimensional
APPT purity solution or issued as a complete-proof Release.
