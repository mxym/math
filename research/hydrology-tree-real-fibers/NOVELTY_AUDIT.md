# Novelty and scope audit — 2026-10-12

This audit separates proved mathematics from historical-priority assertions.
The new formalization is not, by itself, evidence that the mathematics first
appeared here. No broad positive-realization problem is claimed solved.

## Relevant primary literature actually checked

**C. Cobelli, A. Lepschy and G. Romanin Jacur (1979), “Identifiability results
on some constrained compartmental systems,” Mathematical Biosciences 47(3–4),
173–195. DOI: `10.1016/0025-5564(79)90036-1`.** The publisher abstract and the
University of Padua's author repository record explicitly report identifiability
and evaluated solution counts for tree-type and radial models. This is direct
prior art for any claim that tree realization enumeration itself is new. The
repository record supplies no associated full-text file; this check did not
obtain the complete article. Exact assumptions, positivity scope and equality
with our all-real/full-response theorem therefore remain to be compared, rather
than inferred from the abstract.

**“Identifiability of linear compartmental models: The singular locus” (2022),
Advances in Applied Mathematics 133, 102268. DOI: `10.1016/j.aam.2021.102268`.**
The publisher abstract distinguishes generic Jacobian rank, its singular locus,
and generic identifiability degree. It treats cycle/star singular-locus formulas
and states a catenary conjecture. Consequently, a proof of an exact all-rate
Jacobian polynomial is a different statement from re-proving generic local
identifiability, and a full positive-target fiber count is not automatically
identical to a generic complex degree claim.

**“Identifiability of Directed-Cycle and Catenary Linear Compartmental Models”
(2026), SIAM Journal on Applied Dynamical Systems, publisher full-text HTML.**
Its concluding discussion treats the prior catenary singular-locus conjecture
as a future target. This supports the relevance of the separately formalized
Jacobian work, but does not settle priority for the new fiber classification,
nor rule out later or independently circulated results.

The additional publisher record for **“Identifiability of linear compartmental
tree models and a general formula for input-output equations” (2023)** also
cites the 1979 work. Existing tree-identifiability literature must therefore be
compared at the theorem level before any novelty assertion.

## Defensible current assertions

The code proves the displayed theorems for their exact actual objects and
quantifiers. The positive count has an exhaustive actual-parameter bijection;
the all-real strengthening derives every rate's positivity; the discharge
bridge derives the unknown root leak. Every result is tied to source-specific
Lean verification, rather than a generic numerical solver or finite examples.

The current novel-contribution candidates are the explicit combination of the
all-rate Jacobian and multiplicity proof, exhaustive non-generic full-positive
response fibers, automatic admissibility of unrestricted real competitors, and
complete kernel-checkable construction. None of these candidates is labelled
historically first merely because this search did not find an exact match.

No claim is made for arbitrary positive transfer functions, arbitrary directed
networks, complex parameter fibers, fewer-mode targets, nonlinear hydrological
systems, or superior catchment forecasts. Formal verification is not an external
human peer review or empirical validation.

## Sources and search record

Primary records retrieved through web search on 2026-10-12:
- Publisher record for PII `0025556479900361` and University of Padua record
  `https://research.unipd.it/handle/11577/2509174`.
- Publisher record for PII `S0196885821001068`.
- SIAM publisher full-text record `https://epubs.siam.org/eprint/IXIEMIECP3TISXXACWXU/full`.
- Publisher records for PII `S0196885823000088`.

Queries included tree compartmental model realization counts, Stieltjes tree
realizations, positivity of all real solutions, and the catenary singular-locus
conjecture. Lack of a retrieved exact match is not a proof of novelty.
