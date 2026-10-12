# Mathematical audit and verification scope

Original six-page manuscript SHA-256:
`8416f741398ceb4207edcc3ff31964883ae14044698043bf17a75d66c1dec832`.

Expanded seven-page manuscript SHA-256:
`e1528f549be95d495dd03f2e97890bb4c83cd7501dc60dee8c885ecb2edb562a`.

The [new derivation review](review/INDEPENDENT_MATHEMATICAL_REVIEW.md)
and [revision provenance](review/REVISION_PROVENANCE.json) document the
expanded price Hessian, covariance derivative and theorem application.
The archived reviews below bind only the original six-page version.

## Complete proof chain

1. Define the balanced score dual on every centered positive-semidefinite
   covariance, including duplicate rows and rank-deficient endpoints.
   A square-root Gaussian coupling proves continuity uniformly over
   prices. Scaling proves half-degree homogeneity.
2. On covariances positive on the centered label space, invertible score
   differences yield fixed polyhedral integration regions. Price
   coercivity, null ties and a strictly positive facet Laplacian justify
   attainment, uniqueness and smooth balancing prices. Dominated
   Gaussian differentiation and the implicit function theorem justify
   the derivative, with no assumption at a singular endpoint.
3. Gaussian flux gives `B=LM`, `C=tr(LQ)`, and `dC[D]=tr(LD)/2`.
   Every pairwise facet has positive area in the full-rank regime.
4. The imported Milman–Neeman perimeter theorem is applied only with
   `k=n+1` and `n=k-1`. Its total perimeter is half the sum of individual
   perimeters. Equal masses identify the central regular fan.
5. Its lower bound and weighted Cauchy give `C tr(L)/n >= c_k^2`.
   Along `Q_t=P/n+t(Q-P/n)`, this yields `t h' <= h` for
   `h=C(Q_t)^2-c_k^2`. The initial derivative is zero by symmetry and
   the trace constraint. Thus `h/t` decreases from zero. Closed-cone
   continuity supplies the endpoint, including singular covariances.
6. Equality forces the quotient identically zero. Positivity of all
   weights makes equality in weighted Cauchy force equal score distances,
   hence the centered trace-one regular Gram matrix. Integrating the
   exact quotient derivative gives the nonnegative deficit identity;
   endpoint limits establish convergence of the improper integral.
7. Actual partition moments provide a feasible dual assignment even
   for fractional labels. Homogeneity gives the stated squared-moment
   bound. Equality fixes the regular moment Gram and unique winning
   indicators. Rank excludes equality below dimension `k-1`.

The written proof covers every integer `k>=2`, all ambient dimensions,
zero moment value, fractional labels, singular covariance endpoints,
null ties, cylindrical attainment, and all equality cases. The `k=2`
covariance domain is a singleton; `k=1` is separately trivial.

## Imported results and originality

The non-elementary geometric input is the published Gaussian
multi-bubble perimeter theorem; this project does not claim that theorem
as its own. Ordinary Gaussian integration by parts, matrix square-root
smoothness, dominated convergence, the implicit function theorem and
one-variable calculus are also used explicitly. Full covariance
concavity is neither assumed nor claimed. The comparison and deficit
are the argument presented here, with the sources and historical
conjectures compared in `LITERATURE_STATUS.md`.

## What has actually been checked

Both archived model reviews read the original complete manuscript with
the original six-page hash above and checked the full analytic chain and source conventions. They
are internal reviews, not independent human peer review.

`Algebra.lean` proves general finite weighted Cauchy and three scalar
implications. `RadialComparison.lean` proves the abstract real differential
comparison and three helper results with explicit hypotheses. Official
Lean 4.34.1 recompiled fresh sources and replayed all 18,013 declarations
used by these eight exports in an initially empty kernel at trust level
zero. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted.
The deliberate false variant omitting the initial zero-derivative
condition fails compilation; the rational model `h(t)=t` shows why.

Gaussian measure, covariance continuity/differentiability, price
regularity, flux, the multi-bubble theorem and satisfaction of the
abstract differential hypotheses have **not** been formalized here.
They are mathematical claims proved or cited in the paper. This scope
statement concerns the preserved eight-export package. The
[separate 136-module Lean development](https://github.com/mxym/math/pull/3)
covers substantial Gaussian analysis with its geometric perimeter
premise explicit. Neither package certifies the unconditional complete
Gaussian endpoint in Lean.

`check_exact.py` performs finite rational sanity controls and identifies
countermodels to weakened scalar claims. No finite computation is a
premise of the Gaussian theorem. `verify.py` checks the file set, hashes,
recorded sources/logs, diagnostic replay and PDF text; it is an integrity
verifier, not a checker for the written analytic proof.
