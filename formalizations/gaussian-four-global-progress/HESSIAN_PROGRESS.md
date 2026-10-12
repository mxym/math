# Actual Gaussian price Hessian and centered nondegeneracy

**Unconditional partial formalization. Not the global sharp theorem.**

For affine-independent inducing scores v_0,...,v_(k-1) in R^(k-1), arbitrary
prices b and target mass vector p, write

  J(b) = integral max_i(<v_i,x>-b_i) d gamma + sum_i p_i b_i.

The imported quantities are the actual Gaussian measure, winning sets, masses
and Bochner moments. The repaired development establishes genuine Frechet
rather than merely directional differentiability:

  DJ(b)[q] = sum_i (p_i - gamma(C_i(b))) q_i,
  D(DJ)(b) = L(b),
  q^T L(b) q = (1/2) sum_(i,j) w_ij (q_i-q_j)^2.

One and the same constructed positive symmetric Gaussian flux family w
supplies the Bochner flux, the mass derivative and the price Hessian. Its
weights are not arbitrary external assumptions in the actual-Gaussian entry
point `actual_simplicial_price_hessian`.

The new `CenteredPriceHessian.lean` fixes the additive gauge by the actual
submodule H={q : sum_i q_i=0}. It proves that L maps H to H, that q^T L q>0
for every nonzero q in H, and that the resulting linear endomorphism is
bijective. The proof derives injectivity from the proved exact constant
kernel, then uses finite-dimensional injective/surjective equivalence.

The combined entry point

  GaussianFour.actual_simplicial_price_hessian_nondegenerate

constructs w and provides the actual second Frechet derivative, actual
Bochner flux and centered bijectivity together. Four cells correspond to its
parameter d=2, hence four inducing scores in the intrinsic R^3. This does not
silently claim the same result at degenerate score families.

This removes a nondegeneracy obligation needed for the balancing-price
implicit-function route. It does **not** yet prove continuity of that
Hessian in joint score/price parameters, the smooth implicit price map,
the covariance Hessian, or the constrained deformation theorem. Those and
the geometric perimeter inputs are listed explicitly in GAPS.md.

## Repair provenance

The prior Fréchet source checkpoint did not compile. The failed CI logs
identify real norm/absolute-value mismatch, a continuity/tendsto tactic
mismatch, reversed winning-score arguments, unresolved NNReal Lipschitz
constants, and a composition that was not unfolded before reindexing.
`PriceSecondVariation` additionally needed identity-function normalization
and an explicit zero-score path identity. The repair retains the same
mathematical statements and their actual Gaussian definitions.

After individual checks, the entire 89-module repaired package passed
independent clean CI (run 38064502958). The new centered module is added to
all module, source-hash, audit and replay inventories; its reversed strict
curvature inequality is an additional deliberate Lean rejection test.
Current full-package receipts are indexed in README.md and CI_REPAIR.md.

Author: Yongxian Zhang (张永贤), School of Computer Science and Engineering,
South China University of Technology. Email: mxymmxym1@gmail.com.
ORCID: 0009-0000-3864-3536. No external funding. AI-assisted research.
Existing licenses and third-party notices are preserved; original additions
retain all rights not otherwise granted. No external peer-review claim.
