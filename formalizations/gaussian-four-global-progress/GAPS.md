# Remaining proof obligations (not axioms)

This report describes the checked GaussianFour import closure. None of these statements is supplied as an axiom or hidden premise of the sharp theorem. Research-branch infrastructure must be audited and integrated before it counts here.

## Covariance and facets

On H={z in R^4: sum z_i=0}, let C be the PSD trace-one symmetric operators. Construct F(Q) from the actual balanced Gaussian price objective for centered inducing scores with Gram Q. Prove factorization-independence, continuity at singular Q, and required positive-cone smoothness. Identify actual Bochner flux, DF(Q)[K]=(1/2)tr(L(Q)K), the price Hessian, and higher constrained derivatives with manuscript equations (2)-(7) and (16). Facets must be actual Gaussian surface integrals, not arbitrary supplied matrix weights.

## Singular convergence and normal cones

The exact balanced price bound (10), the centered-price norm bound, and subsequential price compactness are now proved in `PriceBounds` and `PriceCompactness`. Convergence of moving-hyperplane Gaussian facet integrals remains unproved. Proven moment separation and triple-tie exclusion do not alone imply facet-integral convergence.

The upper-normal equivalence for arbitrary finite real PSD trace-one matrices, including the sign tr(A(Y-Q))<=0 and full off-diagonal complementarity, is now proved in `NormalCone`. The exact intrinsic three-dimensional regularization residual identity and bound are proved in `RegularizedResidual`. Still required: construct and identify the actual Gaussian covariance derivative on H, transport the centered four-score formulation to these intrinsic matrices, and derive the self-moment rescaling from that analytic construction. An arbitrary matrix satisfying the proved hypotheses is not itself a constructed Gaussian critical point.

## Exact rank-one scope

Newly proved for every d: unit u, strictly increasing a, arbitrary prices p, actual winning masses 1/4, and actual vector self-moment identities imply failure of the explicit adjacent-facet spectral quadratic-form bound. Actual Gaussian projection and Bochner transport are proved.

Missing: extraction of an ordered representation from arbitrary rank-one covariance limits, including sorting/relabeling, and identification of the facet form with the covariance normal-cone matrix. Full singular covariance exclusion is not claimed.

## Rank two and the geometric inputs

For every four distinct centered self-moment inducing vectors of rank two, with actual winning masses 1/4, prove failure of the actual facet inequality L<=P_H. All affine-dependence/hull cases in Lemma 6, including collinear triples and absent interfaces, are required. The strict profile margins (12) are proved, not the planar case analysis.

Required inputs are the actual one-cell Gaussian perimeter bound Per_gamma(A)>=phi(q) at mass 1/4, and the unrestricted three-cell moment bound sum norm(m_i)^2<=9/(8*pi), allowing unequal masses after a merge. An equal-mass three-cell result is not sufficient. This package does not import a conditional perimeter proposition as its proof.

For every four-cell equal-mass finite-perimeter Gaussian partition in dimension d>=3, establish P_gamma(C)>=P_gamma(T), with P_gamma=(1/2)sum_i Per_gamma(C_i) and T the centered tetrahedral cylindrical partition. Include the equality classification. This is the Milman-Neeman geometric input. Its published mathematical proof has not been formalized in this checked closure. No custom axiom is introduced for it or for one-cell isoperimetry.

## Tetrahedron and constrained mountain pass

Prove the exact tetrahedral Gaussian first moments and their squared-norm sum 12*(arctan(sqrt(2)))^2/pi^3, including the analytic angle integral. Prove the actual local Hessian formula (16) and strict local maximality; an algebraic Hessian with prescribed coefficients does not suffice.

Construct the regularized covariance objectives and constrained deformation on the compact positive trace slice. On a compact level band with residual dist(grad F,N_C^+)>0, prove a constraint-preserving continuous deformation that increases F and moves the designated lower superlevel set strictly upward. Existence of its flow, uniform quantitative estimates, and passage to the singular boundary must be proved, not postulated. Assemble Lemma 9's minimax contradiction using the full-rank critical-value lower bound from the actual perimeter theorem.

## Final arbitrary objects and equality

Derive the sharp covariance comparison, then the bound for every measurable four-cell partition of actual mass 1/4 and every measurable fractional partition with labels in [0,1], label sum one almost everywhere, and masses 1/4.

Prove both directions of equality: the labels are almost everywhere indicators of a centered regular tetrahedral winning partition after a permutation and a linear isometric embedding R^3 into R^d, with unrestricted orthogonal-complement coordinates; conversely every such cylindrical partition attains the exact constant. Existing fractional dual equality is not the missing sharp covariance rigidity theorem.

These are mathematical proof obligations, not merely remaining build or publication tasks. The only theorem entry points currently exported are the unconditional partial results listed in ROOTS.txt.
