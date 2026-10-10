# Analytic supplement: actual Gaussian separation and singular limits

This note records the proof used by the new Lean modules. It supplements the
written four-cell argument without modifying its frozen publication files.
It does not claim to complete the full global theorem.

## 1. A direct tent proof of the uniform separation estimate

Let X be the actual standard Gaussian in R^d and u a unit vector. Put Z=<u,X>,
so Z has the actual standard one-dimensional Gaussian law. Let f_i,f_j be
nonnegative fractional labels with f_i+f_j≤1, supported respectively on
Z≥t and Z≤t. Write p_i=E f_i, p_j=E f_j, and m_l=E(X f_l).
Set h_a(z)=max(a-|z-t|,0), a≥0, and c=phi(0).

Pointwise,

    a(f_i+f_j) ≤ f_i(Z-t)-f_j(Z-t)+h_a(Z).

Indeed the signed term is (f_i+f_j)|Z-t|; if |Z-t|≥a the claim is immediate,
and otherwise the deficit is at most a-|Z-t| since f_i+f_j≤1.
The exact Lebesgue area of the tent is a². Because the standard Gaussian
density is everywhere at most c,

    E h_a(Z) ≤ c a².

All functions are integrable: labels are bounded, Gaussian coordinates are
integrable, and h_a is bounded (and compactly supported on the line).
Integrating, with q=p_i+p_j, gives

    <u,m_i-m_j> - t(p_i-p_j) ≥ aq - ca².

Choose a=q/(2c), justified by q≥0 and c>0. Then

    <u,m_i-m_j> - t(p_i-p_j) ≥ (p_i+p_j)²/(4c).

For equal masses p, the offset cancels and the lower bound is p²/c. For four
balanced winning cells, p=1/4, u=(v_i-v_j)/||v_i-v_j|| and
 t=(λ_i-λ_j)/||v_i-v_j||. The defining strict score inequalities give the
required support conditions; pairwise score ties are Gaussian-null. Hence

    <u,m_i-m_j> ≥ 1/(16 phi(0)) = sqrt(2π)/16.

Cauchy–Schwarz yields the same lower bound on ||m_i-m_j||. The argument uses
no optimality, Gaussian isoperimetry, perimeter theorem or synthetic moment
model. It is formalized in `GaussianTent` and `GaussianMomentSeparation`.

## 2. Actual winning-set integrals through rank loss

Suppose v_i^n→v_i and λ_i^n→λ_i, with the limiting v_i pairwise distinct.
At any point x outside the finite union of limiting tie hyperplanes, the
unique strict winner has finitely many positive score gaps. All those gaps
remain positive for sufficiently large n. Consequently every winning-cell
indicator is eventually equal to its limiting indicator at that x.

For any integrable Banach-valued g, the integrands
1_{C_i^n}(x) g(x) are dominated in norm by ||g(x)||. Dominated convergence
therefore proves convergence of the actual Bochner set integrals. Taking
g=1 gives masses and g(x)=x gives first moments. No full-rank assumption
is used. `GaussianWinningLimits` proves this stronger integrable-function
statement, not just coordinate-by-coordinate convergence.

This is not facet-area convergence: facets lie in moving lower-dimensional
planes, so their surface measure needs a separate argument (gap G3).

## 3. Noncollision from actual residuals

Suppose balanced diagrams have actual moment residuals
m_i^n-μ_n v_i^n→0, with v_i^n→v_i and μ_n→μ. Then m_i^n→μv_i, without any
preliminary assumption that the limiting scores are distinct. Uniform
separation and norm continuity imply

    sqrt(2π)/16 ≤ |μ| ||v_i-v_j||, i≠j.

Thus no scores collide, and μ≠0. If μ≥0, it follows that μ>0. With prices
also converging, Section 2 identifies the limiting actual moments as μv_i
and the limiting masses as exactly one quarter. Scaling scores and prices
simultaneously by μ does not change any strict winning cell. The rescaled
diagram is therefore actually self-induced by its own Bochner moments.

`GaussianBoundaryTransfer` proves these conclusions. It does not assert
that a covariance mountain-pass sequence has the required residuals: their
production is gap G8.

## 4. Actual value continuity, Gram invariance and reduction

Define V(v) as the infimum over prices of the actual expected maximum plus
the mean price. A minimizer exists even with coincident scores. The pointwise
score perturbation bound is uniform in prices:

    |max_i(<v_i,x>-λ_i)-max_i(<w_i,x>-λ_i)| ≤ ||v-w||_∞ ||x||.

After integration and comparison at actual minimizers,

    |V(v)-V(w)| ≤ ||v-w||_∞ E||X||.

Positive homogeneity includes the zero scale. Equality of two Gram matrices
implies equality of every scalar projection variance of their actual
Gaussian score vectors; characteristic-function uniqueness gives equality
of their full score laws. Thus V depends only on the Gram matrix, including
singular matrices and score lists in different dimensions.

For an actual balanced fractional partition with energy E=Σ||m_i||²>0,
put v_i=m_i/sqrt(E). Actual Gaussian zero mean implies Σv_i=0 and direct
algebra gives Σ||v_i||²=1. The actual primal/dual inequality gives

    sqrt(E)=Σ<v_i,m_i>≤V(v).

The set-partition adapter takes the original measurable indicator functions;
its masses and Bochner moments are exactly the original set integrals, and
it allows null overlaps and null uncovered sets. Therefore the same reduction
holds for the original theorem's objects. The missing step is the global
sharp bound and unique-optimizer theorem for V, not the measure-theoretic
meaning of its inputs.
