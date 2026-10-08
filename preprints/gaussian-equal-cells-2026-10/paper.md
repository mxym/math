---
title: "Equal Gaussian cells: the sharp simplex first-moment theorem"
author: "Yongxian Zhang"
date: "8 October 2026"
geometry: margin=25mm
fontsize: 11pt
header-includes:
  - \usepackage{amssymb,amsmath}
---

# Abstract

For every number of cells $k\ge2$, we determine the sharp squared
first-moment sum for equal-probability Gaussian partitions when the
ambient dimension is at least $k-1$. The unique maximizers are central
regular simplex cones, and the value is
$(\mathbb E\max_{i\le k}Z_i)^2/(k-1)$ for independent standard normals.
The bound also holds in lower dimensions and for fractional partitions.
We prove a covariance comparison by combining Gaussian flux with the
established Gaussian multi-bubble perimeter theorem. A weighted Cauchy
inequality yields a first-order differential inequality along each path
from the regular covariance; its initial derivative vanishes by symmetry.
This gives the global bound and equality classification, with an exact
nonnegative integral expression for the deficit. No numerical search, variation of arbitrary competing cell boundaries,
local simplex Hessian or mountain-pass argument is needed.
We distinguish the imported perimeter theorem and partial formal checks
from the new analytic comparison.

# 1. Statement and prior conjecture

Let $\gamma_d$ be standard Gaussian probability on $\mathbb R^d$.
For a measurable partition $C_1,\ldots,C_k$ define
$m_i=\int_{C_i}x\,d\gamma_d$ and $F=\sum_i|m_i|^2$.
Write $Z_1,\ldots,Z_k$ for independent standard normals and

$$
 a_k=\mathbb E\max_{i\le k}Z_i,
 \qquad c_k=\frac{a_k}{\sqrt{k-1}},\qquad F_k=c_k^2.
$$

These constants are exact; for example integration by parts gives

$$
 a_k=k(k-1)\int_{\mathbb R}\phi(x)^2\Phi(x)^{k-2}\,dx>0,       \tag{1}
$$

where $\phi,\Phi$ are the standard normal density and distribution.

**Theorem 1.** For every integer $k\ge2$, every integer $d\ge1$, and
every Gaussian partition with $\gamma_d(C_i)=1/k$,

$$
 \sum_{i=1}^k\left|\int_{C_i}x\,d\gamma_d(x)\right|^2
             \le\frac{a_k^2}{k-1}.                         \tag{2}
$$

If $d\ge k-1$, equality holds precisely for the central regular simplex
winning partition in a $(k-1)$-dimensional subspace, with the orthogonal
complement unrestricted, up to null sets, orthogonal transformations and
relabeling. If $d<k-1$, the inequality is strict for every partition;
we do not claim this is the sharp bound at a fixed such lower dimension.

The identical statement holds for fractional partitions:
$0\le f_i\le1$, $\sum_i f_i=1$ almost everywhere, and
$\int f_i\,d\gamma_d=1/k$, using $m_i=\int xf_i\,d\gamma_d$.
The functions $f_i$ are measurable. Equality forces the same ordinary
winning indicators.

This settles the equal-mass subcase for every number of cells of the
first-moment conjecture in [H19, Problem 1.15 and Conjecture 1.16], and
in particular the four-cell dimension-three question [H14, Conjecture 3].
It is not the positive-correlation noise-stability conjecture or the
arbitrary prescribed-mass statement. The latter is false as written
[EX]. Our [literature status](LITERATURE_STATUS.md) reports the precise
sources checked and makes no worldwide first-proof claim.

# 2. The balanced covariance value function

Put $\mathbf1=(1,\ldots,1)^T\in\mathbb R^k$,
$P=I-\mathbf1\mathbf1^T/k$, $n=k-1$,

$$
 \mathcal K=\{Q=Q^T\succeq0:Q\mathbf1=0,\ \operatorname{tr}Q=1\},
 \qquad Q_*=P/n.
$$

For every positive semidefinite $Q$ annihilating $\mathbf1$, define

$$
 \mathcal C(Q)=\inf_{\lambda\in\mathbb R^k}
 \left\{\frac1k\sum_i\lambda_i+
               \mathbb E\max_i(Y_i-\lambda_i)\right\},
 \qquad Y\sim N(0,Q).                                      \tag{3}
$$

For a centered $k\times n$ score matrix $M$ with $MM^T=Q$, this is
called the balanced score value. For distinct rows it equals the optimal
assignment value, as proved below. Prices attain their infimum:
in the gauge $\min\lambda_i=0$, the expression is at least
$\max\lambda_i/k$ by using a zero-priced mean-zero score. This closed
gauge therefore has bounded sublevel sets, and the objective is continuous.
The maximum also bounds the average, so the objective is nonnegative.
A compactness argument gives a minimum; common price shifts let us place
it in the smooth gauge $\sum_i\lambda_i=0$. For distinct
scores $v_i$, differentiating in prices gives
$1/k-\gamma_n(C_i)$, where

$$
 C_i=\{x:v_i\cdot x-\lambda_i\ge v_j\cdot x-\lambda_j\ \forall j\}.
                                                               \tag{4}
$$

Ties are Gaussian-null. Minimizing prices therefore give all masses
$1/k$; the winning labels attain the linear assignment pointwise.

Two elementary facts include the singular covariance boundary:

$$
 \mathcal C(sQ)=\sqrt{s}\,\mathcal C(Q)\ (s\ge0),
 \qquad \mathcal C\text{ is continuous on the closed cone}.       \tag{5}
$$

For homogeneity scale scores and prices, and note $\mathcal C(0)=0$.
For continuity couple $Q^{1/2}G$ and $\widetilde Q^{1/2}G$ on the
same standard Gaussian space. The difference of the maxima, for any
price, is at most $|(Q^{1/2}-\widetilde Q^{1/2})G|$. Its expectation
bounds the difference of the two infima, uniformly in prices; the
matrix square root is continuous.

We use differentiability only where $Q$ is positive definite on
$\mathbf1^\perp$. There the $k$ scores are affinely independent in
$\mathbb R^n$. Every pair of winning cells has a positive Gaussian
facet area: the nonsingular score-difference coordinates allow any
chosen pair to tie at the top while all other scores are strictly lower.
For the ordinary $ij$ facet put

$$
 \ell_{ij}=|v_i-v_j|,
 \quad A_{ij}=\int_{\Sigma_{ij}}\varphi_n\,d\mathcal H^{n-1},
 \quad w_{ij}=A_{ij}/\ell_{ij},
 \quad (Lu)_i=\sum_{j\ne i}w_{ij}(u_i-u_j).               \tag{6}
$$

Let $B$ have rows $b_i=\int_{C_i}x\,d\gamma_n$.
Gaussian integration by parts gives

$$
 B=LM,\quad \mathcal C(Q)=\langle M,B\rangle
      =\operatorname{tr}(LQ)=\sum_{i<j}w_{ij}\ell_{ij}^2,
 \quad \operatorname{tr}L=2\sum_{i<j}w_{ij}.             \tag{7}
$$

The inward $ij$ normal of cell $i$ is $(v_i-v_j)/\ell_{ij}$.
To justify flux on unbounded cells truncate with large balls; their
additional Gaussian boundary term tends to zero exponentially.
The price term in (3) cancels because all winning masses are $1/k$.

**Lemma 2 (smooth derivative).** On this positive cone $\mathcal C$ is
smooth, and for every symmetric $D$ annihilating $\mathbf1$,

$$
 d\mathcal C(Q)[D]=\tfrac12\operatorname{tr}(LD).         \tag{8}
$$

*Proof.* Let $T$ have rows $v_i-v_k$, $i<k$, and put
$a_i=\lambda_i-\lambda_k$. The map $T:\mathbb R^n\to\mathbb R^n$
is invertible. With $s=TX-a$, its Gaussian covariance is $TT^T>0$
and its mean is $-a$. If $p_{\Sigma,\mu}$ denotes that ordinary
$n$-dimensional Gaussian density, the objective equals

$$
 J(M,\lambda)=\frac1k\sum_i\lambda_i-\lambda_k+
 \int_{\mathbb R^n}\max(0,s_1,\ldots,s_n)
                      p_{TT^T,-a}(s)\,ds.                 \tag{8a}
$$

The winner regions in $s$ are fixed polyhedral cones. On a compact
neighborhood of a full-rank score and finite price, covariance
eigenvalues stay bounded away from zero and infinity and the mean
stays bounded. Each parameter derivative of the density is bounded
by $C(1+|s|)^r e^{-c|s|^2}$ for constants $C,c>0$ and a finite $r$
depending on the derivative order. The maximum has at most linear
growth. Differentiation under the integral therefore proves smoothness
of the objective and all winning probabilities.

For a fixed cell $i$, use the invertible coordinates
$z_j=(v_i-v_j)\cdot X$, $j\ne i$. Its probability is a Gaussian
orthant integral with lower thresholds $\lambda_i-\lambda_j$.
Differentiating one threshold gives the negative face integral;
the coarea formula for the scalar coordinate $(v_i-v_j)\cdot X$
converts that integral to $-A_{ij}/\ell_{ij}=-w_{ij}$. Thus

$$
 \partial_{\lambda_i}\gamma_n(C_i)=-\sum_{j\ne i}w_{ij},
 \qquad
 \partial_{\lambda_j}\gamma_n(C_i)=w_{ij}\quad(j\ne i).
                                                               \tag{8b}
$$

Since the objective's price gradient is $1/k-\gamma_n(C_i)$,
its price Hessian is exactly $L$. Every weight is positive at every
finite price. For any nonzero $u$ with $\sum_i u_i=0$,

$$
 u^TLu=\sum_{i<j}w_{ij}(u_i-u_j)^2>0.
$$

This gives strict convexity on the price gauge along every nonconstant
segment, hence uniqueness of its minimizing price. The gauge gradient
maps $\mathbf1^\perp$ to itself, and its Jacobian $L$ is invertible
there. The implicit function theorem makes balancing prices smooth
in the full-rank scores. A smooth positive matrix square-root
factorization of $Q|_{\mathbf1^\perp}$ then gives smoothness in $Q$.

For the covariance derivative, set
$N=(M^TM)^{-1}M^T$. Since $M$ is a column isomorphism onto
$\mathbf1^\perp$, $NM=I_n$ and $MN=P$. For the given $D$ let
$A=NDN^T$. Then $A=A^T$ and $MAM^T=PDP=D$. For sufficiently
small positive and negative $t$, $I+tA$ is positive, and

$$
 M(t)=M(I+tA)^{1/2},\qquad M(t)M(t)^T=Q+tD,\qquad
 M'(0)=MA/2.
$$

Off Gaussian-null ties the envelope score derivative is the winning
moment matrix $B$; the difference quotients have an integrable bound
proportional to $1+|X|$. The price derivative vanishes at balance.
Using (7) and cyclicity of trace gives

$$
 d\mathcal C(Q)[D]=\tfrac12\operatorname{tr}(B^TMA)
   =\tfrac12\operatorname{tr}(LMAM^T)
   =\tfrac12\operatorname{tr}(LD).
$$

Here $L$ uses weights $A_{ij}/\ell_{ij}$; it must not be confused with
the interface-area Laplacian with weights $A_{ij}$ used elsewhere in
multi-bubble profile theory. $\square$

# 3. The imported perimeter theorem and the regular constant

We use the established Gaussian multi-bubble theorem [MN22, Theorem 1.1]:
for $2\le k\le n+1$ and fixed positive masses in $\mathbb R^n$, a
simplicial Voronoi cluster of $k$ equidistant sites minimizes the total
Gaussian perimeter
$S=\frac12\sum_i P_\gamma(C_i)=\sum_{i<j}A_{ij}$.
We always apply it in dimension $n=k-1$, with $k=n+1$ and the strictly
positive mass vector $(1/k,\ldots,1/k)$. To match the theorem's
cluster definition, take the strict winning cells in (4), or assign
ties to the smallest label. These Borel cells are disjoint and cover
almost everywhere. Their Gaussian-null difference from (4) changes
no mass, moment or variational perimeter. Each has finitely many flat
facets of finite Gaussian area, and intersections of codimension at
least two contribute no interface area; for $n=1$ the interface is
a point with its zero-dimensional Hausdorff measure. They therefore
have finite Gaussian perimeter. The surface weight is the ambient
density $\varphi_n=(2\pi)^{-n/2}e^{-|x|^2/2}$ against
$\mathcal H^{n-1}$, not an independently normalized
$(n-1)$-dimensional Gaussian density. The original measurable or
fractional partition need not have finite perimeter: only this auxiliary
polyhedral cluster is used in the imported theorem.

At equal masses this minimizer
is the central regular simplex fan: balancing prices of regular scores
are unique modulo constants by Lemma 2, and permutation symmetry makes
all of them equal. Only the perimeter minimum, not its uniqueness part,
is needed below.

For the trace-one regular scores with Gram matrix $Q_*=P/n$, we can
write $Y_i=(Z_i-\overline Z)/\sqrt n$. Their winning labels are uniform,
so

$$
 \mathcal C(Q_*)=c_k.
$$

All facet weights are equal by symmetry; (7) gives
$L_*=c_kP$ and $w_{ij}^*=c_k/k$. All pair distances are
$\ell_* =\sqrt{2/n}$. Consequently the minimum perimeter is

$$
 S_* =\frac{k(k-1)}2\frac{c_k}k\sqrt{2/n}
              =c_k\sqrt{n/2}.                            \tag{9}
$$

For any $Q\in\mathcal K$ positive definite on $\mathbf1^\perp$,
weighted Cauchy--Schwarz and (7)
give

$$
 S^2=\left(\sum_{i<j}w_{ij}\ell_{ij}\right)^2
 \le\left(\sum_{i<j}w_{ij}\right)
        \left(\sum_{i<j}w_{ij}\ell_{ij}^2\right)
 =\tfrac12\operatorname{tr}L\,\mathcal C(Q).
$$

Combining this with $S\ge S_*$ proves the fundamental inequality

$$
 \mathcal C(Q)\frac{\operatorname{tr}L}{n}\ge c_k^2.       \tag{10}
$$

All weights here are positive, so equality in weighted Cauchy is
possible only when all pair distances are equal. This observation will
supply the equality classification.

# 4. The radial differential comparison and its deficit

**Theorem 3 (covariance form).** For every $Q\in\mathcal K$,
$\mathcal C(Q)\le c_k$, with equality only at $Q_*$.

*Proof.* Put $Q_t=Q_*+t(Q-Q_*)$. It is positive on
$\mathbf1^\perp$ for $0\le t<1$, even if the endpoint $Q$ is singular.
Let $C(t)=\mathcal C(Q_t)$ and $L_t$ be its facet matrix.
For $0<t<1$, (7)--(8) give

$$
 tC'(t)=\tfrac12\operatorname{tr}(L_t(Q_t-Q_*))
       =\tfrac12\left(C(t)-\frac{\operatorname{tr}L_t}{n}\right).
                                                               \tag{11}
$$

Let $h(t)=C(t)^2-c_k^2$. Inequality (10) implies

$$
 th'(t)=C(t)^2-C(t)\frac{\operatorname{tr}L_t}{n}
       \le h(t),\qquad
 \left(\frac{h(t)}t\right)'\le0.                         \tag{12}
$$

At zero $L_*=c_kP$, and $\operatorname{tr}(Q-Q_*)=0$.
Thus (8) gives $C'(0)=0$, while $C(0)=c_k$.
It follows that $\lim_{t\downarrow0}h(t)/t=0$.
The quotient is nonincreasing by (12), hence $h(t)\le0$ on $(0,1)$.
Continuity (5) gives the claimed bound at $t=1$. No differentiability,
balancing-price limit or bounded limiting facet matrix at a singular
endpoint is required.

If $\mathcal C(Q)=c_k$, the quotient tends to zero also at one.
A nonincreasing function with both endpoint limits zero is identically
zero. Therefore $C(t)=c_k$ for every $0<t<1$, and (11) gives
$\operatorname{tr}L_t=nc_k$. The perimeter/Cauchy chain in Section 3
then consists entirely of equalities. All $\ell_{ij}(t)$ are equal,
since all weights are positive. Centered scores of squared norm sum one
with equal pair distances have Gram matrix $P/n$: summing their squared
pair distances over $j$ gives $k|v_i|^2+1$, independent of $i$;
thus $|v_i|^2=1/k$ and $\ell_{ij}^2=2/n$. Hence $Q_t=Q_*$.
For any fixed $0<t<1$, this forces $Q=Q_*$. $\square$

There is also an exact deficit identity. For $Q_t$ as above put

$$
 D(t)=C(t)\frac{\operatorname{tr}L_t}{n}-c_k^2\ge0.
$$

The equality version of (12) reads $(h/t)'=-D(t)/t^2$, giving

$$
 c_k^2-\mathcal C(Q)^2=\int_0^1\frac{D(t)}{t^2}\,dt.     \tag{13}
$$

This is a nonnegative improper integral. At zero smoothness gives
$h=O(t^2)$; integrating on compact subintervals and using the endpoint
limits proves convergence and (13), even for a singular endpoint.
In particular, writing $W(t)=\sum_{i<j}w_{ij}(t)$,

$$
 D(t)=\frac2n\left[
   W(t)\sum_{i<j}w_{ij}(t)\ell_{ij}(t)^2-S(t)^2
                         +S(t)^2-S_*^2\right].           \tag{14}
$$

Both terms are nonnegative: the first is the weighted edge-length
variance, and the second is the established perimeter deficit.
This is an exact identity, not a claim of an explicit metric stability
constant or of full covariance concavity.

# 5. Return to measurable and fractional partitions

For any partition in Theorem 1, let $M$ be its $k\times d$ moment matrix.
Its rows sum to zero, so $MM^T$ has rank at most $k-1$ and trace $F$.
For every price, its labels give a feasible assignment in (3):

$$
 F=\mathbb E[m_I\cdot X]\le\mathcal C(MM^T).
$$

This remains valid for fractional labels by replacing the selected score
with their convex combination. The Gaussian score distribution has the
same covariance even if the original dimension differs from $k-1$.
When $F>0$, (5) and Theorem 3 give $F\le c_k\sqrt F$, proving (2).
For $F=0$ the positive bound is strict.

Equality forces $MM^T=F_kP/n$ and equality in the feasible assignment.
The regular centered scores have null ties and equal prices by symmetry
and uniqueness, so the original labels must be their winning labels
almost everywhere. Fractional labels likewise must be the unique
winning indicators. Their span has dimension $k-1$, which excludes
equality if $d<k-1$.

Conversely, take the regular scores with Gram matrix $P/n$ and their
central winning cells. By (7) and $L_*=c_kP$, their actual moments are
$c_kv_i$, of squared sum $c_k^2$. Cylindrical extension preserves both
masses and moments. This proves attainment and all equality assertions.
For $k=2$ the trace-one covariance domain is a singleton; the proof
includes this case. The excluded $k=1$ case is separately trivial, with
one cell and zero first moment.

# 6. Mathematical and verification dependencies

The only imported non-elementary geometric result is the Gaussian
multi-bubble perimeter theorem [MN22]. Its hypotheses, ambient dimension
and perimeter normalization are stated in Section 3. The proof uses
Gaussian integration by parts, dominated convergence, smooth matrix
square roots in the positive cone, the implicit function theorem, and
one-variable differential comparison. Price derivatives are justified
by Gaussian differentiation in fixed coordinates in Lemma 2. No further
regularity or second-variation theory for arbitrary perimeter minimizers
is required beyond the imported theorem. No local simplex Hessian, full
covariance concavity or mountain-pass theorem is assumed.

No finite search, solver, floating integral or numerical eigenvalue is a
premise of this result. Partial Lean proofs and exact arithmetic controls
bundled in this paper package have their own explicit scope and do not
formalize its Gaussian endpoint. A separate
[Lean development](https://github.com/mxym/math/pull/3)
formalizes actual Gaussian moments, balancing prices, flux and the
comparison and equality chains, with the needed geometric perimeter
lower bound remaining an explicit premise. It also proves regular
attainment and the necessary simplicial BV upper bridge. This does not
give a complete Lean proof of the imported multi-bubble theorem or the
unconditional all-$k$ endpoint. Internal model reviews are not external human peer review.
The complete earlier four-cell proof [FOUR] is preserved as a historical,
longer argument; the present proof is standalone and covers all $k$.

# References

- [H14] S. Heilman, *Euclidean Partitions Optimizing Noise Stability*,
  Electronic Journal of Probability 19 (2014), no. 71, 1--37;
  arXiv:1211.7138v2, Conjecture 3 and Definition 1.7.
- [H19] S. Heilman, *Stable Gaussian Minimal Bubbles*,
  arXiv:1901.03934v1, Problem 1.15 and Conjecture 1.16.
- [MN22] E. Milman and J. Neeman, *The Gaussian Double-Bubble and Multi-Bubble
  Conjectures*, Annals of Mathematics 195 (2022), no. 1, 89--206;
  DOI 10.4007/annals.2022.195.1.2; arXiv:1805.10961v3, Theorem 1.1.
- [EX] mxym/math research project, *A counterexample to the prescribed-mass
  Gaussian regular-simplex conjecture*, repository companion
  research/gaussian-fixed-mass-propeller-counterexample, 2026.
- [FOUR] mxym/math research project, *Four equal Gaussian cells: covariance
  deformation and tetrahedral rigidity*, complete eleven-page repository
  companion research/gaussian-balanced-four-global, commit 0d27bab, 2026.
