---
title: "Mathematical review of the Gaussian equal mass simplex theorem"
author: "Internal derivation review"
date: "8 October 2026"
geometry: margin=24mm
fontsize: 10pt
header-includes:
  - \usepackage{amssymb,amsmath}
---

# Verdict and scope

The six-page argument closes as an ordinary mathematical proof using the
published Milman--Neeman Gaussian multi-bubble theorem. I found no fatal
gap in the sharp bound, equality classification, lower-dimensional
strictness, fractional extension, or covariance deficit identity. The
perimeter theorem is a proved external dependency; the new argument does
not need to reprove its existence, compactness, regularity, or stability
theory. Several compressed analytic steps deserve expansion for a
referee, especially the price Hessian and its implicit-function argument.
Those steps are derived below without an additional conjecture or a
stronger hypothesis on the partitions.

This is an internal mathematical review based on rederivation from the
frozen manuscript and the primary theorem statement. The reviewer also
worked on the partial Lean development. Independence here concerns the
derivation and evidence chain, not a different external human referee.
Earlier review verdicts and Lean compilation records are not premises of
the mathematical verdict. This is not a complete Lean certificate or an
external journal acceptance.

The claim supported by this review is: **a rigorous mathematical proof of
the equal-mass Gaussian first-moment theorem using the published Gaussian
multi-bubble theorem**. A claim of complete formalization in Lean, with
the geometric dependency proved inside Lean, remains unsupported.

# Frozen manuscript and primary sources

The reviewed manuscript is
`research/gaussian-balanced-simplex-all-k/paper.md` at repository commit
`890422e18fd7c80f3ce834426081211763cbc956` in `mxym/math`. Its generated
`paper.pdf` has six pages. A fresh read of `paper.md` at main commit
`659e28073517cc79f86bc9c6ffede9240638e855` gave identical bytes.

Frozen `paper.md`:

```text
8416f741398ceb4207edcc3ff31964883ae14044698043bf17a75d66c1dec832
```
Frozen six-page `paper.pdf`:

```text
f50e07e08e1c9a676b7c5511dcb5a88c4dd18c8b867dcbf5169f62b24bf08872
```
Freshly downloaded Milman--Neeman v3 PDF:

```text
2bebde484903a994dcc198294e404adb4e6d20ad689cd2ba93671e6cbbae1220
```

The main primary reference is Milman and Neeman, *The Gaussian
Double-Bubble and Multi-Bubble Conjectures*, Annals of Mathematics 195
(2022), 89--206, [published article and
DOI](https://annals.math.princeton.edu/2022/195-1/p02). The
[author manuscript v3](https://arxiv.org/pdf/1805.10961v3), printed
pages 1--3, supplies the perimeter and cluster definitions and Theorem
1.1. The final publication abstract independently confirms its range
and minimizing model. Only its perimeter lower bound is imported.

# The exact multi-bubble application

Write $n=k-1$, $E=\mathbf1^\perp\subset\mathbb R^k$,

$$
 P=I-\mathbf1\mathbf1^T/k,\qquad Q_*=P/n.
$$

The auxiliary full-dimensional winning clusters live in
$\mathbb R^n$, regardless of the dimension of the original partition.
Thus the theorem is applied with $q=k=n+1$, and the mass vector is
$(1/k,\ldots,1/k)$, an interior probability vector. In the primary
source a cluster consists of disjoint Borel cells with finite Gaussian
perimeter covering almost everywhere; its total perimeter is half the
sum of the cell perimeters. These are exactly the hypotheses required
here. [Milman--Neeman, printed pp.
1--3](https://arxiv.org/pdf/1805.10961v3).

To obtain such a cluster from the manuscript's closed cells, take the
strict winning cells, or assign ties to the smallest label. All pair
ties lie in affine hyperplanes with nonzero normal, hence are
Gaussian-null. This changes no mass, moment, or variational perimeter.
The cells are Borel polyhedra. Their boundary consists of finitely many
flat facets, with intersections of codimension at least two when
$n\ge2$. Each facet's Gaussian area is at most the area of its
supporting hyperplane and is finite. For $n=1$, the interface is a
point and the same statement uses counting Hausdorff measure.
Consequently these auxiliary cells have finite perimeter. In particular,
the original arbitrary measurable or fractional partition is **not**
being assumed to have finite perimeter: the imported theorem is applied
only to the auxiliary polyhedral partition.

The model supplied by the theorem has equidistant sites. In dimension
$k-1$ its centered score vectors form a full regular simplex. Their
zero-price cells have equal masses by permutation symmetry. The unique
balanced prices modulo constants, proved below, force any equally
balanced model to have common prices; its active translation is therefore
zero. The minimum at equal masses is the central regular fan. The
uniqueness theorem for arbitrary perimeter minimizers is not needed.

There is no out-of-range use of the theorem at a singular covariance or
in an original dimension $d<k-1$. Those cases are handled by continuity
from the full auxiliary dimension.

# Prices and the singular covariance boundary

For $Y\sim N(0,Q)$, define

$$
 J_Q(\lambda)=\frac1k\sum_i\lambda_i+
       \mathbb E\max_i(Y_i-\lambda_i),\qquad
 \mathcal C(Q)=\inf_\lambda J_Q(\lambda).
$$

The maximum is integrable since the finite Gaussian vector has an
integrable norm. Its average bounds the maximum below, giving
$J_Q(\lambda)\ge0$. Common price shifts cancel. In the gauge
$\min_i\lambda_i=0$, select a zero-priced coordinate. Its expectation
is zero, so $J_Q(\lambda)\ge\max_i\lambda_i/k$. Continuity and this
coercive bound on the closed gauge set give a minimizing price, even if
$Q$ is singular.

For distinct score rows $v_i$, a price tie is an affine hyperplane
with nonzero normal and thus null. The price difference quotients of the
maximum are bounded by one. Dominated convergence yields

$$
 \partial_{\lambda_i}J=1/k-p_i,\qquad p_i=\gamma_n(C_i).
$$

At a minimizer this gradient vanishes: it lies in $E$, and vanishes
on the gauge $E$. The winning cells have all masses $1/k$, and
their pointwise winning assignment attains $J$. No general strong
duality theorem for repeated or singular scores is needed later.

For $s>0$, the substitution $Y\mapsto\sqrt sY$,
$\lambda\mapsto\sqrt s\lambda$, is a bijective change in the infimum
and proves homogeneity. At $s=0$, the lower bound zero and equal prices
give $\mathcal C(0)=0$.

For continuity, use a single standard $k$-dimensional Gaussian $G$
and the positive semidefinite square roots of both covariance matrices.
For every price the difference of the two maxima is bounded in absolute
value by
$\|(Q^{1/2}-\widetilde Q^{1/2})G\|$. The bound is integrable and
independent of the price. Taking infima in both directions therefore
preserves this bound. Continuity of the matrix square root proves
continuity of $\mathcal C$, including rank loss and repeated rows.

# Flux, smoothness and the covariance derivative

For this section assume $Q$ is positive definite on $E$. It still
has a zero eigenvalue on $\mathbb R\mathbf1$; “full rank” must mean
rank $k-1$, not rank $k$. Choose centered rows of a $k\times n$
matrix $M$ with $MM^T=Q$. Its column map is an isomorphism from
$\mathbb R^n$ onto $E$. Each score-difference coordinate map is
invertible.

Every pair of cells has a genuine facet of positive area at every
finite price. In the invertible score-difference coordinates prescribe
the chosen pair to tie and every other score to be strictly smaller.
This gives a relatively open subset of the pair hyperplane, with
positive Gaussian density. Set

$$
 \ell_{ij}=\|v_i-v_j\|,\quad
 A_{ij}=\int_{\Sigma_{ij}}\varphi_n\,d\mathcal H^{n-1},\quad
 w_{ij}=A_{ij}/\ell_{ij},\quad
 L=\sum_{i<j}w_{ij}(e_i-e_j)(e_i-e_j)^T.
$$

All $w_{ij}>0$. With the inward normal
$(v_i-v_j)/\ell_{ij}$, Gaussian integration by parts gives

$$
 b_i=\int_{C_i}x\,d\gamma_n
       =\sum_{j\ne i}w_{ij}(v_i-v_j),\qquad B=LM.
$$

The sign is correct: $\nabla\varphi_n=-x\varphi_n$, so the moment
is the negative outward flux. Truncating at radius $R$ adds a term
bounded by a constant times $R^{n-1}e^{-R^2/2}$, which tends to zero.
Gaussian first-moment integrability and increasing facet truncations
justify both limits. Triple junctions have no facet-area contribution.

At balanced prices, the price contributions cancel, hence

$$
 \mathcal C(Q)=\langle M,B\rangle=
 \operatorname{tr}(LQ)=\sum_{i<j}w_{ij}\ell_{ij}^2,
 \qquad \operatorname{tr}L=2\sum_{i<j}w_{ij}.
$$

## A detailed price Hessian justification

Let $T$ have rows $v_i-v_k$, $i<k$, and let
$a_i=\lambda_i-\lambda_k$. The vector
$s=TX-a$ has covariance $TT^T>0$ and mean $-a$.
The objective is the explicit linear price term plus

$$
 J(M,\lambda)=\frac1k\sum_i\lambda_i-\lambda_k+
 \int_{\mathbb R^n}\max(0,s_1,\ldots,s_n)
                  p_{TT^T,-a}(s)\,ds.
$$

Here the maximum and all winner regions are fixed functions or cones in
$s$. On a compact neighborhood of a full-rank parameter, covariance
eigenvalues are bounded away from zero and infinity and the means are
bounded. Every parameter derivative of the density is bounded by
$C(1+\|s\|)^m e^{-c\|s\|^2}$, for some $C,c>0$ and finite $m$
depending on the derivative order. Multiplication by the maximum, which
has at most linear growth, preserves integrability. Differentiating
under the integral proves smoothness of the objective and the cell
probabilities.

For a fixed cell $i$, use instead the coordinates
$(v_i-v_j)\cdot X$, $j\ne i$. Its probability is a smooth Gaussian
orthant integral with thresholds $\lambda_i-\lambda_j$.
Differentiating one lower threshold produces the negative face integral.
Coarea for that linear coordinate supplies exactly the factor
$1/\ell_{ij}$. Therefore

$$
 \partial_{\lambda_i}p_i=-\sum_{j\ne i}w_{ij},\qquad
 \partial_{\lambda_j}p_i=w_{ij}\quad(j\ne i),\qquad
 \nabla^2_\lambda J=L.
$$

This proves both the sign and the normalization of the claimed Hessian.
For $u\in E\setminus\{0\}$,

$$
 u^TLu=\sum_{i<j}w_{ij}(u_i-u_j)^2>0.
$$

Thus the objective is strictly convex on the gauge $E$, since this
holds at every price along each nonconstant segment. Its minimizing
price is unique there. The gauge gradient maps $E$ to $E$; its
Jacobian $L|_E$ is invertible. The implicit function theorem makes
the balanced prices smooth in the full-rank scores. A local smooth
square-root factorization of $Q|_E$ then gives smoothness of
$\mathcal C$ on this relative positive cone.

## Independent derivation of the factor one half

For a symmetric $D$ with $D\mathbf1=0$, put

$$
 N=(M^TM)^{-1}M^T,\qquad A=NDN^T.
$$

Then $A=A^T$, $NM=I_n$, $MN=P$, and
$MAM^T=PDP=D$. For sufficiently small positive and negative $t$,
$I+tA>0$, and

$$
 M(t)=M(I+tA)^{1/2},\quad M(t)M(t)^T=Q+tD,
 \quad M'(0)=MA/2.
$$

The envelope score derivative is $B$. Its pointwise derivative exists
off null ties, with an integrable bound proportional to $1+\|X\|$.
The price derivative vanishes at balance. Consequently

$$
 d\mathcal C(Q)[D]=\tfrac12\operatorname{tr}(B^TMA)
 =\tfrac12\operatorname{tr}(LMAM^T)
 =\tfrac12\operatorname{tr}(LD).
$$

There is no missing price term, derivative of $L$, or factor of two.
This $L$ has weights $A_{ij}/\ell_{ij}$; it is not the interface-area
Laplacian with weights $A_{ij}$ appearing elsewhere in the multi-bubble
literature. The proof uses only the perimeter theorem from that literature.

# Perimeter normalization and the regular constant

The Gaussian surface weight here is the ambient density
$\varphi_n=(2\pi)^{-n/2}e^{-\|x\|^2/2}$ against
$\mathcal H^{n-1}$. It is not the independently normalized
$(n-1)$-dimensional Gaussian density. On the polyhedral cells,

$$
 S=\tfrac12\sum_iP_\gamma(C_i)=\sum_{i<j}A_{ij}
      =\sum_{i<j}w_{ij}\ell_{ij}.
$$

Each interface appears twice in the cell-perimeter sum and once in
$S$. At the regular trace-one covariance, take
$Y_i=(Z_i-\overline Z)/\sqrt n$, so
$\mathcal C(Q_*)=a_k/\sqrt n=c_k$. All pair distances satisfy
$\ell_*^2=2/n$. The symmetric complete-graph Laplacian is
$L_*=kw_*P$. Since $\operatorname{tr}Q_*=1$, the flux identity gives
$kw_*=c_k$, hence

$$
 L_*=c_kP,\quad w_*=c_k/k,\quad
 S_*={k(k-1)\over2}{c_k\over k}\sqrt{2/n}
      =c_k\sqrt{n/2}.
$$

The multi-bubble theorem yields $S\ge S_*$. Weighted
Cauchy--Schwarz gives

$$
 S^2\le\left(\sum_{i<j}w_{ij}\right)
              \left(\sum_{i<j}w_{ij}\ell_{ij}^2\right)
       =\tfrac12\operatorname{tr}L\,\mathcal C(Q),
$$

so $\mathcal C(Q)\operatorname{tr}L/n\ge c_k^2$, exactly the
manuscript's inequality (10). This uses a lower bound on perimeter;
the direction has not been reversed.

As exact normalization checks, $k=2$ gives
$a_2=1/\sqrt\pi$, $F_2=1/\pi$, and
$S_*=1/\sqrt{2\pi}$, the single central interface. For $k=3$,
$a_3=3/(2\sqrt\pi)$, $F_3=9/(8\pi)$, and
$S_*=3/(2\sqrt{2\pi})$, the sum of three half-line interfaces.
These are algebraic checks, not numerical premises of the all-$k$ proof.

# Radial comparison and singular endpoints

For every centered positive semidefinite trace-one $Q$,

$$
 Q_t=(1-t)Q_*+tQ
$$

is positive definite on $E$ for $0\le t<1$: its quadratic form is
at least $(1-t)\|u\|^2/n$ there. Write $C(t)=\mathcal C(Q_t)$.
Since $L_t\mathbf1=0$, $L_tP=L_t$, and the derivative formula gives

$$
 tC'(t)=\tfrac12\operatorname{tr}(L_t(Q_t-Q_*))
       =\tfrac12(C(t)-\operatorname{tr}L_t/n).
$$

Set $h(t)=C(t)^2-c_k^2$ and
$D(t)=C(t)\operatorname{tr}L_t/n-c_k^2\ge0$. Direct differentiation
gives the exact identity

$$
 th'(t)=h(t)-D(t),\qquad (h(t)/t)'=-D(t)/t^2\le0.
$$

At $t=0$, $L_*=c_kP$ and the trace of $Q-Q_*$ is zero, hence
$C'(0)=0$, $h(0)=h'(0)=0$. Thus $h(t)/t\to0$ from the right.
A nonincreasing function with that initial limit is nonpositive, giving
$C(t)^2\le c_k^2$. Since $c_k>0$, this implies $C(t)\le c_k$.
Continuity of $\mathcal C$ extends the inequality to $t=1$.

No differentiability, balancing-price convergence, finite limiting
facet weight, or perimeter comparison is being asserted at a singular
endpoint. The proof uses only continuity there. This includes endpoints
with repeated rows and covariances arising from dimensions below $k-1$.

# Equality and the return to partitions

If $\mathcal C(Q)=c_k$, the endpoint limits of $h(t)/t$ are both
zero. Antitonicity makes this quotient identically zero on $0<t<1$.
Then $C(t)=c_k$ and $\operatorname{tr}L_t=nc_k$. The two inequalities

$$
 S_*^2\le S(t)^2\le\tfrac12\operatorname{tr}L_t C(t)=S_*^2
$$

are equalities. Equality in weighted Cauchy, with every weight positive,
forces every pair length to be the same. For centered rows with
$\sum_i\|v_i\|^2=1$, summing squared distances over $j$ gives

$$
 (k-1)\ell^2=k\|v_i\|^2+1.
$$

All row norms are equal, hence are $1/k$ in squared norm;
$\ell^2=2/(k-1)$. Their Gram entries are exactly those of
$P/(k-1)$. Thus $Q_t=Q_*$ at any chosen interior time, and
$t(Q-Q_*)=0$ forces $Q=Q_*$. This argument also works for $k=2$,
where the covariance domain is a singleton. It does not import
uniqueness of general perimeter minimizers.

Now take any measurable fractional partition with equal masses, and
write $m_i=\int xf_i\,d\gamma_d$, $M=(m_i)_i$,
$F=\sum_i\|m_i\|^2$. The moments are integrable because
$0\le f_i\le1$; their sum is zero. At each price,

$$
 \sum_if_i(x)m_i\cdot x\le
 \max_i(m_i\cdot x-\lambda_i)+\sum_if_i(x)\lambda_i.
$$

Integrating gives $F\le J_{MM^T}(\lambda)$ for every price, and
therefore $F\le\mathcal C(MM^T)$. This step uses the original
Gaussian dimension only through the covariance of the scores.

If $F>0$, normalize $Q=MM^T/F$ and use homogeneity:

$$
 F\le\sqrt F\,\mathcal C(Q)\le\sqrt F\,c_k,
 \qquad F\le c_k^2.
$$

At $F=c_k^2$, both inequalities are equalities, so
$MM^T=c_k^2P/n$. The score rows are distinct and regular, and their
balanced prices are equal. The pointwise assignment gap is nonnegative
and integrable with integral zero, hence zero almost everywhere. Off
the null tie set its expression is a sum of nonnegative loser weights
times strictly positive score gaps. All loser weights are zero and the
winner weight is one. Thus fractional labels are actual regular winning
indicators almost everywhere.

The Gram matrix has rank $k-1$. Since the moment matrix has rank at
most $d$, equality is impossible when $d<k-1$. For $F=0$, the
positive constant makes the inequality strict as well. In $d\ge k-1$,
the Gram identity supplies an isometric embedding of the regular score
span. The cells depend only on the projection onto that span, yielding
precisely the cylindrical regular fan, up to orthogonal transformations,
label permutations, and null sets.

Conversely, for regular trace-one score rows $v_i$, flux gives
$b_i=c_kv_i$, so the actual regular partition has energy $c_k^2$.
Independent orthogonal Gaussian coordinates have mean zero, making
cylindrical extension preserve masses and moments. This proves
attainment without assuming that an arbitrary maximizing partition
exists. The excluded $k=1$ case has zero total first moment and is
separate; the stated theorem begins at $k=2$.

# The exact covariance deficit

On $0<a<b<1$, the fundamental theorem of calculus gives

$$
 \int_a^b D(t)/t^2\,dt=h(a)/a-h(b)/b.
$$

The integrand is continuous and nonnegative on the open interval.
The two endpoint limits exist and are finite: the first is zero and the
second is $\mathcal C(Q)^2-c_k^2$. Passing to the endpoints proves
convergence of the nonnegative improper integral and its exact value.
Smoothness at zero also gives $h(t)=O(t^2)$, but no boundedness
assumption on $L_t$ at one is needed.

Writing $W=\sum_{i<j}w_{ij}$ and using
$S_*^2=nc_k^2/2$ gives exactly

$$
 D(t)=\frac2n\left[
  W\sum_{i<j}w_{ij}\ell_{ij}^2-S(t)^2+
  S(t)^2-S_*^2\right].
$$

The first bracket is weighted Cauchy variance; the second is the
perimeter deficit. Both are nonnegative. Formula (13) concerns the
covariance-value deficit $c_k^2-\mathcal C(Q)^2$; it is not, by
itself, a quantitative distance estimate or a stability constant for
arbitrary partitions. The manuscript respects this distinction.

# Publication clarifications and formalization status

No unresolved mathematical blocker was found in the reviewed route.
The following edits would make the six-page proof easier to audit. They
are the amendments requested by the user after this review. A separately
identified expanded draft incorporates them; the frozen source above
remains the reviewed baseline. The revision provenance identifies the
new manuscript bytes, and the earlier reviews retain their original scope.

1. Expand Lemma 2 with the fixed-density integral, the displayed price
   probability derivatives, positivity of $L|_E$, and the explicit
   $A=NDN^T$ construction above. This is the most useful addition.
2. State that “full rank” means positive definite on $\mathbf1^\perp$,
   and replace closed winning cells by their disjoint null-equivalent
   representatives when invoking the multi-bubble theorem. Mention their
   finite perimeter and the ambient density used for surface area.
3. Explicitly call the fractional $f_i$ measurable. Clarify that the
   claim about avoiding boundary variation concerns variations of
   arbitrary competing clusters; price differentiation is justified in
   fixed Gaussian coordinates in Lemma 2.
4. Keep the mathematical dependency and the Lean certificate scope
   separate. Ordinary rigorous mathematics can use the proved
   Milman--Neeman theorem. The partial Lean theorem still has an explicit
   geometric premise, and its module count does not discharge that
   premise.

For the prior-conjecture identification, Heilman's
[2019 paper, printed p. 8](https://arxiv.org/pdf/1901.03934v1), has a
fixed-mass first-moment objective shifted by the model translation. At
equal masses that translation is zero; its positive scalar factor
does not change maximizers. The present theorem therefore covers its
equal-mass subcase. Heilman's
[2014 author manuscript](https://arxiv.org/pdf/1211.7138v2), equation
(14), Definition 2.2 and Conjecture 3, likewise identifies the four-cell
equal-mass fractional first-moment problem. These checks establish
overlap with the cited conjectures, not priority among later work. The
unequal-mass companion counterexample and the historical four-cell
paper are not dependencies of this proof and were not audited here.

The preserved Lean checkpoint contains actual standard-Gaussian
definitions and proofs for moments, balanced prices, flux, covariance
differentiation, regular attainment, and the analytic comparison and
equality chain **with its perimeter premise explicit**. In particular:

- `covariance_comparison_of_perimeter` takes
  `EqualMassSimplicialPerimeterBound d` and proves the covariance bound
  and exact integral deficit.
- `equality_iff_regular_fan_of_perimeter` takes that same premise and
  proves the almost-everywhere fractional equality classification.
- `regular_fan_attains` is unconditional.
- The needed general simplicial BV upper bridge is proved
  unconditionally. `GaussianBalancedBVLowerBound d`, which represents
  the required balanced multi-bubble lower bound, has not been proved
  inside Lean. Gaussian BV compactness has also not been proved inside
  Lean, and it is unnecessary to redo that infrastructure for this
  ordinary mathematical proof using the published theorem.

The development checkpoint has 136 source modules with successful
exact-byte incremental compilations. The earlier empty-kernel
trust-level-zero audit covers only its original 53 matching modules.
No independent whole-bundle compilation, all-declaration audit, or
empty-kernel replay of all 136 modules is claimed. These facts are
recorded separately and are not used to infer the mathematical verdict.

Recommended public positioning: **the equal-mass all-$k$ theorem has
a rigorous mathematical proof using the published Gaussian multi-bubble
theorem; substantial partial Lean formalization is available with an
explicit geometric premise.** Keep the formalization branch and PR
marked as partial. Expand the indicated analytic details and obtain an
external mathematical reader before treating this internal review as
external peer review.
