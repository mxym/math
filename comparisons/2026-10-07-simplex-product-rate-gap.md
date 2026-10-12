# The simplex product rate is below a known non simplex rate

This supplementary comparison concerns [entry 005 version 1.1 at the reviewed snapshot](https://github.com/mxym/math/tree/65a1baa1307ec91bc53a96087641cc575690f285/preprints/005-simplex-product-optimum). Its exact maximum over products of simplices is denoted by M_n, with c_n=(n+1)n^n/n! and ρ=c_13^(1/13). The statements in that manuscript are correctly restricted to this family.

Feng, Hu, Liu and Xu already construct non-simplex counterexamples in every dimension n≥9, with at most n+2 facets. Their dimension-13 result immediately implies that ρ is below an available unrestricted repeated-block rate. The following calculation makes that consequence quantitative:

$$
\exists Q\subset\mathbb R^{13},\qquad
\frac{R_{13}(Q)}{c_{13}}\ge
\frac{11774111}{11760000}>1,
\qquad R_n(K)=\frac{|\Pi K|}{|K|^{n-1}}.
$$

The body Q has at most 15 facets. This is a conservative specialization of the known construction, not a new unrestricted counterexample construction or an exact extremal value. The geometric source is [Feng–Hu–Liu–Xu, *On the Reverse Projection Inequality*, Theorem 1.3 and Section 4](https://archive.ymsc.tsinghua.edu.cn/pacm_download/743/12781--2026.8.26.pdf). The derivation below spells out the ingredients needed for this particular comparison.

## 1  The section construction

For m=n+2, let

$$
\Delta_{m-1}=\{s\in\mathbb R^m:s_i\ge0,\ \textstyle\sum_i s_i=1\},
\quad C_m=[-1/2,1/2]^m,
\quad F=\{\mathbf1,a\}^{\perp},
$$

where a≠0 and a·1=0. Put λ=1/m, interpreted coordinatewise, and S=(λ+F)∩Δ_(m−1). Write P_F for orthogonal projection and V_F for n-dimensional volume in F.

Here is the lower-bound mechanism of Feng–Hu–Liu–Xu, Proposition 4.1. Let q_i=P_Fe_i. These vectors span F and sum to zero, so Minkowski's existence theorem supplies a full-dimensional polytope Q whose facet-area vectors are the nonzero −q_i, with positively parallel vectors combined. There are at most m facets. Cauchy's formula gives

$$
\Pi Q=\sum_i[-q_i/2,q_i/2]=P_FC_m.
$$

For S′=S−λ, the inequalities z_i≥−λ_i imply h_(S′)(−q_i)≤λ_i. The mixed-volume formula and Minkowski's first inequality therefore give

$$
V_F(Q[n-1],S')\le\frac1n\sum_i\lambda_i=\frac1n,
\qquad
V_F(Q)^{n-1}V_F(S')
\le V_F(Q[n-1],S')^n\le n^{-n}.
$$

Consequently

$$
R_n(Q)\ge n^nV_F(S)V_F(P_FC_m). \tag{1}
$$

This uses an existence theorem for Q; it does not specify rational vertices.

Let f_a(t) be the probability density of a·s when s is uniform on Δ_(m−1), and set D(a)=Σ_(i<j)|a_i−a_j|. Coarea, using |Δ_(m−1)|=√m/(m−1)! and tangential gradient length ‖a‖, gives

$$
V_F(S)=\frac{\sqrt m\,\|a\|}{(m-1)!}f_a(0).
$$

Choose orthonormal columns spanning F and append 1/√m and a/‖a‖ to form an orthogonal matrix. Its complementary minors give the absolute determinant associated with omitted indices i,j as |a_i−a_j|/(√m‖a‖). The zonotope volume formula hence gives

$$
V_F(P_FC_m)=\frac{D(a)}{\sqrt m\,\|a\|}.
$$

Substituting into (1) and dividing by c_n, with m=n+2, yields

$$
\frac{R_n(Q)}{c_n}\ge
\frac{D(a)f_a(0)}{(n+1)^2}. \tag{2}
$$

These are the section and cube-projection identities in the source's Propositions 4.1–4.2.

## 2  A profile with an exact lower bound

Set ε=1/1000. Begin with the eleven-coordinate vector

$$
a^{(0)}=(-1,\varepsilon(-4,-3,-2,-1,0,1,2,3,4),1).
$$

For p uniform on Δ_8 put L=Σ_(j=−4)^4 jp_j and

$$
I(\varepsilon)=\mathbb E(1+\varepsilon|L|)^{-9}.
$$

The following calculation is the profile identity in the source's Lemma 4.3. For a uniform point of Δ_10, let w be the sum of the nine middle coordinates. Its density is 90w^8(1−w), and their normalized proportions are independently uniform on Δ_8. Conditional on w and p, the difference of the two outer coordinates is uniform on [−(1−w),1−w]. Its contribution to the density at zero is therefore [2(1−w)]^(−1) when εw|L|≤1−w. Thus

$$
f_{a^{(0)}}(0)
=45\mathbb E\int_0^{(1+\varepsilon|L|)^{-1}}w^8\,dw
=5I(\varepsilon). \tag{3}
$$

Adjoining a zero coordinate to a vector with m coordinates multiplies its central density by m/(m−1). Indeed, the added barycentric coordinate U has density m(1−u)^(m−1), and the old linear functional is multiplied by 1−U. Its new density at zero is f_a(0)E[(1−U)^(−1)]=mf_a(0)/(m−1). Four such steps yield

$$
a=(a^{(0)},0,0,0,0)\in\mathbb R^{15},
\qquad f_a(0)=\frac{14}{10}\,5I(\varepsilon)=7I(\varepsilon). \tag{4}
$$

The pairwise distances in a^(0) total 20+120ε: the outer-coordinate contribution is 20, and the nine equally spaced middle coordinates contribute 120ε. Each added zero contributes Σ_i|a_i^(0)|=2+20ε. Hence

$$
D(a)=28+200\varepsilon,
\qquad
\frac{R_{13}(Q)}{c_{13}}
\ge\left(1+\frac{50}{7}\varepsilon\right)I(\varepsilon). \tag{5}
$$

To evaluate the needed moment, parametrize uniform p by the gaps between eight ordered uniform [0,1] variables. Telescoping gives L=4−Σ_(i=1)^8U_i; the sum is unaffected by ordering. If S=ΣU_i, symmetry and inclusion–exclusion for the unit cube give

$$
\begin{aligned}
\mu:=\mathbb E|S-4|
&=2\mathbb E(4-S)_+\\
&=\frac{2}{9!}\sum_{k=0}^{4}(-1)^k\binom8k(4-k)^9
=\frac{1487}{2268}.
\end{aligned}
$$

The convex tangent inequality (1+x)^(−9)≥1−9x for x≥0 implies I(ε)≥1−9εμ. Equation (5) now gives the exact comparison

$$
\frac{R_{13}(Q)}{c_{13}}
\ge\frac{141}{140}\left(1-\frac{1487}{252000}\right)
=\frac{11774111}{11760000}
=1+\frac{14111}{11760000}>1. \tag{6}
$$

In particular Q cannot be a simplex, since every 13-dimensional simplex has value c_13.

The [exact checker](../verification/2026-10-07-independent-review/check_nonsimplex_gap.py) evaluates the moment, coordinate-distance sum and rational gain without floating-point decisions. It also verifies

$$
2.810223952012
<\left(c_{13}\frac{11774111}{11760000}\right)^{1/13}
<2.810223952013.
$$

The upper endpoint isolates the root of this lower bound; it is not an upper bound on R_13(Q)^(1/13).

## 3  Product multiplicativity and every large dimension

For full-dimensional polytopes A⊂R^r and B⊂R^s in orthogonal coordinate spaces, every facet of A×B has one facet factor and one whole factor. If a_i and b_j are their facet area-normal vectors, those of the product are (|B|a_i,0) and (0,|A|b_j). Cauchy's formula therefore gives

$$
\Pi(A\times B)=(|B|\Pi A)\times(|A|\Pi B).
$$

Taking volumes and cancelling exponents proves

$$
\begin{aligned}
R_{r+s}(A\times B)
&=\frac{|B|^r|A|^s|\Pi A||\Pi B|}
{(|A||B|)^{r+s-1}}\\
&=R_r(A)R_s(B). \tag{7}
\end{aligned}
$$

Interval factors are included by assigning their endpoints zero-dimensional area one, so ΠI=[−1,1] and R_1(I)=2. This product identity is also proved in the [pinned OpenAI source, Proposition 3](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-product-counterexample-to-the-simplex-maximum-for-projection-body-volume-September-24-2026/build/main.tex), and rederived in entry 005.

Let η=14111/11760000. Since M_(13k)=c_13^k, equations (6)–(7) imply

$$
\frac{R_{13k}(Q^k)}{M_{13k}}\ge(1+\eta)^k.
$$

For n=13k+r, 0≤r≤12, use K_n=Q^k×T_r when r>0 and K_n=Q^k otherwise. Entry 005 proves c_d≤ρ^d for every d≥1, hence M_n≤ρ^n. Put a_0=1 and a_r=c_r/ρ^r for r>0. Then

$$
\frac{R_n(K_n)}{M_n}\ge a_r(1+\eta)^k.
$$

Equivalently, with β=(1+η)^(1/13)>1 and C=min_(0≤r≤12)a_rβ^(−r)>0, this ratio is at least Cβ^n for every n≥13. Thus known non-simplex blocks beat the exact simplex-product optimum exponentially throughout all sufficiently large dimensions, not just on one subsequence.

## Scope of this supplement

The comparison does not change any theorem in entry 005 and supplies no unrestricted upper bound or maximizing-body classification. It combines the known Feng–Hu–Liu–Xu construction with the inherited product identity and a simple conservative rational estimate. Optimizing a finite menu of such blocks would remain a restricted integer optimization. An unrestricted result requires an additional geometric upper-bound or class-reduction argument.
