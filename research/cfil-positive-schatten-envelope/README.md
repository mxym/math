# The sharp upper envelope for the sum of two positive Schatten operators

**Research draft · 18 November 2026.** Fix the two Schatten $p$-norms and the nonnegative overlap $\operatorname{Tr}(A^{p/2}B^{p/2})$. For every real $2\le p<\infty$, the largest possible $\|A+B\|_p$ is exactly the scalar Ivanisvili–Mooney envelope: a pair of commuting diagonal matrices of size two attains it. The bound implies the two-positive-operator inequality proposed by Carlen–Frank–Ivanisvili–Lieb in (5.5) of their paper. It does not address arbitrary signed operators or families of three or more.

**中文摘要。** 给定两个正 Schatten 算子的 $p$ 范数及其 $p/2$ 次幂乘积的迹，本文给出其和的 $p$ 范数的精确上界，适用于所有实数 $p\ge2$（有限）。二维对角矩阵即可取等，从而得到 CFIL 原文式 (5.5) 的双正算子结论。这不是多算子 Carbery 问题的新解。

The proof and a [separate adversarial review](REVIEW.md) were AI-assisted. Neither external peer review nor formal verification has been performed; no priority is claimed. [Reproduction instructions](CHECKS.md) distinguish exact checks from numerical tests.

## 1. The bound and its sharpness

Let A,B be positive semidefinite matrices on the same finite-dimensional complex Hilbert space (or positive operators in the Schatten class S_p). For any real 2 ≤ p < ∞ set
$$
 X=\operatorname{Tr}A^p,\quad Y=\operatorname{Tr}B^p,\quad
 S=(X+Y)/2,\quad Z=\operatorname{Tr}(A^{p/2}B^{p/2}),\quad u=Z/S .
$$
In this note the trace is not normalized. If S=0 both operators vanish; assume S>0. Positivity and Hilbert–Schmidt Cauchy–Schwarz give 0≤Z≤√(XY)≤S. Define
$$
 E_p(u)=(1+\sqrt{1-u^2})^{1/p}+(1-\sqrt{1-u^2})^{1/p}.
$$
The sharp bound is
$$
                 \boxed{\|A+B\|_p\le S^{1/p} E_p(u).}                 \tag{1}
$$
For nonnegative scalar functions this is Ivanisvili–Mooney (IM), Theorem 2.1. IM Corollary 2.3 proves the following scalar inequality:
$$
 E_p(u)^p/2\le(1+u^{2/p})^{p-1}.
$$
Consequently (1) implies the dimension-independent, positive-operator inequality proposed by Carlen–Frank–Ivanisvili–Lieb (CFIL, journal (5.5), preprint (5.5)):
$$
  \operatorname{Tr}(A+B)^p\le (X+Y)(1+u^{2/p})^{p-1}.             \tag{2}
$$
The trace of the positive sandwich $B^{p/4}A^{p/2}B^{p/4}$ in CFIL's formula is exactly $Z$ by cyclicity. We do not assert (1) for signed inputs with this overlap, or a new solution of Carbery's many-operator problem.

**Sharp for each fixed triple, not only each ratio.** For any X,Y≥0, 0≤Z≤√(XY), S>0 let d=√(1-u²). If d>0 put θ=(1+(X−Y)/(2Sd))/2. Then 0≤θ≤1 follows from Z²≤XY. In dimension two choose diagonal p-th powers
$$
 A^p=S\,\mathrm{diag}(\theta(1+d),(1-\theta)(1-d)),\qquad
 B^p=S\,\mathrm{diag}(\theta(1-d),(1-\theta)(1+d)).
$$
Their two traces are X,Y. Their overlap is Su, and each diagonal entry of (A+B)^p equals either Sθ E_p(u)^p or S(1−θ) E_p(u)^p. Hence (1) is attained. If d=0 then X=Y=Z=S and equal scalars work. If u=0 the formula simply uses disjoint supports. The sharpness construction is a matrix realization of the already known commutative extremizers, not an additional improvement of IM.

## 2. Two planar measures (finite-dimensional proof)

Write A=Σ a_i P_i, B=Σ b_j Q_j for their distinct eigenvalues and spectral projections, including zero eigenvalues. Let μ be Heinävaara's **positive** tracial joint spectral measure. Its defining identity is
$$
 \int f(cx+ey)\,d\mu
  =\int_0^1 w(h)\operatorname{Tr} f(h(cA+eB))\,dh,
 \qquad w(h)=(1-h)/h,                                             \tag{3}
$$
for admissible f vanishing at zero (in particular for all the tests used below); c,e are real. This is [Heinävaara's Theorem 1.4 in the arXiv version](https://arxiv.org/pdf/2310.03227), [published in *Inventiones Mathematicae*](https://doi.org/10.1007/s00222-024-01309-6). Its test condition is local integrability of $|f(v)/v|$; the positive powers and the compensated exponential used here satisfy it. For positive A,B the coordinate marginals, tested with c=1,e=0 and conversely, imply support in the rectangle K=[0,‖A‖]×[0,‖B‖] up to null sets: use nonnegative continuous tests supported outside these intervals and away from zero. For any k>0, applying (3) to f(v)=|v|^k gives e.g. ∫x^k dμ=Tr A^k/[k(k+1)]. Also ∫(x+y)dμ<∞. The measure need not be finite at the origin.

The second measure ν is the radial image of the ordinary two-eigenbasis coupling:
$$
 \int F(x,y)\,d\nu=\sum_{ij}\operatorname{Tr}(P_iQ_j)
             \int_0^1 w(h) F(ha_i,hb_j)\,dh.                      \tag{4}
$$
The weights Tr(P_i Q_j)=‖P_i Q_j‖₂² are nonnegative. Discard all mass mapped to (0,0) in (4); every test used here vanishes there. This prevents assigning infinite mass to a single atom and makes ν sigma-finite on the punctured rectangle. Both measures are sigma-finite off the origin by integrability of x+y there. We may take μ({(0,0)})=0 as well. They have the same coordinate marginals on tests vanishing at zero. Both are supported on K and have finite first absolute moments.

For suitable tests $F$ below write $[F]=\int F\,d\nu-\int F\,d\mu$, only when both integrals are separately finite. We do not form the difference of the masses of the plane.

## 3. Fractional mixed moments by a two-variable Golden–Thompson deficit

For s,t≥0 set
$$
 L(s,t)=[e^{-s x-t y}-1]
   =\int_0^1 w(h)\big(\operatorname{Tr}(e^{-hsA}e^{-htB})
                        -\operatorname{Tr}e^{-h(sA+tB)}\big)\,dh\ \ge 0.   \tag{5}
$$
The two integrals defining the bracket are finite because the test is O(x+y) on K. The difference of matrix traces in (5) is taken *before* integrating with w(h); the constants Tr I cancel. The inequality is ordinary Golden–Thompson applied to the Hermitian pair −hsA,−htB for each h, not an operator-order comparison. No positivity of an operator product is presumed; its trace is a nonnegative real.

Besides $L(s,0)=L(0,t)=0$, we have
$$
              \partial_tL(s,0)=0,\qquad\partial_sL(0,t)=0.       \tag{6}
$$
Indeed both t-derivatives under the radial integral are −h Tr(B e^(−hsA)) at t=0, by the Duhamel formula and cyclicity for the second trace; the s-derivative is identical after interchanging A and B. Differentiation under the planar and radial integrals is valid: the rectangle is bounded, all positive-degree monomials are integrable, and w(h)h is integrable at zero. This also gives ∂s∂t L(0,0)=0 by differentiating (6) along its axis. Equivalently
$$
 [xe^{-ty}]=[ye^{-sx}]=[x]=[y]=[xy]=0.                           \tag{7}
$$

The [independent moment argument](REVIEW.md#an-alternative-proof-of-the-axis-cancellations) proves these same cancellations without differentiation.

Let $k(v)=e^{-v}-1+v\ge0$ for $v\ge0$. Expanding its product as **separately integrable** terms gives
$$
 \begin{aligned}
 k(sx)k(ty)={}&(e^{-sx-ty}-1)-(e^{-sx}-1)-(e^{-ty}-1)\\
 &+s x(e^{-ty}-1)+t y(e^{-sx}-1)+stxy.
 \end{aligned}
$$
By (5)–(7),
$$
                 [k(sx)k(ty)]= L(s,t)\ge0.                       \tag{8}
$$
For 1<r<2, let c_r be the reciprocal of ∫₀∞ k(v)v^(−r−1)dv. This is strictly positive finite: k(v)=O(v²) at 0 and O(v) at infinity. Scaling gives
$$
 x^r =c_r\int_0^\infty k(sx)s^{-r-1}\,ds\quad(x\ge0).
$$
For 1<r,l<2, multiply the inequality in (8) by c_r c_l s^(−r−1)t^(−l−1) and integrate. Apply Tonelli to the separate positive kernels for each measure, not to a signed measure of infinite mass. Their resulting mixed moments are finite on K (bound x^r y^l by a constant times x+y). From (4) and ∫₀¹ w(h)h^(r+l)dh=1/[(r+l)(r+l+1)] it follows that
$$
   (r+l)(r+l+1)\int x^r y^l\,d\mu
       \le \sum_{ij}\operatorname{Tr}(P_iQ_j)a_i^r b_j^l
       =\operatorname{Tr}(A^r B^l).                               \tag{9}
$$
This extends to 1≤r,l≤2 by dominated convergence, because the integrands are dominated uniformly by C_K(x+y). No assertion of the corresponding mixed-moment comparison is needed or made for higher powers, where a blanket replacement of symmetrized words would be unjustified.

## 4. Base interval and exact doubling closure

For 2≤p≤4 apply the classical IM Theorem 2.1 to the coordinate functions x,y on the positive measure space with measure p(p+1)μ. Formula (3) applied to |⋅|^p identifies their p-th moments with X,Y, and that of their sum with Tr(A+B)^p. Their mixed moment Z' = p(p+1)∫(xy)^(p/2)dμ satisfies 0≤Z'≤Z by (9). The function E_p(u) is nondecreasing on [0,1]: for q=1/p<1 the derivative of (1+d)^q+(1−d)^q with respect to 0<d<1 is q[(1+d)^(q−1)−(1−d)^(q−1)]≤0, while d=√(1−u²) is nonincreasing; use continuity at both ends. Thus replacing Z'/S by Z/S weakens the classical upper bound in the required direction. This proves (1) in the entire closed base interval.

The doubling device is due to CFIL (Theorem 5.3); the **sharp** envelope propagates without loss. Suppose (1) holds at p≥2. Given A,B at order 2p, normalize (Tr A^(2p)+Tr B^(2p))/2=1 by common scaling (the zero case was removed). Put u=Tr A^p B^p. At order p the pair A²,B² has exactly the same normalized overlap. Therefore,
$$
 \begin{aligned}
 \|A+B\|_{2p}^2&=\|(A+B)^2\|_p\\
 &\le \|A^2+B^2\|_p+\|AB\|_p+\|BA\|_p\\
 &\le E_p(u)+2u^{1/p}\ =\ E_{2p}(u)^2 .                          \tag{10}
 \end{aligned}
$$
Here ‖BA‖_p=‖AB‖_p and Tr|AB|^p=Tr(BA²B)^(p/2)≤Tr B^(p/2)A^pB^(p/2)=u by the Araki–Lieb–Thirring trace inequality at exponent p/2≥1, applied to B² and A². The last identity is the square expansion and (1+d)(1−d)=u², including u=0,1. Undo scaling. The intervals [2^{j+1},2^{j+2}], j≥0, cover [2,∞), so the base interval and (10) prove (1) for every real p in the claim.

For general positive A,B∈S_p choose their respective positive finite spectral truncations A_n,B_n. Their ranges have a common finite-dimensional span at each n. We have A_n→A, B_n→B in S_p and A_n^(p/2)→A^(p/2), B_n^(p/2)→B^(p/2) in S₂ by the summability of their eigenvalue p-powers. The overlaps converge by Hilbert–Schmidt Cauchy–Schwarz, and all norms converge by the triangle inequality. Thus the finite inequality passes to the limit. No simultaneous spectral truncation is assumed.

## 5. Literature checks and scope

* [CFIL, *Inequalities for Lp-norms that sharpen the triangle inequality and complement Hanner's inequality*](https://arxiv.org/abs/1807.05599), §5.2 in the [journal version](https://doi.org/10.1007/s12220-020-00425-y): explicitly proposes the two-positive-operator bound (5.5), proves doubling and dyadic p. The scalar counterpart already holds for all p≥2.
* [Ivanisvili–Mooney, *Sharpening the triangle inequality: envelopes between L² and Lᵖ spaces*](https://arxiv.org/abs/1902.02329): Theorem 2.1, Remark 2.2, and Corollary 2.3 are the classical sharp envelope, its optimality, and the precise numerical comparison to CFIL. We lift their upper envelope, not their arbitrary-sign or reverse assertions.
* [Heinävaara, *Tracial joint spectral measures*](https://arxiv.org/abs/2310.03227), Theorem 1.4 in the arXiv version, supplies (3) for each individual pencil; its norm embedding alone does not identify or bound the noncommutative mixed moment Z. Heinävaara's [22 November 2023 research statement, Question 3.14](https://www.its.caltech.edu/~oeh/research_statement_Otte.pdf) separately identifies this positive Schatten generalization of CFIL as a question. The argument here uses (9) to compare the embedded and operator overlaps before applying the classical envelope and doubling.
* [Audenaert, *Trace inequalities for completely monotone functions and Bernstein functions*, Theorem 4 and Corollary 1](https://arxiv.org/abs/1109.3057) already combines spectral-projector pairings, Golden–Thompson and integral representations for fractional powers. In the range $2\le p\le3$ his resulting power inequality is a **lower** bound with a linear overlap term, not the present sharp upper envelope. [Dinh](https://arxiv.org/abs/2605.17782) already gives the clustered-word upper bound for integer occurrence counts $(n,2)$, including the $(2,2)$ endpoint of (9). The fractional interior of (9) does not follow merely by comparing integer coefficients. In fact, [Cha–Lee](https://arxiv.org/abs/2603.19927) give counterexamples to unrestricted coefficient comparison at $(5,5)$; beyond the base range our proof doubles the norm inequality itself.
* [Chen–de Dios Pont–Ivanisvili–Madrid–Wang, May 2026](https://arxiv.org/abs/2605.05192) treats many functions, including an obstruction to exponent 2 and a three-function estimate. [Chen–Ivanisvili–Madrid–Wang, June 2026](https://arxiv.org/abs/2606.04116) solves Carbery's many-operator ℓ₂ coefficient-norm question, including arbitrary signs. Its Theorem 1.1 uses coefficients α_ij satisfying product-norm bounds, and exponent p'=p/(p−1), not the sharp two-positive-operator envelope for the unsandwiched overlap Z. In particular, on two nearly disjoint normalized commuting functions with overlap z, its right-side multiplier for the p-th power is (1+z^{1/(p−1)})^{p−1} rather than CFIL's (1+z^{2/p})^{p−1}. For p>2 the former bound is strictly larger for 0<z<1.
* [Dinh–Le–Vuong, Oct. 2026](https://arxiv.org/abs/2610.31851) compares a pencil to spectral pinching for the corrected BMV conjecture. Pinching B to E_A(B) is different from the eigenbasis-pair measure (4). [Relative entropy representations via tracial joint spectral measures, Sept. 2026](https://arxiv.org/abs/2609.12547) concerns relative-entropy and variance formulas, not inequality (1). Golden–Thompson and the Araki–Lieb–Thirring trace inequalities are standard; the precise latter specialization is also used in the original CFIL doubling proof.
* Search scope: exact original title, formula (5.5), combinations of the authors' names with Schatten, positive-operator overlap, sharp two-function triangle envelope, noncommutative Carbery, double Laplace, Golden–Thompson, and tracial joint spectral measures, through 18 Nov. 2026. No earlier full proof of (1) or (2) for two positive operators was identified in these targeted checks. This finite search does not establish priority.
