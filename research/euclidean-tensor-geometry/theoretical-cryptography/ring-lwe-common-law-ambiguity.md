# Common-law ambiguity radii for simultaneously labeled dyadic location models

Consider one abstract ring-valued random-design location observation, under very broad wrapped noise. How much enlargement of the probability model is needed for a *single law* to be consistent with every label in a specified set? This is different from the largest pairwise distance. For subexponential label sets we obtain a universal sharp limit, without independence of the label scores. At exponential size we give two same-size ideal label sets with strictly different limits. We also distinguish averaging the design from imposing the design marginal as an exact constraint.

## 1. Model and theorem

Let \(q\ge3\) be any fixed odd integer, \(d\) tend to infinity through powers of two, \(R_d=(\mathbb Z/q\mathbb Z)[X]/(X^d+1)\), and \(b=\beta/d\) for a fixed \(\beta>0\). The wrapped density on \(\mathbb T=\mathbb R/\mathbb Z\) is
\[
f_b(y)=\sum_{h\in\mathbb Z} b^{h^2} e^{2\pi i h y}.
\]
For label \(s\in R_d\), let \(P_s\) be the probability law of \((A,Y)\), where \(A\) is uniform on \(R_d\), and conditional on \(A\) the density of \(Y\) against Haar measure on \(\mathbb T^d\) is
\[
p_s(A,y)=\prod_{j=1}^d f_b(y_j-(As)_j/q).
\]
The displayed \(p_s\) is also the joint density relative to *uniform design times Haar*, without an extra \(q^{-d}\). Fix a nonempty deterministic set \(\mathcal S_d\subset R_d\), not selected after seeing \(A\). Define the common-law radius
\[
\epsilon_*=\inf\{\epsilon\in[0,1]: \exists\, Q\ {\rm probability}\
       \text{with }Q\ge(1-\epsilon)P_s\text{ for every }s\in\mathcal S_d\}.       \tag{1}
\]
Order here is measure domination. This is the intersection of Huber probability neighborhoods, not a guarantee for any sample-editing process or a claim about an implementation.

Write \(M_A=\int_{\mathbb T^d}\max_{s\in\mathcal S_d}p_s(A,y)\,dy\), \(M=\mathbb E_A M_A\). Then:
* Exactly \(\epsilon_*=1-M^{-1}\). If the common law is additionally required to retain the uniform marginal for \(A\) *exactly*, the corresponding radius is \(\epsilon_*^{\rm des}=1-(\max_A M_A)^{-1}\).
* For \(m=|\mathcal S_d|\ge2\) fixed, and \(G_1,\ldots,G_m\) independent standard Gaussians,
  \[
  \epsilon_*=\frac{\sqrt 2\,\beta}{\sqrt d}
       \big(\mathbb E\max_{j\le m}G_j+o(1)\big).                             \tag{2}
  \]
* If \(L_d=\log|\mathcal S_d|\to\infty\) and \(L_d=o(d)\), then
  \[
  \epsilon_*=(2\beta+o(1))\sqrt{L_d/d}.                                       \tag{3}
  \]
  Both (2) and (3) are uniform over deterministic sets of the indicated sizes. The same limits hold in probability over \(A\) for the conditional radius \(1-M_A^{-1}\), but not necessarily for \(\epsilon_*^{\rm des}\).
* Choose a sufficiently large fixed dyadic base \(d_0\) as in §3. For an ideal \(J_0\triangleleft R_{d_0}\), take any coset of its scalar extension \(J\triangleleft R_d\) as \(\mathcal S_d\), and set
  \[
  c(J_0)=\mathbb E_{U\in\mathbb T^{d_0}}\max_{v\in J_0}
               \sum_{j=1}^{d_0}\cos(2\pi(U_j-v_j/q)).
  \]
  Both radii converge to \(1-\exp[-2\beta c(J_0)/d_0]\). In particular the full-ring limit is \(1-\exp[-2\beta(q/\pi)\sin(\pi/q)]\).
* For two labels and \(J=(s-t)R_d\ne0\), use its base ideal \(J_0\) from §3 and let
  \[
    v(J_0)=1-\min_{u\in J_0}\ d_0^{-1}\sum_j\cos(2\pi u_j/q).
  \]
  Then, uniformly over the two labels,
  \[
  \epsilon_*=(\beta+o(1))\sqrt{\frac{2}{\pi d}},
  \qquad \epsilon_*^{\rm des}=(\beta+o(1))\sqrt{\frac{2v(J_0)}{\pi d}}.         \tag{4}
  \]
  Here \(v(J_0)>1\); for a unit difference it is \(1+\cos(\pi/q)\).

There is no general formula here for arbitrary sets with \(\log|\mathcal S_d|\) proportional to \(d\). Section 7 shows that in this regime even the leading limit for ideal cosets can depend on more than cardinality.

## 2. Exact envelope identity

With a common dominating reference measure, the least measure dominating all the \(P_s\) is given by their pointwise maximum density. Indeed the measurable finite regions where a particular index first attains the maximum are disjoint, so even a candidate \(Q\) with a singular part must dominate the maximum by summing the individual domination inequalities on those regions. The dominating subprobability of mass \((1-\epsilon)M\) can be extended to a probability if and only if that mass is at most 1. If the marginal of \(A\) is fixed, the same argument is necessary on each design fiber with its prescribed mass and sufficient by extending separately on each fiber. All fibers have positive weight. This proves both identities, including the attained endpoint. For two densities the integral of the maximum is \(1+\operatorname{TV}(P_s,P_t)\), with \(\operatorname{TV}=\frac12\|\cdot\|_1\).

This envelope integral is the Shtarkov normalization constant from [Shtar'kov's original paper](https://www.mathnet.ru/php/archive.phtml?jrnid=ppi&option_lang=eng&paperid=811&wshow=paper), here used as a common-majorization statistic. Compare [Huber's probability-neighborhood model](https://doi.org/10.1214/aoms/1177699803) and the [Chen–Gao–Ren two-point TV formulation](https://arxiv.org/pdf/1511.04144). These give the probability model and generic normalization perspectives. The work below concerns the asymptotics of this envelope for the specific growing ring families.

## 3. Uniform coherence from the fixed base

For an odd prime \(p\mid q\), the degree of every irreducible factor of \(X^d+1\) over \(\mathbf F_p\) is \(\operatorname{ord}_{2d}(p)\), since each root has exact order \(2d\). This degree doubles with \(d\) past a fixed dyadic threshold: for \(n\ge1\), \(v_2(p^{2^n}-1)=v_2(p^2-1)+n-1\) by factoring successive differences of squares, whose new factor has 2-adic valuation one. Take a common \(d_0\) past the threshold (or at a base from which doubling already holds). With \(D=d/d_0\), each factor \(g_i\) at \(d_0\) gives the factor \(g_i(X^D)\) at \(d\): it divides \(X^d+1\) and its degree is already the common degree of an irreducible factor there. For prime-power modulus \(p^e\mid q\), the unique monic Hensel factorization of the pairwise coprime base factors likewise substitutes \(X^D\). Each factor ring is local with maximal ideal \(p\); every ideal is a power of \(p\) (factor the minimum coefficient valuation from a nonzero element to obtain a unit). Thus all ideals at \(d\), after CRT over the prime powers, are extensions from \(d_0\). Moreover, grouping coefficients by their index modulo \(D\) gives the additive direct product of \(D\) copies of a base ideal \(J_0\). To see the product statement directly, \(R_d\) is free of rank \(D\) over \(R_{d_0}\) via \(X_{\rm base}\mapsto X^D\); in each lifted factor ring \(p^j\) extends from the corresponding base factor, and CRT idempotents extend as well.

For nonzero \(\Delta=s-t\), the random element \(A\Delta\) is uniform in the image ideal \(J=\Delta R_d\). At the fixed base a nonzero ideal projects in each coordinate to a nontrivial additive subgroup of \(\mathbb Z/q\mathbb Z\): some coordinate has nonzero image, and multiplication by \(X_{\rm base}\) gives the signed cyclic rotation. The average of the fundamental character over each such subgroup is zero. Therefore, uniformly in \(\Delta\ne0\), the coherence
\[
   \gamma_{s,t}(A)=d^{-1}\sum_j\cos(2\pi (A(s-t))_j/q)
\]
is an average of \(D\) independent real block averages in \([-1,1]\), each of mean zero. Hoeffding's inequality gives
\[
   \Pr_A(|\gamma_{s,t}|>\xi)\le2\exp(-D\xi^2/2).               \tag{5}
\]
Also \(A\) is a unit except with probability \(\exp(-\Omega_q(d))\): each local nonunit event is zero reduction in a residue field of cardinality exponential in \(d\), and the number of factors is fixed. The proof uses no primality assumption on \(q\).

## 4. Small lists

Let \(U_j\) be independent Haar variables and, for fixed \(A\), define
\[
 C_s=\sum_j\cos(2\pi(U_j-(As)_j/q)),\qquad T=\max_s C_s.
\]
Each \(C_s\) is centered with variance \(d/2\); a distinct pair has covariance \(d\gamma_{s,t}(A)/2\). Because \(f_b=1+2b\cos(2\pi y)+O(b^4)\) uniformly,
\[
   V:=\max_s\log p_s(A,U)=2bT+O(db^2),\qquad |V|\le C_\beta.                  \tag{6}
\]

For fixed \(m\), take \(\xi_d=d^{-1/4}\) in (5) and union-bound pairs. Conditional on all coherences being small, the normalized vector \((C_s/\sqrt{d/2})_s\) converges to independent standard Gaussians. The elementary triangular CLT applies to every fixed linear combination: centered independent coordinate summands are uniformly bounded before normalization, and their normalized variances converge to the proposed diagonal variance. This gives uniform convergence for all good \(A\) by the sequential characterization of convergence. Uniform integrability follows since the squared maximum in absolute value is bounded by the sum of squares with expected value \(md/2\). Bad \(A\)'s contribute \(o(\sqrt d)\) to the integrated conditional mean since the same moment bound holds for every \(A\). Finally \(\mathbb E V^2=O(db^2)=O(d^{-1})\), and on the bounded range in (6) the exponential differs from \(1+V\) by \(O_\beta(V^2)\). We get \(M-1\sim 2b\sqrt{d/2}\,\mathbb E\max G_j\) and the corresponding conditional limit. For \(m=2\), \(\mathbb E\max(G_1,G_2)=\mathbb E|G_1-G_2|/2=1/\sqrt\pi\).

## 5. Subexponential lists

Write \(L=L_d\), \(a_d=\sqrt{dL}\), and \(\xi=(L/d)^{1/4}\). By (5) the union bound \(2\exp(2L-D\xi^2/2)=o(1)\) makes all pair coherences \(o(1)\) at good \(A\). Fix such an \(A\) temporarily. For fixed real \(u,v\), independent Haar coordinates, boundedness, and the covariance formula give, uniformly among good phases and distinct labels,
\[
 \log\mathbb E e^{\sqrt{L/d}(u C_s+v C_t)}
       =L\big((u^2+v^2)/4+O_{u,v}(\xi+\sqrt{L/d})\big).                    \tag{7}
\]
In fact the exact quadratic term is \(L(u^2+v^2+2uv\gamma_{s,t})/4\). The summed cubic remainder is \(O(L^{3/2}/\sqrt d)\). The one-label version has the same expansion with \(v=0\) and no coherence term.

For every fixed \(x>0\),
\[
 \Pr(C_s\ge x a_d)=\exp[-(x^2+o(1))L],\qquad
 \Pr(C_s,C_t\ge x a_d)\le\exp[-(2x^2-o(1))L].                              \tag{8}
\]
For upper bounds use \(u=2x\) (and \(v=2x\) for the pair). For the one-label lower bound tilt by \(u=2(x+\eta)\) with any fixed \(\eta>0\). Under the tilted law, differentiation of the scalar bounded-variable Taylor expansion gives mean \((x+\eta+o(1))a_d\) and variance \(O(d)\). Thus the tilted probability of \([x a_d,(x+2\eta)a_d]\) tends to one. Untilt on that interval and let \(\eta\downarrow0\) to obtain the stated log rate. The one-label law is in fact independent of all phases. The essential distinction in (8) is that dependence across labels is allowed; only the independent coordinate factors are tilted.

For \(x>1\) the union bound gives \(\Pr(T\ge x a_d)=o(1)\). For \(0<x<1\), let \(N_x\) count labels attaining \(x a_d\). The first and second moments in (8) give
\[
  \frac{\mathbb E N_x^2}{(\mathbb E N_x)^2}\le\exp(o(L)),\qquad
  \Pr(T\ge x a_d)\ge\exp(-o(L)).
\]
The diagonal term is \(1/\mathbb E N_x\), which decays exponentially at this \(x\). The count estimate alone is not convergence in probability. For every fixed \(A\), changing one Haar coordinate changes \(T\) by at most 2. The bounded difference inequality, or the corresponding bounded-increment martingale estimate, gives
\[
 \Pr(|T-\mathbb E[T\mid A]|\ge \eta a_d\mid A)
                \le2\exp(-\eta^2L/2).                           \tag{9}
\]
If the conditional mean were below \((x-\eta)a_d\) along any sequence of good \(A\)'s, (9) would contradict the subexponential lower probability. Varying \(x<1\) and \(\eta>0\) proves the lower limit. The upper probability and the same concentration bound prove the upper limit. Thus \(T/a_d\to1\) in probability uniformly over good designs.

For completeness, all designs have a common integrable bound on the normalized second moment: the positive tail at \(w a_d\) is at most \(\min(1,\exp[L-w^2L/2])\) by Hoeffding plus the union bound. The negative part of the maximum is bounded in absolute value by the negative part of any selected single score, of second moment at most \(d/2\). This also yields uniform integrability for the first moment and shows bad designs contribute \(o(a_d)\). By (6), \(\mathbb E V=2b a_d(1+o(1))\), and \(\mathbb E V^2=O(b^2 dL+d^2 b^4)=o(b a_d)\). Expanding the bounded exponential yields \(M-1\sim2b a_d\), and gives the same estimate for \(M_A-1\) on good designs.

## 6. Design constraint and product-ideal sets

For two labels, expand the densities using (6) without the maximum (each individual log likelihood is uniformly bounded). Uniformly in \(A\), the error in the first-order pair TV formula is \(O(db^2)\) because each individual score has second moment \(d/2\). In detail,
\[
 M_A-1=\operatorname{TV}\big(P_s(\cdot\mid A),P_t(\cdot\mid A)\big)
       =b\,\mathbb E|C_s-C_t|+O(db^2).
\]
The difference score has variance \(d(1-\gamma_{s,t}(A))\). Uniformly over all phase configurations,
\[
 d^{-1/2}\mathbb E |C_s-C_t|
   =\sqrt{(2/\pi)(1-\gamma_{s,t}(A))}+o(1).
\]
To verify uniformity take any sequence, then a subsequence on which \(1-\gamma\) converges. For a positive limit apply the bounded-summand triangular CLT and the second-moment bound; for limit zero the same second moment directly gives convergence to zero. The attainable differences \(A(s-t)\) are precisely \(J\), so the minimum coherence is achieved by choosing in every block a minimizer in \(J_0\). The minimum is strictly negative: its uniform mean is zero and the zero word gives value 1. Maximizing \(M_A\) yields (4). For the full ideal the minimum individual cosine is \(-\cos(\pi/q)\) as \(q\) is odd.

For an ideal coset \(s_0+J\), the shift by \(A s_0\) does not affect the Haar integral and \(AJ\subseteq J\). Thus \(M_A\) is bounded by the envelope for \(J\) with all its shifts available; equality holds whenever \(A\) is a unit, and hence at the supremum. The all-shifts envelope factors into \(D\) identical block envelopes by §3. Its single block integral is \(1+2b\,c(J_0)+O_{d_0}(b^2)\) by uniform first-order expansion on the fixed block. Consequently the supremum of \(M_A\), and also its mean (since the unit probability is \(1-\exp(-\Omega(d))\)), converge to \(\exp(2\beta c(J_0)/d_0)\). In the full ring the scalar maximum cosine integrates to \((q/\pi)\sin(\pi/q)\) by integrating the nearest-grid-point phase on the circle.

## 7. Cardinality does not determine the exponential-size limit

Take \(q=25\), base \(d_0=2\). The degree-doubling property for \(p=5\) holds starting here: \(\operatorname{ord}_{2d}(5)=d/2\) for all dyadic \(d\ge2\), by the same valuation formula. The ring at the base factors using roots \(7,-7\) modulo 25. Consider the two coordinate-vector ideals
\[
 J_{\rm lin}=\{(a,7a):a\in\mathbb Z/25\mathbb Z\},\qquad
 J_{\rm prod}=5(\mathbb Z/25\mathbb Z)^2 .
\]
The first is the evaluation kernel at \(X=7\), since \(7^2=-1\bmod25\); the second is the product ideal. Both have 25 elements and their extensions have exactly \(5^d\) labels for every \(d\). Put \(\operatorname{sinc}(z)=\sin(z)/z\). The product alphabet gives \(c(J_{\rm prod})/2=\operatorname{sinc}(\pi/5)\).

The phase lattice over \(J_{\rm lin}\) is \(\mathbb Z^2+(1,7)\mathbb Z/25\) (the last term denotes multiples of the vector \((1,7)/25\)). It is generated by \((4,3)/25\) and \((-3,4)/25\), which belong to it and have determinant \(1/25\), its covolume. These are perpendicular of equal length \(1/5\), so the Euclidean nearest lattice point has a residual uniform in the rotated side-\(1/5\) square under Haar input mod \(\mathbb Z^2\). This is just an admissible phase for a lower bound on the cosine envelope, not an assertion that it maximizes the cosine objective. Integrating either coordinate cosine in the rotated square gives
\[
  c(J_{\rm lin})/2
     \ \ge\ \operatorname{sinc}(4\pi/25)\operatorname{sinc}(3\pi/25)
     \ >\ \operatorname{sinc}(\pi/5).
\]
For the strict inequality use the Euler sine product at \(x=4\pi/25\) and \(y=3\pi/25\): \(x^2+y^2=(\pi/5)^2\), and for every \(n\ge1\), \((1-x^2/(\pi n)^2)(1-y^2/(\pi n)^2)>1-(x^2+y^2)/(\pi n)^2>0\). The ratios are all greater than one and converge as a product, so already the first gives strictness. The exponential-size limits differ by §6, despite identical cardinalities.

The note is a one-observation probability comparison with independently wrapped coordinates at \(b=\beta/d\). It does not analyze attacks, data handling in a deployed system, computational access, or the converse question of designing a robust procedure below these radii. The distinction between the annealed conditional envelope and the worst design in (4) is part of the result, not interchangeable notation.
