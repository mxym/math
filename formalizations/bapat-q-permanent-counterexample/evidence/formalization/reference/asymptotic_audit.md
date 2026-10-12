# Independent audit of the noncomputational asymptotic argument

Date: 2026-10-08 UTC

Audited source: the proof now published as `asymptotic_existence_proof.md`. This public copy replaces the original local draft path; the mathematical audit is unchanged.

Scope: the existence proof using equidistributed projective rows, a selected maximizing point, a uniquely peaking extra factor, ordering, and contiguous replication. This report does not audit or rely on the finite Gaussian-integer certificate.

## Verdict

**The noncomputational argument is mathematically sound, with the ordinary definition**

\[
P_q(A)=\sum_{\sigma\in S_N}q^{\operatorname{inv}(\sigma)}\prod_i A_{i,\sigma(i)}.
\]

It proves the existence, in some finite dimension, of a rank-two Hermitian positive semidefinite Gram matrix with positive diagonal for which \(P'_1(A)<0\). Consequently its real-valued q-permanent decreases on an interval immediately to the left of 1, including points in \((0,1)\). A sufficiently small positive diagonal perturbation gives a positive definite example.

No convergence of an unbounded empirical moment, independence between the maximizing point and the configuration, nondegeneracy of the maximum, or exchange of the two asymptotic limits is needed. All these possible failure modes can be excluded by the arguments below.

The proof is non-explicit: it provides neither a finite base configuration, a bound on the required repetition count, nor a numerical interior q. Those are not needed for existence.

One statement should be qualified: **\(\pi^2/8\) is the lower asymptotic benchmark supplied by this construction, not a proved universal exact limit of the repetition ratio.** For each fixed base configuration, that exact limit is \(2g(u)/n^4\), which may be larger. The draft's phrase “asymptotic target constant” is harmless if it is intended as a benchmark, but should not be promoted to an equality claim.

## 1. Set-up and conventions

A coefficient row is \(v_i=(a_i,b_i)\), a variable point is a column \(\zeta=(x,y)^T\), and \(\ell_i(\zeta)=v_i\zeta\). This distinction matters because the factor peaking at a unit column \(u\) has coefficient row \(u^*\), not \(u^T\).

All absolute values of homogeneous forms are evaluated on unit representatives of \(\mathbb{CP}^1\). These absolute values are well-defined on the projective quotient. So is \(|S/F|^2\), away from the zeros of F, because changing a unit representative by a phase changes \(S/F\) by a phase of modulus one.

A finite product of nonzero linear forms is a nonzero polynomial and has only finitely many projective zeros. Thus its global maximum modulus \(M\) exists and is strictly positive. In particular, at any maximizing point every factor is nonzero.

## 2. Existence of the required equidistributed configurations

This can be made completely deterministic. For each positive integer r, take \(m=r^2\) unit rows indexed by \(0\leq k,l<r\):

\[
p_k=(k+1/2)/r,\qquad
v_{kl}=\left(\sqrt{p_k},\sqrt{1-p_k}\,e^{2\pi i(l+1/2)/r}\right).
\]

Under normalized Haar measure on \(\mathbb{CP}^1\), \(p=|a|^2\) is uniform on [0,1] and the relative phase is uniform on the circle, independently. The displayed projective grid is therefore equidistributed by ordinary Riemann sums. Endpoint phase identifications cause no problem: the parameterization into projective space is continuous and the boundary has measure zero.

The proof only needs a sequence of such finite configurations; it does not require a configuration for every integer m or n.

## 3. Rotating to a configuration-dependent maximum is legitimate

Let \(\nu_m\) be the empirical projective row measure, with \(\nu_m\Rightarrow\mu\), where \(\mu\) is Haar measure. Select any global maximum \(u_m\) of \(|F_m|\). Choose a unitary matrix \(Q_m\) whose first column is \(u_m\), so \(Q_me_1=u_m\), and make the variable change

\[
\zeta=Q_mw.
\]

The transformed coefficient rows are \(v_iQ_m\), and their product has a maximum at \(w=e_1\). The Gram matrix is unchanged because

\[
(v_iQ_m)(v_jQ_m)^*=v_iQ_mQ_m^*v_j^*=v_iv_j^*.
\]

The right action by any unitary on projective coefficient rows preserves Haar measure. Crucially, this remains enough even though \(Q_m\) depends on the entire configuration.

For completeness, let f be any continuous function on projective space. Along an arbitrary subsequence, compactness of U(2) supplies a subsubsequence with \(Q_m\to Q\). Uniform continuity on the compact product space gives

\[
\sup_{[v]}|f([vQ_m])-f([vQ])|\longrightarrow0.
\]

Consequently

\[
\int f([vQ_m])\,d\nu_m([v])
-
\int f([vQ])\,d\nu_m([v])\to0,
\]

and the second term tends to \(\int f([vQ])\,d\mu=\int f\,d\mu\). Every subsequence has a subsubsequence with this same limit, proving convergence of the full rotated sequence.

No independence assumption was used. No distributional assertion about the locations of \(u_m\) was used.

The transformation laws can be derived directly. Each new linear factor is \(\ell_{i,\rm new}(w)=v_iQ_mw=\ell_{i,\rm old}(Q_mw)\), so

\[
F_{\rm new}(w)=F_{\rm old}(Q_mw).
\]

For every pair of rows, the determinant transforms by

\[
\det\begin{pmatrix}v_iQ_m\\v_jQ_m\end{pmatrix}
=\det\left(\begin{pmatrix}v_i\\v_j\end{pmatrix}Q_m\right)
=\det\begin{pmatrix}v_i\\v_j\end{pmatrix}\det Q_m.
\]

Multiplying by the remaining transformed factors and summing gives

\[
S_{\rm new}(w)=\det(Q_m)S_{\rm old}(Q_mw).
\]

Thus S acquires a determinant phase rather than transforming solely by composition. Haar measure is invariant under \(w\mapsto Q_mw\), and \(|\det Q_m|=1\). Therefore the sphere integrals, Bargmann norms, and corresponding peak modulus ratios in the proof are unchanged.

## 4. The Cauchy chart and its singular point

Write a transformed row as \((a,b)\). Since the chosen peak has nonzero product, each actual finite row has \(a\neq0\). Thus the finite scores \(z=b/a\) and \(t=\operatorname{Re}z\) are defined.

The map \([a:b]\mapsto\operatorname{Re}(b/a)\) is continuous off the single point \([0:1]\). Assigning it any value at that point makes a measurable map whose discontinuity set is Haar-null. The almost-everywhere continuous mapping theorem therefore implies weak convergence of the real empirical measures to its Haar pushforward. Equivalently, for every bounded continuous real test function h, the projective function \(h(\operatorname{Re}(b/a))\) is bounded and continuous outside that null point, which is enough for convergence of integrals.

This is a legitimate weak-convergence statement into the noncompact real line. It implies tightness. It does **not** claim convergence of first moments, and the argument below does not need such convergence.

The complex chart has density

\[
\frac{1}{\pi(1+|z|^2)^2}\,d\operatorname{Re}z\,d\operatorname{Im}z.
\]

Indeed, \(r^2=|z|^2=(1-p)/p\), with p uniform on [0,1] and angle uniform on the circle. Integrating the plane density over the imaginary coordinate gives

\[
f_X(t)=\frac1\pi\int_{\mathbb R}\frac{ds}{(1+t^2+s^2)^2}
=\frac{1}{2(1+t^2)^{3/2}},
\]

and hence

\[
G(t)=\frac12\left(1+\frac{t}{\sqrt{1+t^2}}\right).
\]

These normalizations are correct. In particular, \(E|X|=1\), so \(E|X-Y|\) is finite.

For independent X and Y with this law, Tonelli's theorem applied to

\[
|x-y|=\int_{\mathbb R}|\mathbf1_{x>s}-\mathbf1_{y>s}|\,ds
\]

gives

\[
E|X-Y|=2\int_{\mathbb R}G(s)(1-G(s))\,ds
=\frac12\int_{\mathbb R}\frac{ds}{1+s^2}
=\frac\pi2.
\]

Thus the draft's D1 is correct.

## 5. Truncation gives precisely the required one-sided pair-sum bound

Let \(\rho_m=m^{-1}\sum_i\delta_{t_i}\Rightarrow\rho\), the real marginal above. For each fixed finite T, define

\[
h_T(s,t)=\min\{|s-t|,T\}.
\]

This is bounded and continuous on \(\mathbb R^2\). Product weak convergence gives

\[
\frac1{m^2}\sum_{i,j}h_T(t_i,t_j)
\longrightarrow E h_T(X,Y).
\]

The diagonal terms vanish and the off-diagonal terms occur twice. Therefore, with \(H_m=\sum_{i<j}|t_i-t_j|\),

\[
\frac{H_m}{m^2}\geq
\frac1{2m^2}\sum_{i,j}h_T(t_i,t_j).
\]

Taking a liminf with T fixed, then increasing T to infinity by monotone convergence, yields

\[
\liminf_m\frac{H_m}{m^2}\geq\frac12 E|X-Y|=\frac\pi4.
\]

The order of limits is valid. Escaping outliers can only increase the untruncated nonnegative pair sum, so a missing uniform-integrability argument is not a flaw here. An equality of the empirical untruncated moments has not been proved and is unnecessary.

## 6. One extra factor really does select a unique global peak

Select a unit representative \(u_m\) of the chosen maximizing projective point. Append

\[
\ell_{u_m}(\zeta)=u_m^*\zeta.
\]

For unit \(\zeta\), Cauchy–Schwarz gives \(|\ell_{u_m}(\zeta)|\leq1\), with equality precisely when \([\zeta]=[u_m]\). If \(M_m=|F_m(u_m)|>0\), then

\[
|F_m(\zeta)\ell_{u_m}(\zeta)|\leq M_m
\]

with equality at \([u_m]\), and strict inequality at every other projective point. This proves unique global maximality, even if the old maximizer set was not discrete or the maximum was degenerate.

In the coordinates \(\zeta=Q_mw\), the added row is exactly

\[
u_m^*Q_m=e_1^*=(1,0).
\]

It therefore adds real score zero. If \(n=m+1\), the augmented pair sum is

\[
\widetilde Q_n=H_m+\sum_{i=1}^m|t_i|\geq H_m,
\]

and

\[
\liminf_m\frac{\widetilde Q_{m+1}}{(m+1)^2}
\geq\frac\pi4
\]

because \(m^2/(m+1)^2\to1\). No bound on the extra unbounded summand is required. One could also prove this by weak convergence of the augmented empirical measure; the displayed inequality is simpler.

The factor may be appended before or after choosing coordinates. Its phase depends on the choice of representative of u, but its modulus, unique peak, and all relevant scores are unaffected.

## 7. Ordering yields the Gini score with the stated sign

For the augmented n rows at the peak \(e_1\), every \(a_i\neq0\), and

\[
\frac{S(e_1)}{F(e_1)}
=\sum_{i<j}\frac{a_ib_j-b_ia_j}{a_ia_j}
=\sum_{i<j}(z_j-z_i)
=\sum_i(2i-n-1)z_i.
\]

Order the rows by nondecreasing \(t_i=\operatorname{Re}z_i\). Then

\[
\operatorname{Re}\frac{S(e_1)}{F(e_1)}
=\sum_{i<j}(t_j-t_i)
=\widetilde Q_n.
\]

Ties cause no ambiguity in this equality. Consequently

\[
\frac{g(e_1)}{n^4}
=\frac{|S(e_1)/F(e_1)|^2}{n^4}
\geq\left(\frac{\widetilde Q_n}{n^2}\right)^2,
\]

and

\[
\liminf\frac{g(e_1)}{n^4}\geq\frac{\pi^2}{16}>\frac12.
\]

Permuting the rows does change the q-permanent in general. The proof does not need invariance under that permutation: it is explicitly choosing the ordering of the eventual Gram matrix. The product F, its modulus, and its unique peak are unchanged by row ordering.

The draft's ancillary “best ordering” identity is also valid: write \(|w|=\max_\theta\operatorname{Re}(e^{-i\theta}w)\), exchange the finite maximum over permutations with the maximum over \(\theta\), and apply the rearrangement inequality to the increasing weights \(2i-n-1\). The single fixed real projection used in the proof suffices without this optimization.

## 8. Replication: exact polynomial identity and exact normalization

Now **fix one finite ordered base configuration** satisfying

\[
g(u)>n^4/2
\]

at its unique projective peak. Repeat each row L times contiguously, leaving the order of the n groups unchanged. Set \(N=nL\).

A pair drawn from one group has zero determinant. For each pair of distinct groups, there are \(L^2\) pairs, all carrying the same determinant and the same remaining product. Thus

\[
F_L=F^L,\qquad S_L=L^2F^{L-1}S.
\]

Contiguity is important to preserve the sign of every cross-group determinant in the sum indexed by earlier and later positions. The argument uses exactly this ordering.

For a degree d homogeneous binary polynomial p and normalized projective Haar measure,

\[
\|p\|_B^2=(d+1)!\int|p|^2\,d\mu.
\]

The scalar follows from

\[
\int|x|^{2a}|y|^{2b}\,d\mu
=\int_0^1p^a(1-p)^b\,dp
=\frac{a!b!}{(a+b+1)!},
\]

and different monomials are orthogonal by averaging the relative phase.

The degrees of \(F_L\) and \(S_L\) are N and N−2. Consequently the ratio in the draft is

\[
\begin{aligned}
R_L
&=\frac{L^4(N-1)!}{\binom N2(N+1)!}
\frac{\int|F|^{2L-2}|S|^2\,d\mu}{\int|F|^{2L}\,d\mu}\\
&=\frac{2L^4}{N^2(N^2-1)}
\frac{\int|F|^{2L}g\,d\mu}{\int|F|^{2L}\,d\mu}\\
&=\frac{2L^2}{n^2(n^2L^2-1)}
\frac{\int|F|^{2L}g\,d\mu}{\int|F|^{2L}\,d\mu}.
\end{aligned}
\]

In particular, the apparent additional powers of n in B3 and B4 are correct. There is no missing factor of two or factorial. Since the chosen n is at least 2, all denominators are positive for every positive integer L.

## 9. Concentration remains valid despite poles of S/F

Let \(M=|F(u)|>0\). The unique maximum and compactness imply that for every neighborhood U of u,

\[
\max_{\mathbb{CP}^1\setminus U}|F|<M.
\]

Take U small enough that F is nonzero there and g is continuous there. Choose positive constants a,b with

\[
\max_{U^c}|F|\leq a<b<M,
\]

and a smaller neighborhood V of u, of positive Haar measure, on which \(|F|\geq b\). Then

\[
D_L:=\int|F|^{2L}\,d\mu\geq\mu(V)b^{2L}.
\]

Since S is bounded,

\[
\frac{\int_{U^c}|F|^{2L-2}|S|^2\,d\mu}{D_L}
\leq\frac{\|S\|_\infty^2a^{2L-2}}{\mu(V)b^{2L}}
\longrightarrow0.
\]

Similarly the normalized mass of \(U^c\) under \(|F|^{2L}\,d\mu\) tends to zero. On U, continuity makes \(|g-g(u)|\) uniformly as small as desired by choosing U sufficiently small. Combining these two observations yields

\[
\frac{\int|F|^{2L}g\,d\mu}{\int|F|^{2L}\,d\mu}\longrightarrow g(u).
\]

At zeros of F, the numerator is interpreted as the continuous polynomial modulus \(|F|^{2L-2}|S|^2\); for L=1 the factor \(F^0\) is identically 1. A globally bounded g is not being assumed. The proof needs neither a nonsingular Hessian nor a quantitative Laplace approximation.

Therefore

\[
\lim_{L\to\infty}R_L=\frac{2g(u)}{n^4}>1.
\]

## 10. Quantifiers, endpoint implication, and definiteness

The logical order is:

1. Choose one sequence of equidistributed finite configurations.
2. For each member, choose any maximum, append its uniquely peaking factor, rotate, and order.
3. The liminf inequality implies that every sufficiently late member of this sequence has \(g(u)/n^4>1/2\). In particular, select one finite member with that strict inequality.
4. Hold that member, its n, its F, its S, and its unique maximum fixed.
5. Only now let L tend to infinity. Since the repetition limit is strictly above 1, every sufficiently large finite integer L gives \(R_L>1\).
6. Apply the exact endpoint identity to that finite replicated matrix.

There is no simultaneous-limit assertion or need for estimates uniform in n. More explicitly, fix any \(\eta\) with \(1/\sqrt2<\eta<\pi/4\). The liminf argument gives \(\widetilde Q_n/n^2>\eta\) for all sufficiently late members. Fix one such finite m, hence n=m+1, and only afterward choose L large enough. Its fixed repetition limit exceeds \(2\eta^2>1\).

The endpoint identity used here is

\[
2P'_1(A)=\binom N2\|F_A\|_B^2-\|S_A\|_B^2.
\]

Its inversion-marking derivation has the correct orientation: for i<j and k<l, the marked inversion is \(\sigma(i)=l,\sigma(j)=k\), contributing \(A_{il}A_{jk}\) times the complementary permanent. Subtracting the wedge-minor norm from the two-row permanent expansion produces twice this contribution. Thus \(R_L>1\) gives a strictly negative derivative.

For Hermitian A, \(P_q(A)\) is real for real q: conjugation pairs the term for \(\sigma\) with that for \(\sigma^{-1}\), and \(\operatorname{inv}(\sigma^{-1})=\operatorname{inv}(\sigma)\). Polynomial continuity therefore makes \(P'_q(A)<0\) throughout some interval \((1-\delta,1]\). The interval may be reduced to lie in \((0,1]\), so it gives a monotonicity failure at strictly interior positive q, not merely a formal endpoint problem.

All construction rows are unit rows, so the Gram matrix has diagonal 1 and is Hermitian positive semidefinite. Its rank is at most two. The selected rows cannot all lie in one complex line, since in that case S is identically zero, contradicting the strict score inequality. Hence its rank is exactly two.

Once the finite matrix is fixed, \(P'_1\) depends continuously on its entries. Thus \(A+\varepsilon I\) is positive definite and still has strictly negative endpoint derivative for all sufficiently small positive \(\varepsilon\). The same interior-q reasoning applies. If a unit-diagonal positive definite example is desired, dividing this perturbed matrix by \(1+\varepsilon\) preserves the derivative sign by homogeneity.

## 11. Recommended editorial adjustments

These are clarifications, not repairs to a false argument:

- State the q-permanent definition and the intended Hermitian domain explicitly before naming a conjecture. This proof establishes the mathematical counterexample described above; matching the exact historical formulation is a separate source-scope question.
- Use distinct symbols for a variable column and the coefficient ratio \(b_i/a_i\).
- Specify a unit representative when writing \(u^*\zeta\), and retain the conjugation in that row.
- State that the coefficient-row transformation is \(v_i\mapsto v_iQ\), with \(Qe_1=u\). Mention the harmless factor \(\det Q\) in S if transformation laws are spelled out.
- Make explicit that the base configuration is fixed before the replication limit.
- Refer to \(\pi^2/8\) as a lower asymptotic benchmark unless additional upper bounds or moment convergence are proved.
- Do not infer any numerical dimension, repetition count, exact rate, minimality, or untruncated empirical-moment equality from this argument.

**Bottom line:** no fatal gap was found. The peak-selection, projective weak-convergence, truncated pair-score, and replication steps do establish the stated finite existence result independently of the computational certificate.
