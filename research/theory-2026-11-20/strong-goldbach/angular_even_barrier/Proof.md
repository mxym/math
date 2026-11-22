# An all-rank obstruction to positive-only angular capping

This is an obstruction for a particular fixed-target proof method, **not** a construction of primes or an assertion that any even target fails Goldbach. It applies even if different genuine small-prime marks get different angular cutoffs. It complements the explicit finite-rank obstruction to a single common monotone cutoff.

For \(r\ge1\), write
\[
 \mathcal U_r=\{u_i>0:\sum_{i=1}^r u_i=1\},\qquad
 I_{r,\sigma}(B)=\frac1{r!}\int_{\substack{\mathcal U_r\\u_i\ge\sigma}}
                   B(\boldsymbol u)\frac{du_1\cdots du_{r-1}}{u_1\cdots u_r},
                                                                    \tag{1}
\]
where the last coordinate is eliminated by the sum, and rank one is evaluation at \(u_1=1\). The angular normalization is the one used in the [central actual angular upper](../AngularPrimeDomination.md). All limits of signed all-rank sums here first fix the finitely many kernels, then let the minimum angle \(\sigma\downarrow0\) in the *whole* angular sum. We do not exchange the signed sum with a per-rank limit.

Put \(u_A=\sum_{i\in A}u_i\) and define the linear cusp
\[
 F_r=\sum_{A\subseteq[r]}(-1)^{|A|}|u_A-1/2|.
\]
It is the angular version of the [actual even cusp](../true_even_cusp_rank_tail/Proof.md), whose full normalized reference is \(2\). In particular \(F_r=0\) at odd \(r\).

Here is the class of permitted angular transfers. Fix an integer \(j\ge1\) and a symmetric coefficient \(\Phi(\boldsymbol v)\), with \(\boldsymbol v\in[0,1]^j\), supported at \(V=\sum v_i\le b\) for a constant \(b<1/2\), and satisfying
\[
 |\Phi(\boldsymbol v)|\le C\prod_{i=1}^j v_i.                     \tag{2}
\]
A smooth function vanishing on every zero tag face satisfies (2), by iterated integration of its mixed derivative. Let \(k_{\boldsymbol v}(s)\) be any uniformly bounded measurable family, symmetric in its tag coordinates, for \(s\ge0\), constant in \(s\) on \([0,\eta]\) for a fixed \(\eta>0\), and zero when \(V+s\ge\theta\), with a fixed \(\theta<1/2\). The flat values can vary with the entire tag. Smoothness and the flatness used for actual Bombieri--Vinogradov calibration are compatible with this class, but smoothness is not needed for this model calculation. Define
\[
 Z_r=\sum_{\substack{Q\subseteq[r]\\|Q|=j}}\Phi(\boldsymbol u_Q)
        \sum_{E\subseteq[r]\setminus Q}(-1)^{|E|}
                         k_{\boldsymbol u_Q}(u_E).                 \tag{3}
\]
In particular \(Z_1=0\) since its only possible tag would have length 1. The [actual single-mark transfer](../marked_cusp_finite_rank/Proof.md) is the special case \(j=1\), \(k_v(s)=g(v+s)\). Formula (3) permits general marker-dependent horizons and any finite linear combination of such transfers, of any fixed finite tag sizes.

**Proposition.** Let \(Z\) be any such finite linear combination. Then
\[
 \begin{split}
 \lim_{\sigma\downarrow0}\sum_r I_{r,\sigma}(F_r-Z_r)&=1,\\
 \lim_{\sigma\downarrow0}\sum_{r\ {\rm even}} I_{r,\sigma}(F_r-Z_r)&=1.
 \end{split}                                                        \tag{4}
\]
Consequently the sum of the *positive* angular integrals over even ranks alone is at least 1. In particular, a method which multiplies each such integral by a universal domination factor \(C_*\ge2\), without any signed input or other restriction, cannot certify a strict upper below normalized reference \(2\). This also applies to different prescribed factors at different ranks when all factors on the even ranks are at least 2. In the central range the presently available universal factor \(200/53\) is therefore insufficient for this positive-only method, whatever the chosen transfer.

There is an exact feasible angular comparison, not only a failure of that sufficient upper bound: give the unweighted angular measure density 2 on each even rank and zero on each odd rank, with the same minimum-angle limiting convention for signed scores. This has no rank-one atom, matches the normalized cusp value 2, and gives value zero to every fixed transfer (3). It obeys every domination inequality with factor at least 2 on the even ranks. This does not assert that it models arbitrary Type II information or new genuine shifted-prime lower bounds.

## 1. The two convolution measures

Write \(\nu_\sigma(dt)=\mathbf1_{t\ge\sigma}\,dt/t\), and let
\[
 M_{\pm,\sigma}=\sum_{n\ge0}\frac{(\pm1)^n}{n!}\nu_\sigma^{*n}.
\]
The zeroth term is \(\delta_0\). The sum is finite on each compact interval. Its Laplace transform at \(s>0\) is \(\exp(\pm E_1(\sigma s))\), where \(E_1(v)=\int_v^\infty e^{-t}dt/t\). Uniqueness of the Laplace transform gives the exact formulas
\[
 M_{+,\sigma}=\delta_0+\sigma^{-1}\omega(t/\sigma)dt,qquad
 M_{-,\sigma}=\delta_0+\sigma^{-1}\rho'(t/\sigma)dt,               \tag{5}
\]
where \(\omega\) is Buchstab's function (zero below 1) and \(\rho\) is Dickman's function (one on \([0,1]\)).

For completeness, the delay relations give everything about (5) used below. For \(u\ge1\), \(u\omega(u)=1+\int_0^{u-1}\omega(v)dv\). Taking Laplace transforms of this identity with the zero extension gives
\(-\widehat\omega'(s)=e^{-s}(1+\widehat\omega(s))/s\), so \(1+\widehat\omega(s)=e^{E_1(s)}\). For \(\rho\), the relation \(u\rho'(u)=-\rho(u-1)\) for \(u>1\) gives \((s\widehat\rho(s))'=e^{-s}\widehat\rho(s)\). Since \(s\widehat\rho(s)\to1\) at infinity, \(s\widehat\rho(s)=e^{-E_1(s)}\), which is the transform of \(\delta_0+\rho'(t)dt\). Equivalently, these are the classical Dickman--Buchstab inverse transforms discussed in [the smooth--rough error relation](https://arxiv.org/abs/2604.22058).

The integrated delay relation \(u\rho(u)=\int_{u-1}^u\rho(v)dv\) shows by the first-zero argument that \(\rho\ge0\); its derivative is then nonpositive and \(\rho(u)\le1/\lfloor u\rfloor!\). Its derivative has factorial decay too. Thus \(M_{-,\sigma}\) has mass zero and total variation 2. The relation \(u\omega'(u)=\omega(u-1)-\omega(u)\) for \(u>2\) gives factorial convergence of \(\omega\): if \(D_n=\operatorname{ess\,sup}_{u\ge n}|\omega'(u)|\), then \(D_{n+1}\le D_n/(n+1)\) by integrating \(\omega'\) over the previous unit interval. The elementary bounds \(0\le\omega(u)\le1\) follow from its integral relation, so \(D_2\) is bounded. Since \(E_1(s)+\log s\to-\gamma\), the transform limits are
\[
 \omega(u)=e^{-\gamma}+O(1/\lfloor u\rfloor!),\qquad
 \int_0^\infty\rho(u)du=e^\gamma.                                 \tag{6}
\]
Here \(E_1(s)+e^{-s}\log s=\int_s^\infty e^{-t}\log t\,dt\), with limit \(\Gamma'(1)=-\gamma\). In particular, for \(t\ge c>0\) fixed, \(\sigma^{-1}\omega(t/\sigma)=\sigma^{-1}e^{-\gamma}+O_{c,A}(\sigma^A)\), whereas \(\sigma^{-1}|\rho'(t/\sigma)|=O_{c,A}(\sigma^A)\) almost everywhere, for every fixed \(A\).

## 2. Exact signed factorization at total length one

Let \(H_r=\sum_A(-1)^{|A|}(1/2-u_A)_+\). Direct piecewise linear algebra gives \(F_r=2H_r-\mathbf1_{r=1}\): the difference is the full linear alternating sum, zero for at least two labels and \(-1\) at rank one. On splitting the labels into \(A\) (total \(s\)) and its complement (total \(t\)), the coefficient \(\binom{r}{|A|}/r!\) is exactly \(1/(|A|!\,|A^c|!)\). Out of the convolution relation \(s+t=1\) this gives
\[
 \sum_r I_{r,\sigma}(H_r)=
    \int_{[0,1/2]}(1/2-s)M_{-,\sigma}(ds)
                           \frac{\omega((1-s)/\sigma)}{\sigma}.  \tag{7}
\]
The \(s=0\) atom is included. The \(t=0\) atom contributes nothing, because \(t=1-s\ge1/2\). There is no counting of the full set twice. Replace the last density by \(e^{-\gamma}/\sigma\), with error \(o(1)\) by total variation 2 and (6). Integration by parts, including the atom, gives
\[
 \int_{[0,1/2]}(1/2-s)M_{-,\sigma}(ds)
     =\int_0^{1/2}\rho(s/\sigma)ds\sim\sigma e^\gamma.
\]
Thus (7) tends to 1 and \(\sum I_{r,\sigma}(F_r)\to1\).

For (3), write \(E\) for the marked divisor's other labels and \(C=[r]\setminus(Q\cup E)\). Their sizes \(j,m,n\) give exact multiplicity \(1/(j!m!n!)\) in (1). Their lengths satisfy
\[
                       V+s+t=1,\qquad s=u_E,\quad t=u_C.
\]
Fixing the \(j\) tag angles, the exact summed contribution is
\[
 \frac1{j!}\int_{v_i\ge\sigma}\frac{\Phi(\boldsymbol v)}{\prod v_i}\,d\boldsymbol v
  \int_{[0,\theta-V]} k_{\boldsymbol v}(s)
       M_{-,\sigma}(ds)\frac{\omega((1-V-s)/\sigma)}{\sigma}.    \tag{8}
\]
There is no \(t=0\) term since \(t>1-\theta>1/2\), and the outer integral has finite uniform absolute mass by (2). Replace the last density by \(e^{-\gamma}/\sigma\). The remaining inner integral is superpolynomially small uniformly in the tag: extend the kernel by zero as prescribed, subtract its initial constant from it, use the zero mass of \(M_-\), and bound the variation of that measure on \(s\ge\eta\) by \(\rho(\eta/\sigma)\). This proves \(\sum_r I_{r,\sigma}(Z_r)\to0\).

If the left side is weighted by \((-1)^r\), then the sign assigned to the tag is the constant \((-1)^j\), and in (8) the two convolution signs are interchanged. The density on the long side \(t>1/2\) is now \(\rho'(t/\sigma)/\sigma\), rapidly small by (6). The short measure \(M_{+,\sigma}\) has mass \(O(1/\sigma)\) on \([0,1/2]\) including its atom, which is harmless. Hence the parity-weighted sum also tends to zero. Because the unmarked cusp already vanishes on odd ranks, both assertions of (4) follow. All statements are stable under finite linear combinations.

The positive-part conclusion follows by monotone convergence: every nonnegative coefficient integral increases as \(\sigma\) decreases, and the truncated positive sum is at least its signed counterpart at every \(\sigma\). In particular no absolute convergence of the signed *untruncated* rank sum was used. The even-only comparison gives the asserted obstruction even if one tries to use the negative signed pieces but supplies no genuine lower bounds on them. It is a measure of possible angular data, not a realization by actual reflected primes. A genuine signed estimate or arithmetic restriction beyond these calibrations and marginal caps is still necessary.
