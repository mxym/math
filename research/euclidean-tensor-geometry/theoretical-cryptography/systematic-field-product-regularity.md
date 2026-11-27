# Sharp regularity profiles for factor-independent noise in a systematic finite-field product

## Statement and scope

The regularity argument in [Lyubashevsky–Peikert–Regev, *A Toolkit for Ring-LWE Cryptography*, §7](https://web.eecs.umich.edu/~cpeikert/pubs/toolkit.pdf) analyzes uniformity of a systematic ring-linear map on lattice-Gaussian inputs. Here we fix a deliberately narrower, independent-factor model and determine the **actual total-variation critical window**, including a transition between two qualitatively different limits.

Let \(F=\mathbb F_q\) be fixed, \(k\ge1\) fixed, and \(g\to\infty\) the number of independent factors of the abstract product \(F^g\). In each factor \(j\), independently choose \(h=h(g)\) columns \(B_{j,i}\) uniform on \(F^k\). Let \(X_{j,0}\in F^k\) have independent coordinates of law \(\chi\) on \(F\), and independently draw scalars \(X_{j,1},\ldots,X_{j,h}\sim\chi\), all independent across \(j\) and of the public columns. Define the standalone output
\[
Y_j=X_{j,0}+\sum_{i=1}^h B_{j,i}X_{j,i}.
\]
Compare the joint law of \((B,Y)\) to \((B,U)\) with the **same** public \(B\) and independent uniform \(U\in(F^k)^g\). Put \(D_g(B)=d_{\rm TV}(\mathcal L(Y\mid B),U)\); joint TV is \(\mathbb E_B D_g(B)\).

For a fixed \(\chi\) that is neither uniform on \(F\) nor a point mass, set \(a=\sum_x\chi(x)^2\in(1/q,1)\). The sharp window variable is \(g a^h\):
* If \(g a^h\to0\), \(D_g(B)\to0\) in probability. If \(g a^h\to\infty\), \(D_g(B)\to1\) in probability.
* If \(g a^h\to t\in(0,\infty)\) and \(\chi\) is not uniform on an additive coset, the limit in probability is
  \[
  2\Phi\!\left(\tfrac12\sqrt{((qa)^k-1)t}\right)-1 .
  \]
* If \(\chi\) is uniform on a nontrivial proper additive coset, the same scale instead has a random Poisson conditional limit, computed in section 3. Section 4 gives an explicit intermediate profile for noise approaching such a coset law.

This is a statistical comparison of positive simulations with **independent CRT-coordinate inputs** in a finite product model. A canonical lattice Gaussian generally does not satisfy this independence assumption. In particular this is not a new guarantee for arbitrary number fields, a concrete parameter set, a key recovery method, or an analysis of an operating cryptosystem.

## 1. Per-factor Fourier identity and the common threshold

Fix a nontrivial additive character \(\psi\) of \(F\), and use \(\widehat\chi(w)=\mathbb E[\psi(wX)]\). The characters indexed by \(F\) are distinct by the nondegenerate multiplication pairing. Let
\[
a=q^{-1}\sum_w|\widehat\chi(w)|^2,\qquad
b=q^{-1}\sum_w|\widehat\chi(w)|^4,\qquad
S=(qa)^k-1 .
\]
Parseval gives the stated collision probability \(a\), and \(b\le a\). The Fourier coefficient of one conditioned output at \(\omega\in F^k\) is
\[
\widehat P_{B_j}(\omega)=
\prod_{\ell=1}^k\widehat\chi(\omega_\ell)
\prod_{i=1}^h\widehat\chi(\omega\cdot B_{j,i}).
\tag{1}
\]
For each \(\omega\ne0\), its dot product with an independent uniform column is uniform on \(F\), regardless of the other characters. Let \(v_j=\chi^2(P_{B_j}\Vert U_{F^k})\), which equals the sum of the squared moduli of the nontrivial coefficients. Equation (1) gives
\[
\mathbb E v_j= S a^h,\qquad
\mathbb E v_j^2\le(q^k-1)^2 b^h .
\tag{2}
\]
The second bound follows by squaring each summand and using Cauchy–Schwarz on the at most \(q^k-1\) terms; no independence of different frequencies is assumed. Indeed an individual squared summand has expectation at most \(b^h\). By independence of the coefficient blocks the exact mean joint chi-square divergence is \((1+Sa^h)^g-1\): conditional product chi-square plus one is \(\prod_j(1+v_j)\), and averaging is legitimate because the public law agrees in both experiments.

If \(ga^h\to0\), this last formula and the chi-square bound on TV prove the first limit. For \(ga^h\to\infty\), put \(V_g=\sum v_j\). Its relative variance is at most
\((q^k-1)^2 b^h/(g S^2 a^{2h})\), tending to zero since \(b\le a\) and \(ga^h\to\infty\). Thus \(V_g\to\infty\) in probability. To turn this into TV, write \(1+\delta_j=dP_{B_j}/dU_{F^k}\), so \(-1\le\delta_j\le q^k-1\), \(\mathbb E_U\delta_j=0\), and \(\mathbb E_U\delta_j^2=v_j\). The affinity between one factor's laws satisfies
\[
1-\mathbb E_U\sqrt{1+\delta_j}
=\tfrac12\mathbb E_U(\sqrt{1+\delta_j}-1)^2
\ge\frac{v_j}{2(\sqrt{q^k}+1)^2}.
\]
The product affinity tends to zero when \(V_g\to\infty\), and TV is at least one minus affinity. This proves the other side, even when the conditional densities do not uniformly approach Haar in every local factor.

## 2. Gaussian likelihood limit for \(b<a\)

Assume \(ga^h\to t\in(0,\infty)\), so \(h\to\infty\). If \(b<a\), (2) implies \(V_g\to S t\) in probability and \(\sum_j v_j^2\to0\) in probability, since \(g b^h\to0\). Fourier inversion and Cauchy–Schwarz give
\(\|\delta_j\|_\infty\le\sqrt{q^k-1}\sqrt{v_j}\), so the maximum of these sup norms tends to zero in probability.

For any deterministic sequence of public arrays satisfying those two limits, consider the conditional log likelihood \(\sum_j\log(1+\delta_j(U_j))\) under independent uniform outputs. The centered linear sum has total variance tending to \(St\), and converges normally by the triangular-array central limit theorem, because every summand is uniformly small. The sum of squares tends in probability to \(St\); its variance is at most \((\max_j\|\delta_j\|_\infty^2)V_g\). The Taylor remainder is likewise bounded in mean by a constant times \(\max_j\|\delta_j\|_\infty V_g\). Thus the log likelihood tends to \(\mathcal N(-St/2,St)\). Using the bounded continuous TV expression \(x\mapsto(1-e^x)_+\) and integrating against this normal law gives the displayed Gaussian limit. The conclusion holds in probability over the public matrix, for example by extracting an almost surely convergent subsequence of \(V_g\) and the maximal sup norm from any subsequence.

For completeness, \(b=a\) is exactly the additive coset case. Equality means every Fourier modulus is either zero or one. Let \(H\) be the additive subgroup generated by differences of points in the support of \(\chi\). The modulus is one exactly on \(D=H^\perp=\{w:\psi(wh)=1\text{ for every }h\in H\}\), since a unit complex variable has mean of modulus one only if it is constant. On \(D\) the phase is that of any point of the support coset; if every other coefficient vanishes, Fourier inversion gives the uniform law on that coset. Conversely such a coset law clearly has only these moduli. The excluded cases Haar and a point mass are respectively always uniform output and conditionally deterministic output (TV \(1-q^{-kg}\)).

## 3. Poisson defects, with block size from a subfield

Now let \(\chi=U_{c+H}\) where \(H\) is a nontrivial proper additive subgroup. Set \(D=H^\perp\), \(u=|D|\), so \(a=u/q\). The nonzero Fourier frequencies surviving in one factor are precisely
\[
\{\omega\in D^k\setminus\{0\}: \ \omega\cdot B_i\in D\text{ for every }i\}.
\tag{3}
\]
The conditional output is uniform on an affine additive subspace: the sum of independent uniform affine subspace variables is uniform on their affine sum, by translation invariance. Its annihilator consists of zero and the frequencies in (3).

Let
\[
K=\{0\}\cup\{s\in F^\times:sD=D\},\qquad Q_0=|K|.
\]
This is a subfield. The nonzero elements are multiplicatively closed and invertible within the set; if \(s,t\) preserve \(D\) then \(s+t\) maps \(D\) into itself, and when nonzero its injectivity on the finite set \(D\) makes it onto. Thus \(D\) is a \(K\)-vector space. The nonzero vectors in \(D^k\) divide into
\(\kappa=(u^k-1)/(Q_0-1)\) lines, counting each \(K\)-line without zero once. All nonzero vectors in one such line have identical survival conditions; each line survives with probability \(a^h\).

If two lines are distinct, there are two cases. If their representatives are \(F\)-linearly independent, their two dot products with one uniform column are independent, so the per-column simultaneous probability is \(a^2<a\). If they are proportional over \(F\) with ratio \(s\notin K^\times\), the per-column probability is \(|D\cap s^{-1}D|/q<a\), since unequal subsets of size \(u\) intersect in fewer than \(u\) points. Because \(F,k\) are fixed, these intersection rates are bounded by a common \(\rho<a\). Therefore the chance of exactly one surviving line in one factor is \(\kappa a^h+O(\rho^h)\), and the chance of two or more is \(O(\rho^h)\), by summing the pair intersections. At \(ga^h\to t\) there is no multiple defect in any factor with probability tending to one, and the number \(N_g\) of factors with one surviving line tends to \(\mathrm{Poisson}(\kappa t)\) by the elementary binomial rare-event limit.

Every single defect has an annihilator of size \(Q_0\), so its conditional uniform affine subspace occupies a fraction \(1/Q_0\) of the full output. On the event without multiple defects the conditional law is uniform on a product of affine subspaces of total fraction \(Q_0^{-N_g}\). Thus
\[
D_g(B)\ \Longrightarrow\ 1-Q_0^{-\mathrm{Poisson}(\kappa t)},\qquad
\mathbb E_B D_g(B)\longrightarrow
1-\exp[-\kappa t(1-Q_0^{-1})].
\tag{4}
\]
This is not the deterministic Gaussian limit of section 2. Even in the case where a first moment such as (2) has the same fixed scaling, it need not predict the shape of the conditional TV distribution.

## 4. An exact near-subgroup crossover

Retain the nontrivial proper \(H\) and \(c\) from section 3 but choose a triangular family
\[
\chi_h=(1-\epsilon_h)U_{c+H}+\epsilon_h U_F,\qquad
0\le\epsilon_h<1,\quad\epsilon_h\to0 .
\]
Let \(a_h\) be its collision probability and set \(a_0=u/q\), \(\gamma=1-1/u\). The nonzero Fourier support is unchanged, and every nonzero retained source coefficient has amplitude \(1-\epsilon_h\), so
\[
a_h=q^{-1}[1+(u-1)(1-\epsilon_h)^2],\qquad
b_h=q^{-1}[1+(u-1)(1-\epsilon_h)^4].
\]
Assume \(ga_h^h\to t\in(0,\infty)\). If \(h\epsilon_h\to\tau\in[0,\infty)\), let \(r=e^{-\gamma\tau}\in(0,1]\). Then \(ga_0^h\to t/r^2\), by expanding \(\log(a_h/a_0)=-2\gamma\epsilon_h+O(\epsilon_h^2)\).

Multiple-line failures are still negligible since the support condition (3) and the rate \(\rho<a_0\) are unchanged. Conditional on any given line surviving, its representative's dot product in each column is independent uniform on \(D\). The count of nonzero such products therefore has distribution \(\mathrm{Binomial}(h,\gamma)\); every nonzero representative on the line has the same count and the same number of nonzero systematic coordinates. The coefficient amplitude on that line is \((1-\epsilon_h)\) to the power of this total count. It tends to \(r\) in probability on every surviving line, jointly in the sense that the probability of **any** surviving line with amplitude away from \(r\) tends to zero. Indeed, for a fixed tolerance, bound by the expected number \(g\kappa a_0^h\) of surviving lines times the conditional binomial-tail probability, which tends to zero by the law of large numbers. The Fourier phases are from the fixed affine translation \(c\) times the corresponding column sum and systematic entries, and do not affect TV to Haar.

Thus each unique defect is a mixture of Haar and Haar on its affine subspace, of weights \(1-r_j,r_j\) with \(r_j\) close to \(r\), whose density differs from one only through the indicator of a fraction \(1/Q_0\) of the space. The limiting number of these defects is \(N\sim\mathrm{Poisson}(\kappa t/r^2)\). For \(n\) such defects at amplitude \(r\) define
\[
F_{n}(r)=\tfrac12\mathbb E\bigl|
(1+(Q_0-1)r)^J(1-r)^{n-J}-1\bigr|,
\qquad J\sim\mathrm{Binomial}(n,1/Q_0).
\]
This is the exact finite product TV from the uniform reference, with zeroth powers interpreted as one. The count is tight and the law is continuous in the amplitudes for bounded counts (a finite product), so
\[
D_g(B)\Longrightarrow F_{N}(r),\qquad
\mathbb E D_g(B)\longrightarrow\mathbb E F_N(r).
\tag{5}
\]
At \(\tau=0\) this recovers (4). If instead \(h\epsilon_h\to\infty\), then \((b_h/a_h)^h\to0\) since \(\log(b_h/a_h)=-2\gamma\epsilon_h+O(\epsilon_h^2)\). The proof of section 2 applies directly with these varying coefficients and \(S_h\to u^k-1\), giving the deterministic Gaussian limit \(2\Phi(\sqrt{(u^k-1)t}/2)-1\). This also matches the \(r\to0\) limit of (5): \(Nr^2\to\kappa t\) in probability, each local centered density perturbation has variance \((Q_0-1)r^2\), and the same likelihood central limit argument applies. Thus an additive coset perturbation at inverse-column scale already yields intermediate compound-Poisson profiles, rather than an abrupt jump between the two fixed-law limits.

## Relation to existing regularity and reproduction

Toolkit §7 and [Dachman-Soled et al., *Towards a Ring Analogue of the Leftover Hash Lemma*](https://doi.org/10.1515/jmc-2020-0076) give regularity for systematic ring maps under Gaussian hypotheses. [Liu–Wang, *Rounding in the Rings*](https://iacr.org/archive/crypto2020/12171112/12171112.pdf) treats ring leftover hashing with ideal-quotient entropy conditions. Those results should not be replaced by an independent factor assumption. The present calculation uses a restricted product structure to obtain exact **conditional** critical-window profiles under mutually independent factor coefficients, beyond a sufficient mean chi-square upper bound. No exhaustive priority claim is made for the underlying Fourier identities or the use of a Poisson limit.

Run **node verify-systematic-field-product-regularity.js** for exact synthetic field arithmetic, Fourier-square and collision identities, survival line classification, and small checks of the crossover profiles. These finite fixtures do not test real cryptographic inputs.
