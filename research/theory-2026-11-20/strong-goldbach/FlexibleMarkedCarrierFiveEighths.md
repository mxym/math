# A positive polynomial-marker carrier with contiguous Type I through \(5/8-\eta\)

This is an application of the independent-triple **Proposition 2** in [Jain, *Smooth Numbers in Arithmetic Progressions with Uniformity in the Residue Class*, Hexagon 2611.00530v1 (Nov. 16), primary PDF pp. 5–6](https://hexagonmath.org/pdf/2611.00530v1). A single redesigned positive mixed carrier supports a contiguous maximal progression estimate to \(x^{5/8-\eta}\), including its **actual polynomial marker** \(K_{P_i}(n)\). The construction is not an application of Jain's smooth-number Theorem 1 to a prime-product sequence. It uses the proposition as stated in its recent preprint and does not settle the remaining larger-modulus signed Vaughan terms or Goldbach.

## 1. One fixed carrier and its exact weight

Use \(N=2x\), \(I=(x/2,x]\), \(J=N-I\), and \(y=x^\varepsilon\) as in the [polynomial log marker](PolynomialLogConservationMarker.md), with its eligible exponents \([\alpha,\beta]\), \(\alpha=.155,\ \beta=.5-\delta,\ 0<\delta<.001\). For any fixed \(0<\eta<.006\), the carrier is chosen once, independently of the even target and of the modulus. Its two actual macro primes \(A_M,B_M\) have exponents near .240 and .250. It has nine further distinct actual prime labels, with disjoint, sufficiently narrow fixed-width exponent bands around these values:
\[
\begin{array}{c|c|c}
 \text{label group}&\text{central exponents}&\text{total}\\\hline
 X & .028,\ .058,\ .065,\ .072 & .223\\
 Y & .045,\ .047,\ .051 & .143\\
 Z_1 & .046,\ .049 & .095 .
\end{array}
\tag{1}
\]
Groups \(X_1,Y_1,Z_1\) below mean the products of the indicated labels (\(X_1\) is the product of the entries in row \(X\)). The notation \(Z_1\) is different from the subpower rough-reference threshold \(Z\).

Choose a sufficiently large fixed integer \(K\), then put
\[
       b=.049/(K+1/4),\qquad \tau=b/4,\qquad
       b_i=b+\left(i-\frac{K+1}{2}\right)\frac{b}{100K^2}
       \quad(1\le i\le K).
\tag{2}
\]
In addition to the eleven previous labels, impose actual primes \(c_i\) in disjoint fixed exponent intervals centered at \(b_i\), and one independent \(y\)-rough residual \(v\) near exponent \(\tau\). We specify below how small to choose the widths and then take \(s\) sufficiently large so that \(\varepsilon<\tau/2\). The indicator \(C_{\rm flex}(n)\) is the product condition
\[
       n=A_M B_M X_1 Y_1 Z_1 c_1\cdots c_K v\in I .
\tag{3}
\]
The two macros, nine labels, and tiny labels have disjoint prime bands, and every prime factor of \(v\) is smaller than every \(c_i\). Thus (3) has unique label factorization, and \(C_{\rm flex}\) is 0 or 1. The prime factors of \(v\) need not themselves be distinct. Its interval is a redundant independent interval in (3): the exact central exponents of the labels sum to \(1-\tau\). If every label band has half-width \(\rho\), take \(|\log_xv-\tau|\le2(K+11)\rho\) and then \(x\) large so \(\log_x(n/x)=O(1/\log x)\) accounts for the other reserve. Choose the label widths so that this interval is positive in exponent and still below all \(b_i\).

Let \(u_q=\log q/\log n\) for prime divisors of \(n\). Write
\[
      S=\sum_{q\mid n,\ q<x^\alpha}u_q,\qquad
      E=\frac{\sum_i\log c_i+\log\operatorname{rad}(v)}{\log n}.
\]
For **every** \(n\) in the carrier and each polynomial \(P=P_2\) or \(P_3\) from (53), the exact marker is
\[
                         K_P(n)=P(S)-P(E).
\tag{4}
\]
Indeed only the two macros are eligible; they and their pair are below \(D=x^\beta\). Thus \(F=1-2+1=0\). A tuple of at most three small primes that contains any of the nine labels in (1) raises the product test on the two macros above \(D\), because the smallest large label has exponent near .028. It retains both singletons: the largest sum of at most three small exponents is at most \(3(.072+\rho)\), and \(.250+\rho+3(.072+\rho)<.499\) for the chosen small \(\rho\). Such a shifted \(F\) is \(-1\). A tuple containing only primes from the tiny labels or \(v\) has radical exponent at most \(3(b+o(b))\), less than the gap from the macro-pair exponent to \(\beta\) by choosing \(b\) small, so its shifted \(F\) is 0. The sum of weights of the ordered \(j\)-tuples with at least one of the nine labels is exactly \(S^j-E^j\), even with repeated tuple indices. The physical shift uses the radical, as before; the preceding bounds apply to that radical, not a falsely assumed distinct tuple. If \(v\) has a squared prime, its contribution is still \(\log\operatorname{rad}(v)\), and the same shifted tests and (4) hold. This is distinct from claiming \(S\) is the logarithm of all factors with multiplicity.

With sufficiently narrow widths and large \(x\), \(0\le E\le.0491\) and \(.4609\le S\le.5101\). On this entire interval \(P_2(S)>.95\) and \(P_3(S)>.99\) (use the factorizations \(P_2=1-(1-S)(1-2S)\) and \(P_3=1-(1-S)(1-2S)^2\)). Meanwhile \(P_2(E)\le3E\), \(P_3(E)\le5E\), and these values are nonnegative. It follows that, uniformly on the carrier, \(K_P>.74\) and \(K_P<2\). In particular this is an actual positive low carrier, not the bare smooth class of the old argument.

## 2. Uniform factor allocation and endpoints

Write \(C_*\) for the unspecified absolute constant in the stated Hexagon Proposition 2. Choose
\[
 \lambda=\min(10^{-6},10^{-4}/(C_*+1),\eta/[1000(C_*+1)]),\qquad
 \kappa=\lambda/8 .
\tag{5}
\]
Take \(K\) so \(b<\lambda/1000\). Choose \(\rho>0\) so the tiny bands are disjoint and \((K+11)\rho<b/1000\), and fulfill the preceding rough-suffix and elementary sign requirements. All choices are fixed independently of \(x\) and moduli. For subsets of the tiny labels the sum of centers differs from its cardinality times \(b\) by at most \(b/200\). To assign two prescribed nonnegative log lengths \(B_1,B_2\) with \(B_1+B_2\le .0485\), round their desired counts to the nearest integers, and use disjoint initial and following blocks of tiny labels of those sizes. Their total count is \(<K\) with fixed slack in length; each assigned sum has error \(<b\). This simultaneous adjustment uses a deterministic partition **by the chosen counts** before extracting any individual prime value. It does not select divisors according to the value of the carrier integer.

Let \(r=\log_x R\) for a modulus dyad \(R\), and write \(m,u,\ell\) for the three lengths \(M,N_{\rm len},L\) in the primary proposition. The allocations below hold for every \(r\) in the indicated ranges; common overlaps allow strict endpoint handling of dyads. For each row aim at
\[
                    m_*=1-r-\lambda,\qquad \ell_*=r+\lambda-u_*.
\tag{6}
\]
Apart from assigned tiny labels, use these groups:
\[
\begin{array}{c|c|c|c|c}
 r\text{ range}&M\text{ base}&\text{middle base}&L\text{ base}&
 (m_{\rm base},u_{\rm base},\ell_{\rm base})\\\hline
 [.5-\lambda/4,.512]&A_M Y_1 q_{.028} q_{.058}&q_{.065}q_{.072}&B_M Z_1&(.469,.137,.345)\\
 [.511,.546]&A_M Y_1 q_{.058}&q_{.065}q_{.072}&B_M Z_1 q_{.028}&(.441,.137,.373)\\
 [.545,.5865]&A_M Y_1 q_{.028}&X_1/q_{.028}&B_M Z_1&(.411,.195,.345)\\
 [.586,.611]&A_M Y_1&X_1&B_M Z_1&(.383,.223,.345)\\
 [.6105,.625-\eta]&X_1 Y_1&A_M&B_M Z_1&(.366,.240,.345)
\end{array}
\tag{7}
\]
Here \(q_t\) denotes the single large label centered at exponent \(t\). In the first four rows let \(u_*=u_{\rm base}\); in the last set
\[
                    u_*=\max(.240,2r-1+\eta/4).
\tag{8}
\]
Assign \(m_*-m_{\rm base}\) to the first group and \(u_*-u_{\rm base}\) to the middle group by the tiny-label rule above; the remaining tiny labels and the whole residual \(v\) go into the third group. All allocations are nonnegative. The maximal required **total** allocated length across the five rows is at most, respectively, .031, .048, .044, .031, and .0335. For the last bound note \(0\le u_*-.240\le.010\) and \(m_*-.366\le.0235\). Since the original bases sum to .951, the remaining desired length for the third group is the rest of .049 and accommodates \(v\). All groups are exact independent bounded coefficients; independent cutoffs on \(v\) are retained, including its \(y\)-rough condition. Dyadically subdividing the actual group variables, including the \(O(1/\log x)\) change of normalization to \(X'=M N_{\rm len} L\asymp x\), gives deviations per coordinate \(<\lambda/100\) from the targets, for sufficiently large \(x\). The deviations in each coefficient support and in the dyadic scale are dominated by \(b\), the specified widths and a term tending to 0; there are only a fixed power of \(\log x\) such product dyads.

For completeness, the exact exponent tests in Proposition 2 are (1) of [IndependentCarrierHighModulusStrips.md](IndependentCarrierHighModulusStrips.md), namely
\[
 \begin{gathered}
 u\ge\kappa,\quad u+\ell\le 2/3-5\kappa,\quad
 \ell\le m-\kappa,\quad m\le r\le u+\ell-\kappa,\\
 2u\le\tfrac12-\kappa,\quad
 2u+3\ell-1-r\le-\kappa,\quad
 C_*(u+\ell-r)+u+\tfrac12-2\ell\le-\kappa .
 \end{gathered}
\tag{9}
\]
For the first four rows the central margins \(1+u_*-2r\) (which bound both \(m_*-\ell_*\) and the gap from the diagonal lower level after respective costs \(2\lambda,3\lambda\)) are at least .113, .045, .022, .001. Their central complementary margins \(2r-\tfrac12-3u_*\) are at least \(.089-\lambda/2,\ .111,\ .005,\ .003\). For the final row the first margin is at least \(\eta/4\) by (8), and the complementary margin is at least \(\min(.001,13\eta/4)\); on the constant-middle branch use \(r\ge.6105\), and on the other branch use \(r\le.625-\eta\). In the final row \(1/2-2u_*\ge\min(.020,7\eta/2)\); in the others it is at least .054. Also \(u_*\ge.137\), \(u_*+\ell_*=r+\lambda\le.625+\lambda\), and the seam nearest the square-root level has \(r-m_*\ge\lambda/2\). The actual margin \(u+\ell-r\) is between \(.98\lambda\) and \(1.02\lambda\), so \(C_*(u+\ell-r)\le 1.02 C_*\lambda\) is smaller than every corresponding complementary margin. All checks remain strict with the losses in (9), by (5). The residue parameters \(a_1=N=2x,\ a_2=1\) satisfy the size and coprimality hypotheses at \(X'\asymp x\), since the supplied \(\delta>0\) in Proposition 2 is fixed. Thus the high-conductor estimate applies on every stated dyad, rather than only isolated narrow strips.

## 3. Distribution of the actual weight, including the small characters

Put \(W(n)=C_{\rm flex}(n)K_P(n)\). There is a uniform fixed-target maximal estimate for every fixed \(A>0\) and large enough fixed \(s\):
\[
 \sum_{r\le x^{5/8-\eta}}\sup_t
 \left|\sum_{\substack{m\in J\\m\le t,\,r\mid m}} W(N-m)
       - g_N(r)\sum_{\substack{m\in J\\m\le t}} W(N-m)\right|
                      \ll_{A,s,\eta,C_*}x(\log x)^{-A},
 \qquad g_N(r)=\frac{1_{(r,N)=1}}{\varphi(r)} .
\tag{10}
\]
Here and below the symbol \(r\) in a sum denotes the integer modulus, not its log exponent.

**The actual marker is an admissible finite coefficient expansion.** Expand (4) as a finite sum of monomials in the named individual prime logarithms and the single independent \(\log\operatorname{rad}(v)\), first dividing each such logarithm by \(\log x\). All exponents of these logarithmic variables are nonnegative integers with total at most three. The remaining factor for each degree \(j\) is \((\log n/\log x)^{-j}\), on \(n\asymp x\), a smooth function of the normalized full product. Mellin separate this together with a smooth cutoff for the requested product prefix. Each designated logarithm power is a bounded weight on exactly one of its factor labels, and \(\log\operatorname{rad}(v)\) is allowed on the independent suffix coefficient. Grouping by (7) just multiplies the weights inside a slot. Thus the theorem treats each monomial by genuinely independent 1-bounded coefficients up to fixed rescaling. Neither smoothness/primality of the full coefficient nor general distribution of weighted marker sequences is assumed. Squareful rough \(v\) is kept with its exact \(\operatorname{rad}\) weight, so no loss at the sum-of-moduli scale is hidden.

**Main-term and endpoint transfer.** For the range in (7), choose \(D=x^\gamma\) with \(0<\gamma<\min(\kappa,\delta_{\rm prop},\varepsilon/10)\) sufficiently small. The stated Proposition 2 after removing all conductors at most \(D\) gives a fixed power saving. To subtract the low nonprincipal conductors, fix all factors except, for example, the independent label \(q_{.058}\). The fixed product \(F\) is chosen **before** that prime; the endpoint condition just makes its interval shorter at length scale \(x/F=x^{.058+O(\rho)}\). For any monomial its additional prime weight is \((\log p/\log x)^a\), \(0\le a\le3\), a bounded weight of bounded variation there. The remaining smooth product factor or smoothed prefix also has bounded variation in that prime after the other factors are fixed. Partial summation and the usual maximal primitive-character mean estimate of Bombieri–Vinogradov (Vaughan plus Siegel–Walfisz), valid for \(D\ll(x/F)^{1/20}\), therefore give, for every \(B\), a weighted error \(O_B((x/F)(\log x)^{-B})\) in
\[
 \sum_{1<d\le D}\frac{1}{\varphi(d)}
     \sum_{\chi\bmod d}^{*}
        \left|\sum_{p \ {\rm in\ its\ label\ interval}}
                    \chi(p)\,\text{(prime and product weights)}\right|.
\]
One may alternatively use the endpoint maximal version before partial summation. The sum of \(1/F\) over the other named prime slots and \(v\) costs at most a log power, because there are a fixed number of label intervals and at worst a harmonic integer suffix. Multiple induction moduli cost \(O((\log x)/\varphi(d))\) for a conductor \(d\). To pass to the inducing primitive character, missed coprimality costs \(O(xD^2(\log x)^C/y)\): a missed prime \(p\mid r\) must be \(\ge y\), and the sum over its modulus multiples is \(\ll (\log x)/p\), in addition to \(O(x/p)\) possible full products. This is a power saving. The principal and nonreduced class passages are the same harmonic arguments: a common prime \(p<y\) makes the nonreduced actual carrier class empty, and common \(p\ge y\) costs \(O(x(\log x)^C/y+x^{5/8-\eta}(\log x)^C/y)\), since there are \(O(x/(rp)+1)\) only when a further independent divisibility is imposed, or directly \(O(x/r+1)\) along each \(r\) already containing \(p\). The latter suffices by summing over multiples of each \(p\mid N\). All arguments are after normalization to the bounded full carrier weight.

For \(r\le x^{.5-\lambda/4}\) use the ordinary convolution Bombieri–Vinogradov theorem, e.g. the [Bombieri–Friedlander–Iwaniec form used in Liu–Park–Song, Lemma 3.1](https://link.springer.com/article/10.1007/s40993-017-0089-3#Sec3). After each monomial separation, one actual prime factor \(q_{.058}\) has the required Siegel–Walfisz property (trivial bound for larger test moduli, ordinary Siegel–Walfisz for log-power moduli, bounded-variation prime weight); the opposite product coefficient is bounded by unique label factorization. Excluding primes dividing an auxiliary integer introduces at most its number of distinct prime divisors times log powers, permitted in the usual divisor-weighted Siegel–Walfisz condition. The fixed saving \(\lambda/4\) absorbs the losses, for example use the convolution theorem with exponent loss only \(\lambda/8\). This joins the Hexagon range since at the lower endpoint of the high range the margin in (9) is a fixed multiple of λ, and a modulus dyad has logarithmic width o(λ). All product endpoints and arbitrary prefixes are treated by the bounded smooth transition and a log-power grid as in [the previous seam note](MarkedCarrierTypeISeam.md#2-unweighted-maximal-distribution-and-reference). At each endpoint the actual or principal transition mass costs \(\ll xL^{-B}/r+1\) or \(\ll(xL^{-B}+1)/\varphi(r)\) respectively because \(|W|\le2\); after summing \(r\) these leave power reserve since \(5/8-\eta<1\). Increase the log reserve before taking the grid or Mellin sums. This proves (10), not just an estimate for dyadic smooth products.

**The own matched reference.** On a logarithmic mesh \(J_j\subset J\), let
\[
 a_j=|J_j|^{-1}\sum_{m\in J_j} W(N-m),\qquad
 c_N^W(m)=W(N-m)-a_j\,1_{P^-(N-m)\ge Z}/V_0\quad(m\in J_j)
\]
and set it to zero outside \(J\). Here \(Z=e^{(\log x)^{1/4}}\) and \(V_0=\prod_{p<Z}(1-1/p)\) are the **same** subpower reference cutoff and normalization as before; only the mesh multipliers match this actual \(W\), with \(0\le a_j\le2\). The fundamental-lemma/CRT and mesh arguments of (59) apply unchanged through \(x^{5/8-\eta}\): the largest combined modulus floor costs are \(x^{5/8-\eta+o(1)}\); for reduced \(r\) the literal density is \(r^{-1}\prod_{p<Z,p\mid r}(1-1/p)^{-1}\), which differs relatively from \(1/\varphi(r)\) by \(O((\log x)/Z)\). Nonreduced \(r\)'s are empty for common \(p<Z\), and are harmonically negligible for \(p\ge Z\). Mesh matching removes the full-cell unconditional discrepancy while the arbitrary prefix inside one mesh cell has small absolute mass. In particular
\[
             \sum_{r\le x^{5/8-\eta}}\sup_t
                \left|\sum_{\substack{m\le t\\r\mid m}}c_N^W(m)\right|
                         \ll_{A,s,\eta,C_*} x(\log x)^{-A}
\tag{11}
\]
for arbitrary \(A\) (with the standard sufficiently fine logarithmic mesh). The prime-log mass of the matched reference equals \(\mathfrak S(N)\sum_n W(n)\) with arbitrary log reserve by the same subpower rough CRT on prime progressions and the usual prime BV; the bounded new mesh coefficients do not change that calibration. This is not a claim that the actual prime-log mass has this main term.

## 4. Positive normalization and remaining signed terms

In the earlier order of limits (first \(x\to\infty\) at sufficiently large fixed \(s\), then \(s\to\infty\)), the ordinary unweighted carrier count has leading scale a fixed positive constant times \(x/(\varepsilon\log x)\). Indeed each named prime interval has a fixed positive PNT reciprocal factor \(\log(b'/a')\) for exponent endpoints \(a',b'\), and the independent \(y\)-rough suffix exponent near \(\tau>0\) gives the same uniform rough-number leading count as the previous mixed carrier. Squareful suffixes may remain in (10); for this ordinary count and weighted main integral their relative mass is negligible even in any desired progression-sum comparison at fixed \(s\): \(O(x/y)\) rough integers are divisible by a prime square, each contributes to at most \(\tau_2(N-n)=x^{o(1)}\) actual divisibility moduli, and the principal reciprocal mass costs only a log power. On the remaining squarefree carrier, \(S=1-(\log A_M+\log B_M)/\log n\) and \(E=S-\sum_{j=1}^9\log q_j/\log n\), so (4) is a continuous function of the eleven large-labelled log exponents up to \(O(1/\log x)\). The same prime reciprocal integral yields a positive weighted constant, also immediate as a lower bound from \(K_P>.74\). In the earlier reference normalization this is a positive constant times \(M_N/\varepsilon\), which can be extremely small, depending on the fixed widths and thus on \(\eta,C_*\). No lower bound uniform in that narrowing is asserted.

With the genuine Vaughan coefficients one may now start (60) with, for example, \(U=V=x^{.300}\), since their product is below \(x^{5/8-\eta}\). For \(U<d\le x^{.600}\), expand \(\sum_{\ell\mid k,\ell>V}\Lambda(\ell)\) as before. Its logarithmic Type I contribution and all terms \(dp\le x^{5/8-\eta}\) are negligible by (11); on collecting \(r=dp\), the absolute \(\log p\) weights are bounded by \(\log r\), and moving \(h\) endpoints are covered by maximal prefixes. Prime powers with \(d\ell>x^{5/8-\eta}\) have \(\ell>x^{.025-\eta}\), hence their absolute contributions are power small as in (61). The remaining terms are exactly the signed \(dp>x^{5/8-\eta}\) with short unweighted quotient \(h\), and the original quotient-weighted block on \(d>x^{.600}\) (there \(k\ll x^{.400}\)). This changes the actual K-weighted Type I reduction for **this one redesigned carrier**. It says neither that its remaining terms cancel nor that other low sectors admit comparable independent allocation. Strong Goldbach is unresolved.
