# Centering the true same-cofactor prime versus balanced-semiprime cell

This concerns only the two stubborn physical cohorts of [AdaptiveWholeLowCollision](AdaptiveWholeLowCollision.md), in the literal cubic representation of [WholeLowCubicHybrid](WholeLowCubicHybrid.md). Their exact joint signed score is a calibrated high-rough quotient parity sum. The **entire Vaughan Type I contribution equals the literal rough-reference term** to arbitrary-log accuracy, with real balanced semiprimes retained. What remains is one explicit signed Type II sum at each \(N\). No estimate for that sum or for the other whole-low cells is asserted.

## 1. Literal score and one-sided target

Use \(N=2x\), \(I=(x/2,x]\), \(L=\log x\), \(M_N=\mathfrak S(N)x/(2L)\), where
\[
 \mathfrak S(N)=2\prod_{p>2}\left(1-\frac1{(p-1)^2}\right)
                   \prod_{\substack{p\mid N\\p>2}}\frac{p-1}{p-2}.
\]
As in WholeLowCubicHybrid, \(Z=e^{L^{1/4}}\), \(R_Z(v)=1_{P^-v\ge Z}\), \(V_0=\prod_{p<Z}(1-1/p)\), \(a(n)=\log(N-n)1_{N-n\ {\rm prime}}\), \(b(n)=R_Z(N-n)/V_0\), \(w=a-b\). Fix the original marker parameter \(0<\delta\le .001\). Each \(s\) below is prime with \(\sigma=\log s/L\in[.10,.14]\). Define the true quotient support
\[
 H_s(u)=1_{\{su\in I,\ P^-(u)>x^{.5-\sigma+2\delta},\ \mu^2(u)=1\}},
 \qquad f(t)=(1-2t)^3,\qquad
 C_s(u)=H_s(u)\bigl[-\mu(u)-f(\log s/\log(su))\bigr].
\]
The \(H_s=1\) quotients are literally prime \(u\), or \(u=pq\) with distinct \(p,q\) in \((x^{.5-\sigma+2\delta},x^{.5-2\delta})\); indeed three eligible factors would exceed \(x^{1-\sigma}\), and the upper split bound follows by dividing \(u\le x^{1-\sigma}\) by the lower bound on the other factor. In the same-s collision these are exactly \(E_2(s),E_3(s)\). For \(\delta\le.001\) the term \(f(\log s/\log(su))\) is in the untapered part of the cubic. The hybrid scores in the two cohorts are exactly \(1-f\) and \(-1-f\); the first also equals the exact \(R\)-score on \(\mathcal L_\tau\). There is no multiplicity across \(s\): it is the unique short prime in these cohorts. Write
\[
    G_N=\sum_{s,u}w(su)C_s(u),\qquad A_N=\sum_{s,u}a(su)C_s(u).
\]
By the per-cell uniform true quotient rough-reference formula and unprogressioned PNT in AdaptiveWholeLowCollision, and then prime Mertens on \(s\),
\[
 \begin{split}
 \sum_{s,u}b(su)C_s(u)&=(J_\delta+o(1))M_N,\\
 J_\delta&=\int_{.10}^{.14}
    \frac{(1-f(t))-(1+f(t))\log[(.5-2\delta)/(.5-t+2\delta)]}
         {t(1-t)}\,dt.                                          \tag{1}
 \end{split}
\]
Here \(\log s/\log(su)=\sigma+O(1/L)\) uniformly, and summing the absolute reference masses of the two cohorts costs \(O(M_N)\). The signs are real: in raw \(\mu\)-weight the reference is **negative** because the balanced semiprime-to-prime ratio \(\log[(.5-2\delta)/(.5-\sigma+2\delta)]\) is below 1. An uncentered vanishing theorem for this parity statistic would not represent its proper main.

Let \(R_{\rm rest}(N)\) be the actual two unpriced sums in (2) of WholeLowCubicHybrid after deleting exactly these cohorts. An upper below
\[
 \frac{A_N}{M_N}
    \le J_\delta+.00659-\eta-\frac{R_{\rm rest}(N)}{M_N}          \tag{2}
\]
with sufficiently small independent error tolerances and a fixed \(\eta>0\) would fit that whole-low criterion. There is no bound for \(R_{\rm rest}\) in this note. Giving the entire residual allowance to the single cell is only a diagnostic: the raw one-sided threshold there is \(J_\delta+.00659\), not an asymptotic or a whole Goldbach criterion. By the rational checker, \(.06282<J_{0}<.06284\) in the limit \(\delta\downarrow0\), so that threshold tends to a number in \((.06941,.06943)\). At \(\delta=.001\), \(.06791<J_\delta<.06794\); this records the integral, not that the original high ledger is optimized at that \(\delta\).

## 2. Entire true Type I term matches the literal reference

Put \(U=V=x^{1/5}\),
\[
 c_V(r)=\sum_{\substack{\ell\mid r\\\ell>V}}\Lambda(\ell).
\]
For every fixed \(B>0\), uniformly in all large even \(N\),
\[
 \boxed{\quad
 G_N=\sum_{\substack{s,u,d,r\\ dr=N-su,\ d>U,\ r>V}}
   C_s(u)\,1_{(su,N)=1}\mu(d)R_Z(d)c_V(r)R_Z(r)
       +O_{B,\delta}(xL^{-B}).
 \quad}                                                         \tag{3}
\]
This uses exactly one unresolved signed Type II sum. In its support \(dr\asymp x\), \(d,r>x^{1/5}\), so each variable is polynomially long.

**Exact arithmetic reductions.** Every physical product \(su\) can be counted at most ten times even if one forgets the uniqueness of \(s\), so proper prime powers \(m=N-su\) cost \(O(x^{1/2}L^2)\) after the \(\log m\) weight. No genuine prime \(m\) with \((m,N)>1\) can be on this composite \(su\) support: if \(m\ge x=N/2\) is prime dividing \(N\), only \(m=x\) is possible, and then \(su=x=m\) would be prime. The \(b\)-mass removed by \((su,N)>1\) is at most \(O(x^{.9}L^{O(1)})\): all prime divisors of the true \(su\) exceed \(x^{.10}\), there are \(O(1)\) primes of \(N\) of that size, and open their multiples before applying the multiplicity bound and \(V_0^{-1}=O(L^{1/4})\).

Replace \(a(su)\) by \(\Lambda(m)R_Z(m)\) with this exact unit test, with the proper-power error just stated. Apply the standard Vaughan identity as in [Lü–Wang–Wu v2, (2.3)](https://arxiv.org/html/2610.20242v2#S2); its \(\Lambda(m)1_{m\le V}\) term is absent. The two short terms before opening roughness are
\[
 \sum_{\substack{d k=m\\ d\le U}}\mu(d)R_Z(d)R_Z(k)\log k,\qquad
 -\!\sum_{\substack{d\ell k=m\\ d\le U,\ \ell\le V}}
     \mu(d)\Lambda(\ell)R_Z(d\ell)R_Z(k).
\]
The long term is exactly the sum on the right of (3). The multiplicative identity for the rough indicators is exact even when factors are not coprime. In the second Type I term put \(q=d\ell\); its coefficient before \(R_Z(q)\) has modulus at most \(\log q\) because \(\sum_{\ell\mid q}\Lambda(\ell)=\log q\). For the first term use \(q=d\).

**Uniform genuine source distribution.** Fix \(N,s\) with \(s\nmid N\), and use the true quotient source \(C_s(u)1_{(u,N)=1}\) at scale \(Y=x/s\), hence \(Y\ge x^{.86}\). Its prime piece has ordinary maximal BV; in its balanced piece both original primes are in independent bands and \(>x^{.36}\). On actual dyads both lengths are polynomial in \(Y\), their product is \(\asymp Y\), and one independent prime is Siegel–Walfisz. The latter remains true after excluding the prime divisors of \(N\), which removes \(O(\log N)\) entries. Use the sub-half **bilinear BV** in [Polymath, *New equidistribution estimates of Zhang type*, journal Theorem 2.9, p. 2079](https://msp.org/ant/2014/8-9/ant-v8-n9-p03-p.pdf), whose stated proof is [Bombieri–Friedlander–Iwaniec, Theorem 0(b), (1.5)](https://doi.org/10.1007/BF02399204). It treats two divisor-bounded coefficients of scales with product \(\asymp Y\), one of polynomial length satisfying Siegel–Walfisz including auxiliary coprimality, and sums maximum reduced-class discrepancies to \(Y^{1/2}(\log Y)^{-B}\). There is no fixed-residue or smooth-modulus hypothesis in this sub-half input. Here immediate prime prefix Siegel–Walfisz applies to every clipped factor interval; auxiliary masks remove at most \(\omega(b)\leq\tau(b)\) prime labels for a mask \(b\). As usual for all moduli in the Siegel–Walfisz definition, above an arbitrary log power the trivial count in one residue class suffices. The bounded coefficients are actual ordered prime pairs divided by 2; delete squares even across all moduli at a cost \(O(Y^{.49}\sqrt Y)\) for fixed \(s\).

For product-prefix maxima, use a log-relative grid of mesh \(Y/L^B\) in the output and, for each chosen product endpoint \(t\), partition the first prime factor into relative \(O(L^{-B})\)-width intervals. On each, freeze the second prime's prefix at \(t\) divided by the first interval's lower endpoint. Only physical products in a strip of length \(O(Y/L^B)\) about \(t\) can change; there is at most fixed divisor-power multiplicity. Shiu's bound in the reduced AP and in its principal gives total boundary cost \(O(Y L^{-B+O(1)}/\phi(q))\) at each modulus \(q\le Y^{.49}\). Here \(q\) is polynomially below the strip length; use a full strip of that length even when actual errors lie in a shorter strip. There are only log-power many factor rectangles and grid endpoints, so increasing the BV accuracy gives arbitrary saving after taking both maxima and summing moduli. The small polynomial \(f\) and \(\log m-\log q\) weights are now handled by partial summation. Both weights have bounded variation with polylog budget: on \(su\in I\), \(m\in[x,1.5x)\), the variation of \(\log m\) is \(O(1)\), its supremum is \(O(L)\), and \(q\) is a constant for each progression. Keep \(\log m\) at the actual \(u\) in the coprime principal; no replacement by \(\log x\) is made.

Open \(R_Z(k)\) with consecutive upper/lower Bonferroni truncations of degree \(K=\lfloor L^{1/4}\rfloor\) and \(K+1\). The auxiliary labels \(e\) have all primes \(<Z\), \(e\le Z^{K+1}=\exp(O(L^{1/2}))\). They are coprime to \(q\) because \(R_Z(q)=1\). Under the retained unit conditions, there are no rows if \((qe,Ns)>1\); otherwise the residue is the real reduced \(u\equiv N\bar{s}\pmod{qe}\). In particular there is no nonunit \(N\)-residue to estimate. All moduli satisfy the strict reserve
\[
 q e\le x^{.4+o(1)}< Y^{.49}\quad
      (.49\cdot .86=.4214>.4).
\]
The split between below-\(Z\) and above-\(Z\) prime factors makes the labels \((q,e)\) unique at a modulus, and the remaining Vaughan coefficients cost \(O(L)\). Treat Bonferroni errors using the **unsigned** genuine prime and balanced product sources. Their exact reduced principal is \(1_{(u,qe)=1}/\phi(qe)\). Every \(u\) factor and \(s\) exceeds \(Z\), so restoring the small Euler product in the coprime principal is immediate after removing \(p\mid N\). A factorial bound \((O(\log L))^{K}/K!\) and the absolute harmonic \(\sum_{q\le x^{.4}}1/\phi(q)=O(L)\) make the Bonferroni tail arbitrary-log-small. Summing the BV error \(O_B(Y L^{-B})\) over \(s\) costs no polynomial loss, by \(\sum_{x^{.10}\le s\le x^{.14}}1/s=O(1)\) for primes. The products' endpoint O terms have the same arbitrary log reserve. This produces the pointwise coprime principal for each fixed \(s,u\), multiplied by
\[
 V_N(Z)=\prod_{\substack{p<Z\\p\nmid N}}\left(1-\frac1{p-1}\right).
\]

**Uniform harmonic evaluation, including the subpower presieve.** Fix \(A=Nsu\) (even and polynomially bounded). For the full coprime harmonic sums we use [Huang–Li, Lemma 1](https://arxiv.org/pdf/2005.03811), the uniform Goldston–Yıldırım estimate: at \(R\) of fixed positive polynomial size with \(\log A\ll\log R\),
\[
 \sum_{\substack{d\le R\\(d,A)=1}}\mu(d)/\phi(d)=O_B(L^{-B}),\qquad
 \sum_{\substack{d\le R\\(d,A)=1}}\mu(d)\log(R/d)/\phi(d)
      =\mathfrak S(A)+O_B(L^{-B}).                               \tag{4}
\]
One cannot insert the entire small-prime primorial into \(A\) in this lemma. Instead, to get the same sums additionally restricted by \(R_Z(d)=1\), convolve the full coefficients with the nonnegative inverse Euler weights
\[
 h(t)=\prod_{p^j\parallel t}(p-1)^{-j}\ 
 \text{ for }P^+(t)<Z,\ (t,A)=1,\qquad h(t)=0\text{ otherwise}.
\]
This is an exact Dirichlet convolution since each squarefree \(\mu(p)/\phi(p)=-1/(p-1)\). With \(p=2\) already excluded, \(\sum h=V_N(Z)^{-1}=O(L^{1/4})\): the prime divisors of \(su\) are above \(Z\), and omitting factors \(p\mid N\) only decreases it. At \(\varepsilon=1/\log Z\) the Euler sum \(\sum h(t)t^\varepsilon\) is \(O(\sum h)\): after separating bounded \(p\), the extra logarithm is
\(O(\sum_{p<Z}(p^\varepsilon-1)/p)=O(1)\) by \(\sum_{p<Z}\log(p)/p\ll\log Z\). Thus the mass above \(t=e^{L^{1/2}}\) is \(O(L^{1/4}e^{-L^{1/4}})\). For the remaining \(t\), (4) applies to \(R=U/t\) uniformly. The discarded tail in the convolution is bounded using \(\sum_{d\le U}|\mu(d)|/\phi(d)\ll L\) and log weight at most \(O(L)\). We obtain
\[
 \sum_{\substack{d\le U\\(d,A)=1}}\frac{\mu(d)R_Z(d)}{\phi(d)}
   =O_B(L^{-B}),\qquad
 \sum_{\substack{d\le U\\(d,A)=1}}\frac{\mu(d)R_Z(d)}{\phi(d)}\log(U/d)
   =\mathfrak S(A)/V_N(Z)+O_B(L^{-B}).                           \tag{5}
\]
For the first Vaughan principal \(\log(m/d)=\log(U/d)+\log(m/U)\) **pointwise** before summing over \(s,u\). Equation (5) and \(\sup|\log(m/U)|=O(L)\) show that this gives \(\mathfrak S(A)/V_N(Z)\) with arbitrary log reserve.

For the second principal the divisor factor is literally \(\phi(d\ell)^{-1}\). For \(\Lambda(\ell)\ne0\) write \(\ell=p^j\), with \(p\ge Z\) by the rough test. Replacing it by \(1/(\phi(d)\phi(\ell))\) changes the factor only if \(p\mid d\), then by the exact relative factor \(1-1/p\). The absolute correction is at most
\(O(L\,\sum_{p\ge Z,j\ge1}\log p/(p\phi(p^j)))=O(L^{O(1)}/Z)\),
even dropping \(p\mid d\) in the inner absolute sum. The resulting factored harmonic is \(O_B(L^{-B})\) by the first estimate of (5) and \(\sum_{\ell\le V}\Lambda(\ell)/\phi(\ell)\ll L^{O(1)}\).

Consequently the combined short principal equals
\(\sum_{s,u}C_s(u)1_{(su,N)=1}\mathfrak S(Nsu)\), up to arbitrary-log error. Since \(su\) has at most three genuine prime factors, all \(>x^{.10}\) except possible equality at the lower endpoint, the ratio \(\mathfrak S(Nsu)/\mathfrak S(N)=1+O(x^{-.10})\) uniformly. Direct application of the same Bonferroni product BV with \(q=1\) shows that the literal \(b\)-sum differs from \(\mathfrak S(N)\sum_{s,u}C_s(u)1_{(su,N)=1}\) by \(O_B(xL^{-B})\) (use \(V_N(Z)/V_0=\mathfrak S(N)(1+O(L/Z))\)). This proves (3), without changing the signed calibration or tagging an artificial prime.

## 3. Which new literature applies, and which term does not transfer

[Lü–Wang–Wu, arXiv:2610.20242v2, revised Nov 19](https://arxiv.org/html/2610.20242v2) states in Theorem 1 the fixed-\(+2\) assertion \(\sum_{p\le X}\mu(p+2)=o(\pi(X))\). This is the preprint's claim, not an independently certified theorem here. Its Remark 1 does not prove a Liouville version; its Remark 3 explicitly leaves even moving additive shifts of size \(\asymp X\) to a possible Quasi-RH-based extension. Inspection of §§3–5 verifies the following scope comparison. Their Type I Proposition 3.1 treats the multiplicative \(\mu(qk+2)\mathcal W(qk+2)\) coefficient via bounded-multiplicative-function BV, whereas (3) above treats both true quotient pieces by prime and prime-product BV and has a **nonzero** principal. Their Type II equations (4.1), (4.7) retain the actual fixed determinant \(bmn-ars=2(a-b)\) in (4.12), after taking a common quotient of the shift by several subpower prime labels. This identity and the ensuing compact support \(\psi_{-2}((bmn-ars)/Y)\) are explicit, not estimates widened to a moving shift. On our physical same-\(u\) projection, \(dr=N-s u\), two rows give
\[
                 s' dr-s d'r'=N(s'-s).
\]
With \(s,s'\asymp S\) this numerator is on the \(N S\) scale, not the fixed-shift \(S\) scale. Neither the original compact determinant kernel nor its small-conductor Mellin estimates (Proposition 2.2 and §5) supplies a bound for this moving equation. Their auxiliary weight requires many subpower prime factors of the shifted input; on our hard \(H_s(u)\) it is identically zero, and it is not applicable to the single genuine macro tag \(s\). Their concluding de-weighted \(o(X)\) bound with log-prime weight, even if independently verified, would not alone reach \(o(X/\log X)\) on this rare polynomially rough source. [Jiang–Lau–Lü, arXiv:2611.12467v2, Theorem 4.1](https://arxiv.org/html/2611.12467v2#S4) likewise keeps the exact fixed offset 1, not our moving determinant or true cohorts. These are comparisons of the proved-in-the-note reduction to the **stated** outside inputs, not endorsements of their entire proof.

Two other nearby proof programmes matter for scope. [Arneth, *A Candidate Proof Architecture for Binary Goldbach*, Gold-42, Oct 20, 2026](https://zenodo.org/records/23504447) explicitly targets signed fixed-target Möbius–prime cancellation after a quartic sieve and balanced Type II reassembly, and describes the unresolved parity-separation step. Its public primary abstract does not state the present physical \(s\)-marked prime/balanced-semiprime quotient comparison or this cubic reference. [Pham, *Uniformity, Local Structure and Boundary Correlations in Goldbach Representations*, Oct 30, 2026](https://www.preprints.org/manuscript/202610.3061) gives weighted mixed prime/rough row estimates in Theorems A.1 and C.2 and a rough-pair benchmark in Theorem D.2. Proposition D.5 keeps the centered double-prime row covariance as a **hypothesis**, not an unconditional Type II estimate. Those mixed/rough estimates concern two reflected row forms with a shared free argument; they do not supply the actual Möbius-weighted \(dr=N-su\) correlation in (3). We use no claimed parity closure from either preprint.

[check_same_cofactor_vaughan_center.py](check_same_cofactor_vaughan_center.py) encloses the calibration integrals with rational interval arithmetic and tests the finite coefficient identities.
