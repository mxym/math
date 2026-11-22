# Ordinary Möbius and Liouville parity opposite true primes at a small-radical target

Fix \(B>0\) and a compact interval \(J=[a,b]\subset(0,1)\) with \(a<b\), and put \(I=PJ\), \(L=\log P\). Uniformly over every sufficiently large prescribed even \(P\) with \(\operatorname{rad}(P)\le L^B\), for both \(f=\mu\) and \(f=\lambda\) we have
\[
 \sum_{\substack{p\in I\\p\ {\rm prime}}} f(P-p)
 \ll_{B,J} \frac{P}{L\sqrt{\log L}} .
\tag{1}
\]
This uses the [companion small-radical projected major bound](Proof.md) and its already established full-target minor comparison. No Riemann hypothesis is assumed; the eventual threshold need not be effective. In particular the complete unweighted sum on \(p<P\) is \(o_B(P/L)\): take \(J=[\eta,1-\eta]\), use the prime number theorem to bound the two omitted intervals by \(O(\eta P/L)\) for fixed \(\eta>0\), then let \(\eta\) decrease after \(P\) tends to infinity.

For \(\lambda\), (1) gives asymptotically equal numbers of actual prime-opposite rows of either sign on \(I\). For \(\mu\), both signs occur on squarefree rows, and their respective counts are
\[
 (1+o_{B,J}(1))\,\frac{|I|}{2L}
    \prod_{\ell\nmid P}
          \left(1-\frac1{\ell(\ell-1)}\right).
\tag{2}
\]
This is a statement about **ordinary** factor parity of \(P-p\), not a sign of a signed angular score and not about the existence of a prime complement. In particular \(\mu(P-p)=-1\) can arise from any odd number of distinct factors.

## 1. The needed true progression input

For fixed \(f\in\{\mu,\lambda\}\) and every \(A>0\), we use
\[
 \sum_{q\le x^{.46}}\max_{(c,q)=1}
          \left|\sum_{\substack{n\le x\\n\equiv c\bmod q}} f(n)\right|
 \ll_A x(\log x)^{-A}.
\tag{3}
\]
Here \(q=1\) is allowed. To obtain (3), [Granville and Shao, *Forum of Mathematics, Sigma* 6 (2018), e15, Theorem 1.1(b)](https://doi.org/10.1017/fms.2018.14) gives the Bombieri–Vinogradov bound for the discrepancy relative to the coprime mean of \(f\). Indeed \(f\in\mathcal C\) in their notation: the logarithmic derivative coefficients of \(1/\zeta(s)\) for \(\mu\), and of \(\zeta(2s)/\zeta(s)\) for \(\lambda\), have modulus \(\Lambda(n)\) on prime powers. Both restrictions to the primes equal \(-1\) there. Their Siegel–Walfisz criterion for \(f\) follows from the small-conductor classical zero-free argument for the series \(1/L(s,\chi)\) and \(L(2s,\chi^2)/L(s,\chi)\), respectively, with the usual Euler factors for imprimitive characters. In this argument for conductors \(\le (\log x)^C\), take Perron height \(\exp(c\sqrt{\log x})\); the classical excluded strip, and Siegel's lower bound on the distance of a possible real zero with an arbitrarily small fixed exponent, both allow a shift of order \((\log x)^{-1/2}\). For the reciprocal estimate one can use exactly the disc comparison of §1 of [the companion proof](Proof.md), now with fixed disc radius (take \(u=1/16\)) and \(\log |L|\ll\log(qT)\) there by the usual polynomial growth bound. The local logarithmic derivative error is \(O(\log(qT))\); comparison at \(1+\theta+it\) with \(\theta\asymp1/\log(qT)\) yields \(|1/L|\ll \log(qT)\) in the smaller strip. The principal character uses \(1/\zeta\) and its classical zero-free estimate. In the half-plane used, \(L(2s,\chi^2)\) is uniformly bounded by its absolutely convergent series; the imprimitive Euler factors cost at most fixed logarithms. For modulus beyond a sufficiently large fixed power of \(\log x\), the Siegel–Walfisz discrepancy criterion follows simply by bounding the number of terms in one residue class and \(x/\varphi(q)\).

For completeness, remove the coprime mean rather than identifying it with zero by convention. Write
\[
 f(n)1_{(n,q)=1}=(f*g_q)(n),\qquad
 \begin{cases}
 g_q(d)=1_{\text{all prime factors of }d\text{ divide }q},& f=\mu,\\
 g_q(d)=1_{d\mid\operatorname{rad}(q)},& f=\lambda .
 \end{cases}
\]
These are the local inverses of \(1-p^{-s}\) and \((1+p^{-s})^{-1}\) at \(p\mid q\), respectively. Both have reciprocal mass \(\ll 1+\log\log(3q)\). For \(d\le\sqrt{x}\) the classical Mertens bound for \(f\) gives arbitrary logarithmic cancellation at length \(x/d\). For larger \(d\), Rankin gives
\[
 \sum_{d>\sqrt x}g_q(d)/d
 \le x^{-1/8}\prod_{\ell\mid q}(1-\ell^{-3/4})^{-1}
 \le x^{-1/8}\exp(O((\log x)^{1/4}))
\]
uniformly for \(q\le x\): split \(\sum_{\ell\mid q}\ell^{-3/4}\) at \(\log x\) and use \(\omega(q)\le\log x/\log2\) on the upper part. Thus \(\sum_{n\le x,(n,q)=1} f(n)\ll_A x(\log x)^{-A}\) uniformly in this range. In the discrepancy sum this is multiplied by \(\sum_{q\le x}1/\varphi(q)\ll\log x\). This proves (3). We apply it at each common actual endpoint \(x\asymp_J P/u\) for a fixed tag product \(u\); we do not require a maximum over unrelated endpoints inside the modulus sum.

## 2. A marked signed cancellation

Put \(z=\exp(L^{.24})\), \(R=\operatorname{rad}(P)\), and take one of the admissible \(K\)-band families for the full-target comparison. Its tag set \(\mathcal T\) contains exactly one prime from each band, \(\mathcal V=\sum_{u\in\mathcal T}1/u\), and
\[
 W(y)=\mathcal V^{-1}\sum_{\substack{u\in\mathcal T\\u\mid y}}1 .
\]
All tag primes are larger than \(\exp(cL^{.1})\), smaller than \(\exp(2L^{.2})\), and coprime to \(R\) for large \(P\). Pointwise \(W(y)\ll_K L^K\) for \(y\le P\). For sufficiently large fixed \(K\), chosen for each fixed required \(A>0\), we show
\[
 \sum_{\substack{p\in I\\p\ {\rm prime}}}
      (\log p) f(P-p)W(P-p)=O_{A,B,J,K}(P L^{-A}).
\tag{4}
\]
The constants are uniform across all admissible families of that \(K\).

Replace the true prime leg by \(\Lambda(n)1_{P^-(n)>z}\) on \(n\in I\); prime powers cost \(P^{1/2+o(1)}\), and the true primes in the interval are not lost. A rough \(n\) is a target unit since \(R<z\), hence \(P-n\) is also a target unit. For \(\lambda\), \(f(u h)=(-1)^K f(h)\) always. For \(\mu\) this holds if \((u,h)=1\), and a failure requires a marked square \(r^2\mid P-n\) with \(r>\exp(cL^{.1})\). The number of **all** such integer \(n\) is
\[
 \le \sum_{\substack{r>\exp(cL^{.1})\\r\ {\rm prime}}}\left\lfloor P/r^2\right\rfloor
 \ll P\exp(-c L^{.1}).
\]
Since the signed and corrected weights have magnitude at most \(W(P-n)\ll_K L^K\), the correction costs less than any fixed log power before expanding \(\Lambda\). We may therefore use the exact replacement \((-1)^K\mathcal V^{-1}\sum_{P-n=uh,\ u\in\mathcal T} f(h)\), with \((h,R)=1\) on every retained term.

Use Vaughan's identity as in [the near-full cofactor theorem](../near_full_cofactor/Proof.md), cutting both short factors at \(P^{1/5}\). The Type II part has \(\mu\) on a polynomial-length slot and coefficients bounded by \(L\) on the other slot. It is handled by the reflected comparison and the companion major estimate, with the bounded residual \(f(h)1_{(h,R)=1}\). As in the prior application, split the products into mesh rectangles at the endpoints of \(I\) and the tag products into smooth fixed-ratio shells. The divisor moments and the fourth moment of \(W(P-n)\) over integers bound the discarded mesh boundaries before inserting the mean-square estimate; the same logarithmic precision and parameter order apply for this residual of modulus at most one. Cauchy on \(h\) in a shell of tag size \(Y\) uses \(O(P/Y)\) possible residuals. This gives the arbitrary-log Type II bound in (4).

The Type I terms have a short divisor \(d\le P^{.4}\) with \(P^-(d)>z\), and a remaining integer \(k\) with \(dk=n\in I\), \(P^-(k)>z\). The coefficient at \(d\), after grouping the two separately truncated factors in the second Type I term, is \(\ll L\) by \(\sum_{b\mid d}\Lambda(b)=\log d\). The first Type I term has an extra smooth \(\log k\), of size \(O(L)\). Open the \(z\)-rough condition on \(k\) by Bonferroni truncated at \(j=\lfloor L^{.1}\rfloor\) prime factors. Its absolute pointwise error is bounded by the positive divisor sum over squarefree \(e\mid k\) with \(j+1\) primes \(\le z\), and \(e\le\exp(O(L^{.34}))\). In the exact equation \(P-dk=uh\), we have \(de\mid P-u h\) when \(e\mid k\). A divisor shared by \(de\) and \(u\) would divide \(P\) and contradict \((u,P)=1\). A divisor shared by \(de\) and \(P\) is impossible once \((h,R)=1\) is retained. Thus \((de,uP)=1\) for every term, and \(h\equiv P\bar u\bmod de\) is reduced.

The error from the Bonferroni remainder after fixing \(u,d\) is bounded by summing \(O(P/(ude)+1)\) over the above \(e\), with any unit restrictions dropped at this stage. The floor errors over \(u,d,e\) are \(P^{.4+o(1)}\) times fixed logarithms. The reciprocal mass of \(e\) is at most \((C\log L)^{j+1}/(j+1)!\), so the other error is \(O_{A,K}(P L^{-A})\) after using \(\sum_d1/d\ll L\), \(\sum_u1/u=\mathcal V\), and the fixed coefficient and \(\log k\) losses.

In the retained sum impose \(h\bmod R\) by CRT, taking its \(\varphi(R)\) allowed unit classes modulo \(R\). Thus for fixed \(u,d,e\), \(f(h)\) is summed over at most \(R\le L^B\) **reduced** classes modulo \(Q=deR\), with \(Q\le P^{.4+o(1)}\). For fixed \(u\) the actual endpoint \(x\asymp_J P/u\) is independent of \(d,e\); \(Q\le x^{.46}\) uniformly. From \(Q\) we recover \(de=Q/R\) and then \(d,e\) uniquely by their opposite prime ranges. Formula (3) therefore bounds the aggregate modulus error by \(O_{A,B,K,J}((P/u)L^{-A})\), allowing arbitrary fixed log losses and the sum over CRT classes. For \(\log k=\log((P-uh)/d)\), use partial summation: its endpoint size is \(O(L)\) and its derivative in \(h\) is \(O_J(u/P)\) independently of \(d,e\); apply (3) at each common endpoint in the partial-summation integral. Sum over \(u\) by its reciprocal mass \(\mathcal V\). The only third term of Vaughan's identity is supported below \(P^{1/5}\) and is absent in \(I\). This proves (4).

## 3. Removing the marks on the actual prime leg

Choose \(J_0\asymp_K\log L\) families of disjoint full prime bands, all pairwise disjoint across different families. To make this explicit, for \(1\le i\le K\) use an exponent block centered at \(.1+(i-\tfrac12)/(10K)\) of width \(1/(40K)\). The blocks are mutually separated by more than \(1/(20K)\). Walk through each block in steps \((\log4)/\log L\), simultaneously across the \(K\) blocks. Use the band of primes \(r\equiv1\bmod4\) in \([\exp(L^\vartheta),\exp(2L^\vartheta)]\) at each selected exponent \(\vartheta\). Consecutive bands within a block are disjoint (their lower logarithmic endpoints differ by a factor 4), and the prime number theorem modulo \(4\) gives harmonic masses \(\frac12\log2+o(1)\) uniformly. These are admissible for the existing full-target comparison. All bands are above target primes by the radical restriction.

Write \(W_j\) for these normalized weights and \(\bar W=J_0^{-1}\sum_j W_j\). Ordinary true-prime Bombieri–Vinogradov, applied to the progressions \(p\equiv P\bmod\mathrm{lcm}(u,v)\), gives
\[
 \sum_{p\in I,\ p\ {\rm prime}}
      (\log p)|\bar W(P-p)-1|^2\ll_{B,J,K} P/J_0+O_{A,K,J}(PL^{-A}).
\tag{5}
\]
Specifically each expansion in one or two families uses moduli \(\exp(O_K(L^{.2}))\), all target units. For two distinct families, \((u,v)=1\) and the pair of tags can be recovered from its lcm by the band labels. In the same family the multiplicity of an lcm is at most \(2^K\): for each color it specifies either one repeated prime or two primes to order. This bounds the total absolute BV errors up to the fixed normalizers. Any proper powers allowed by a von Mangoldt version of BV cost at most \(P^{1/2+o(1)}\) by the pointwise moment bound. In the principal model each tagged divisor contributes the genuine local factor \(1/(r-1)\). The ratio of its band mass to the normalizing \(\sum 1/r\) is \(1+O(\exp(-cL^{.1}))\). Distinct families therefore have first and mixed moments \(1+O_K(\exp(-cL^{.1}))\). The same-band second moment is bounded, because in each color the reciprocal lcm sum is at most
\[
 \sum_r\frac1{r-1}+
             \left(\sum_r\frac1{r-1}\right)^2 .
\]
Expand \(|\bar W-1|^2\) in the actual \(\log p\) sum using these estimates and divide the off-diagonal and diagonal terms by \(J_0^2\). This proves (5), with the diagonal loss \(J_0^{-1}\) and negligible fixed-model and BV errors.

On averaging (4) and using (5) by Cauchy and \(|f|\le1\), we find \(\left|\sum_{p\in I}(\log p) f(P-p)\right|\ll P/\sqrt{\log L}\). Since \(\log p=L+O_J(1)\) on \(I\), the prime number theorem gives (1). Finally, the elementary identity \(\mu^2(y)=\sum_{d^2\mid y}\mu(d)\) and true prime BV give the squarefree mass in (2): truncate \(d\) at \(L^C\) with a large fixed \(C\), use the reduced classes \(p\equiv P\bmod d^2\) for \((d,P)=1\), and bound the tail by the number of integers in \([1,P]\) divisible by some \(d^2\), at most \(P\sum_{d>L^C}d^{-2}\). Classes with \((d,P)>1\) are absent for sufficiently large \(P\), since actual primes in the fixed central interval cannot divide \(R\le L^B\). The resulting Euler product is uniformly bounded below by a positive constant since \(2\mid P\), and (1) separates both signs.

## Comparison and limits

[Lü, Wang and Wu, arXiv:2610.20242v2](https://arxiv.org/html/2610.20242v2), Theorem 1 concerns a fixed shift; Remark 3 discusses an extension with a zero-free hypothesis. Jizhou Guo's October 2026 *The Möbius function at \(N-p\)*, v2, is directly relevant: its primary [repository description](https://github.com/aster2024/openai-math-followups), indexed before the repository became unavailable, reports the same order of bound in a general reflected range under an external zero-free hypothesis and describes two target-radical versions retaining an assumption about arguments of Lü–Wang–Wu. We could not retrieve its precise v2 theorem from the now unavailable repository and make no claim about its exact radical thresholds or priority. The mechanism here is the alternate high-tag-moment and restricted-Bessel bound for the full target projector, with the projected Jiang–Lau–Lü minor input. It establishes (1) only on the stated structured targets. The genuine near-full second-prime conclusion of the companion note, with its specified small multiplier, is an additional result, not a consequence of (1).

At every sufficiently large \(P\) in scope, the two signs in (1) are compatible with all negative rows having at least three factors. The present marking mechanism would vanish on a prime complement before the unweighting, and the final error in (1) is larger than the natural weighted binary-pair scale after converting to ordinary counts. Thus (1) does not settle binary Goldbach at any collection of targets.
