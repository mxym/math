# A symmetric quadratic score and a growing reflected even-rank limit

This is a companion to [NarrowQuotientScoreAndMarkedRanks](NarrowQuotientScoreAndMarkedRanks.md). It combines a different **exact** prime-free correction with complete removal of a growing band of reflected even ranks. It neither pays the higher-rank/short-quotient-factor remainder nor establishes Goldbach.

## 1. Centered change of score with no reflected-prime term

Use the same true \(N=2x\), \(L=\log x\), \(T=\log L\), \(M_N=\mathfrak S(N)x/(2L)\), \(x^{.10}<s<x^{.14}\) prime, \(n=sq\in(x/2,x]\), \(m=N-n\), \((n,N)=1\), and weights \(W_s(q)\). Keep \(B_q=x^{.501}, B_m=x^{.5+T^{-20}}, z_q=\exp(L/T^3), z_m=\exp(L/T^{23})\), the exact rough guards \(\rho_j=1_{P^->z_j}\), \(T_q,T_m\) from [JointShortDivisorProjection](JointShortDivisorProjection.md), and \(C(q;s)\) from the Narrow Quotient note with \(\delta=T^{-1/2}\). Define the symmetric polynomial \(g(t)=8t(1-t)\) and the genuine short score
\[
 S_2(m)=\sum_{d\mid m,\ d<m/B_m}\mu(d)\,g(\log d/\log m).
\]
In particular \(g(0)=0\), so \(S_2=0\) on prime \(m\), just as \(C-T_q=0\) on prime \(q\). The centered null proof in Sections 2–3 of the Narrow Quotient note gives
\[
 \sum_{\substack{q,m\ \mathrm{composite},\ P^+(q)\le B_q\\\rho_q(q)\rho_m(m)=1}}
     W_s(q)(\log m)(C(q;s)-T_q(q))S_2(m)=O_A(xL^{-A}).                 \tag{1}
\]
For this score its proof is unchanged except that there is **no** extra prime label of \(d_m\) or interval \(m\le B_m r^2\): the new weight is a bounded smooth function of the genuine \(d_m,m\). The all-integer CRT, the actual giant-quotient prime \(p>x^{.501}\) which is tested by product BV for \(n=p(su)\), the exact cutoff \(s p(u/d)>x^{1-\delta}\), and the restored coprime short/long \(\mu\) principal all apply to this simpler weight. In particular the true reflected-prime subtraction that would obstruct the same argument with \(T_m\) is **absent**. The squareful rough errors still have arbitrary log reserve by bounded divisor moments.

Thus the exact threshold \((J+.010)M_N\) with strict margin can be tested against the original joint squarefree score with \(T_qT_m\) replaced by
\[
                  T_q T_m+(C-T_q)S_2.                               \tag{2}
\]
As before this is a competing representation, not additive credit; the extra high-reflected rank-two and rank-three rows of (2) are kept literally. For squarefree \(m=r v\) with a true giant \(r>B_m\), the complete divisor sum on \(v\) vanishes for \(\omega(v)\ge3\) because its weight is a polynomial of degree two in the prime log bits. For \(v=p_1 p_2\) it equals \(-16\log p_1\log p_2/(\log m)^2\), and for \(v=p_1\) it is \(-g(\log p_1/\log m)\). Both are nonpositive. These are the true high rank-three and high semiprime corrections, not terms of a model.

On a squarefree smooth reflected rank three let \(k\) be the number of singletons \(p<m/B_m\). No two-prime divisor contributes and the least singleton always qualifies. Consequently \(T_m=1-k\), and \(S_2=-8\sum_{i\text{ qualifying}}t_i(1-t_i)\) for \(t_i=\log p_i/\log m\). If \(k=3\), \(\sum t_i=1\) and each \(t_i<.5\), so \(S_2\le-4\le T_m\). If \(k=2\), the omitted factor is \(\le B_m\) and has normalized logarithm at most .51, so the two retained \(t_i<.5\) sum to at least .49, implying \(S_2\le-1.96\le T_m\). If \(k=1\), \(S_2\le0=T_m\). Hence all these statements include the prime collar literally. On actual quotient rows with \(P^-(q)>x^\delta\) and \(\Omega(q)\le4\), we have \(C=1,T_q\le1\) as before. Therefore (2) is nonpositive on **all reflected rank three**, including the new high rows, and on high reflected semiprimes, in this quotient sector. The balanced reflected semiprime collar is unchanged (\(S_2=0\) there), already \(o(M_N)\) in the original whole ledger. No sign extension to arbitrary higher quotient rank is made.

## 2. Absolute removal of growing even ranks on actual joint rows

Put \(K_* = \lfloor4\log T\rfloor\). Retain both exact rough guards and all literal unit and central conditions. The entire part of (2) with squarefree even \(4\le\Omega(m)\le K_*\) is \(O(T^{-1/5}M_N)\) in absolute sum, with no bound on \(\Omega(q)\). The same estimate holds for its \(T_qT_m\) part alone in the original joint ledger (including even rank two there). In particular this result is not a further positive-part charge for the main higher-rank signed term.

For squarefree even \(m\), complementary divisors outside the closed band \([m/B_m,B_m]\) have equal Möbius sign on either side. For the constant weight this gives \(2T_m=-\sum_{d\mid m,\ m/B_m\le d\le B_m}\mu(d)\), and for the symmetric quadratic it gives
\[
        2S_2=-\sum_{d\mid m,\ m/B_m\le d\le B_m}\mu(d)g(\log d/\log m)
                    \qquad (\Omega(m)\ge4\text{ even}).
\]
The latter uses the exact zero of the full quadratic Möbius moment for \(\Omega\ge3\). Both identities include strict or closed endpoints as shown. Therefore their signs can be discarded at a cost of one actual integer divisor \(d\) in the global range \([x^{1-b_m},x^{b_m}]\) with \(m=d v\), \(P^-(d),P^-(v)>z_m\). The coefficients \(|C|+|T_q|\le 2\cdot2^{\omega(q)}\) and \(|g|\le2\) suffice for this upper. Use one shared exponential tilt at \(\lambda=1/12\): on the actual squarefree rank bound, \(1\le\lambda^{-K_*}\lambda^{\omega(d)+\omega(v)}\). We only drop other restrictions **after** this inequality on actual rows; no repeated-prime correction is hidden in the tilt.

At fixed \(s,d\), \((sd,N)=1\), \((s,d)=1\) by the physical units. Write \(q=q_0+d j\), \(v=(N-s q_0)/d-s j\), with \(0\le q_0<d\) and \(q_0\equiv N\overline s\pmod d\). Both forms are primitive since the constants are units at the corresponding slope factors; their determinant is \(N\). Their free length is \(Y\asymp x/(s d)\gg x^{.34}\) at comparable height. Apply corrected Henriot to the nonnegative multiplicative weights \(2^{\omega(q)}\rho_q(q)\), \(\lambda^{\omega(v)}\rho_m(v)\), enforcing unit masks at primes of \(N\). The root/discriminant calculation is as in [UngatedReflectedRankProjection](UngatedReflectedRankProjection.md). In addition to the harmless \(s\)-factor, the extra local ratio for primes of the *composite* \(d\) is exactly \(\prod_{p\mid d}(p-1)/(p-2)=1+o(1)\), since each \(p>z_m\) is large and \(\omega(d)\le K_*\). At such a prime one affine form is nonzero constant and the other has one root. This also justifies dropping the exact upper/lower band relation to bound the actual rows after retaining the units. The height and short-interval hypotheses are fixed; the local weights have uniform class constants. With
\[
 P_m=\sum_{z_m<p\le2x}\frac1p=23\log T+O(1),\qquad
 P_q=\sum_{z_q<p\le2x}\frac1p=3\log T+O(1),
\]
this gives \(\ll \mathfrak S(N)Y L^{-2}\exp(2P_q+\lambda P_m)\).

It remains to sum the genuine near-half \(d\) harmonics. Its largest prime \(p\) is \(\ge x^{.499/K_*}\). Fix the complementary true \(a=d/p\) first (its primes all exceed \(z_m\)). The allowed moving \(p\)-interval is inside \([x^{1-b_m}/a,B_m/a]\) and has log-length \(\le2 T^{-20} L\), with \(\log p\ge .499 L/K_*\) on the portion that counts. Ordinary PNT and partial summation thus give prime harmonic \(\ll K_* T^{-20}+O_A(L^{-A})\), uniformly after the endpoint cuts and also if the interval is empty. The log-reserve is valid because \(K_*=O(\log T)\). Ignoring other rank/mask restrictions only in this positive upper, \(\sum_{a\text{ squarefree},P^-(a)>z_m}\lambda^{\omega(a)}/a\ll\exp(\lambda P_m)\) (restrict primes to at most \(2x\)). Therefore the full tilt-weighted \(d\) harmonic is bounded by \(\ll\lambda (K_* T^{-20}+L^{-A})\exp(\lambda P_m)\), without any multiplicity count exceeding the one chosen largest prime.

Now include the physical \(\log m\ll L\), the bounded \(\sum_s1/s\) harmonic, and the common \(\lambda^{-K_*}\) rank charge. The normalized upper is
\[
 \ll (K_* T^{-20}+L^{-A})\,T^{6+46/12+4\log12}.
\]
Since \(-20+6+46/12+4\log12<-0.22\) (\(\log12<2.485\) suffices), the extra \(K_*\) leaves \(O(T^{-1/5})\) for all sufficiently large \(x\). This proves the growing-rank claim. Its overlap with the signed raw-neck slices must not be counted twice; use these absolute even ranks first and keep any previous raw signed theorem only on its original full scope unless its restricted rank variant is separately justified.

No analogous bound is provided for the larger even ranks, the remaining odd ranks, or the true high-reflected rank-two correction on the unpriced quotient profiles. The ordinary Goldbach question is unchanged.
