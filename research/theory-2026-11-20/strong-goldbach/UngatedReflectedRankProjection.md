# An ungated reflected-rank projection by matching both prime slopes

This is a new projection of the **whole** fixed-target centered ledger. It requires no marked large prime on the quotient leg. It removes **every** reflected composite with a factor above a freely chosen near-half threshold, including all unbalanced semiprimes. The surviving near-half semiprimes have a uniform cap arbitrarily small relative to the original reference. The signed rank-three-and-higher remainder is not estimated here.

## 1. The observable and its unchanged calibration

Let \(N=2x\) be even, \(L=\log x\), \(M_N=\mathfrak S(N)x/(2L)\), and keep the genuine primes \(x^{.10}<s<x^{.14}\), \(n=sq\in(x/2,x]\), \(m=N-n\), and \((n,N)=1\). Put \(W_s(q)=W(\log s/\log(sq))\), where \(W(t)=(1-t)(1-2t)^2\). Write
\[
 H_g(y)=\sum_{d\mid y}\mu(d)g(\log d/\log y),\qquad
 Z_N=\sum_{s,q\text{ prime}} W_s(q)\Lambda(m).
\]
Choose smooth compactly supported real kernels \(h,f\) satisfying
\[
       h(t)=f(t)=1-t\quad\text{near }0,\qquad
       h(t)=0\ (t>c_h),\quad f(t)=0\ (t>c_f),
       \quad 0<c_h\le .400,\quad 0<c_f< .001.
\]
No restriction from earlier large-\(p\) arguments is imposed on \(h\). In particular the old short flat-at-zero quotient kernel is **not** being used. The true measure condition is unchanged, and the original signed observable remains \(E_N=Z_N-(J+o(1))M_N\), with \(J=\log(7/5)-.1408\). In these new kernels one has, at each even target,
\[
 E_N=\sum_{q,m\text{ composite}} W_s(q)(\log m)H_h(q)H_f(m)
                        +O_A(xL^{-A}).                               \tag{1}
\]
Here and subsequently sums include all original \(s,q\) rows unless stated otherwise.

To audit the calibration directly, let \(T_{AB}\) sum \(W_s(\log m)H_h H_f\) over all rows, \(T_{qP}\) the same weight with the \(q\)-score replaced by \(1_{q\text{ prime}}\), \(T_{mP}\) with the \(m\)-score replaced by \(1_{m\text{ prime}}\), and \(T_{PP}\) with both replacements. Since each translated score equals 1 on its own prime, the right side of (1) before the error is **exactly** \(T_{AB}-T_{qP}-T_{mP}+T_{PP}\). In \(T_{mP}\), replacing the prime log indicator by \(\Lambda(m)\) costs \(x^{1/2+o(1)}\), by counting proper prime powers and the divisor multiplicity in \(N-m\). Likewise \(T_{PP}=Z_N+O(x^{1/2+o(1)})\).

The equality \(T_{AB}-T_{mP}=O_A(xL^{-A})\) holds without any assumption on the slope of \(h\). For each opened \(d\mid q\), the test in \(m\) has bounded variation and the modulus \(a=sd\) is \(\ll x^{.484}\). Ordinary maximal prime BV models \(m\equiv N\pmod a\) by \(1/\phi(a)\). In the integer part of \(T_{AB}\), open \(e\mid m\); it is necessarily coprime to \(Na\), and the coprime CRT density per \((a,e)\) is \(\phi(N)/(Nae)\) if \((a,N)=1\). The floors cost \(x^{.485+o(1)}\), and each \(a\) has a bounded number of original \(s\)-labels since \(s>x^{.10}\). The uniform harmonic identity for the slope \(-1\) kernel \(f\), restated below in (4), gives exactly \(1/\phi(a)\) after multiplying by \(\phi(N)/(Na)\). Logarithmic harmonic weights cost at most powers of \(L\). This is the same exact smooth-score replacement as in [BilateralSmoothRoughReduction](BilateralSmoothRoughReduction.md), using its original centered short-divisor term. Likewise \(T_{qP}=Z_N-E_N+O_A(xL^{-A})\): this is the established difference between the original short reflected subtraction and its smooth replacement with any slope \(-1\) \(f\) of admissible support, against the true \(s q\) prime-product row. It follows also by applying ordinary prime BV to \(q\) at fixed \(s\), with reflected moduli at most \(x^{.001+o(1)}\), evaluating the same local harmonic principal; the previous short subtraction has that principal. These equalities prove (1); no guessed main-term change, or value of \(h'(0)\) in the joint CRT, is used.

## 2. Distribution of an exactly centered quotient score

Define the **fixed** coefficient, independent of the reflected modulus,
\[
                G_h(q)=H_h(q)-1_{q\text{ prime}} .                    \tag{2}
\]
It agrees with \(H_h\) on every composite (including prime powers), and is exactly zero on primes. This is why no large \(p\)-label is needed. Let the physical reflected test be a sum over \(Q\mid m\), \(Q\le x^{1/2-\delta}\) for a fixed \(\delta>0\), with \((Q,N)=1\) dictated by the row condition. We allow at most a fixed power of \(L\tau(Q)\) labels per \(Q\), smooth bounded-log-divisor weights in \(s,q,Q,m\) (and in the label variables), and a bounded number of potentially label-dependent intervals in \(n\) per label. Here “smooth” means that in normalized logarithmic coordinates in dyadic boxes each fixed derivative has log-power size, so compact Fourier separation has log-power mass and log-height truncation with arbitrary log reserve. The proof below only needs the explicit weights in (5).

The true source is \(n=s\cdot q\). Its \(s\)-factor is a prime Siegel–Walfisz coefficient (twists and the physical target prime exclusions follow by partial summation and deleting at most \(O(L)\) primes). Both contributing lengths are polynomial: \(s\ge x^{.10}\), \(q\gg x^{.86}\). Its \(q\)-factor (2) is divisor-bounded and may be signed, as permitted in [Maynard's Lemma 8.9](https://ora.ox.ac.uk/objects/uuid%3A39a52f47-3770-4ddd-b7a2-b2a4f7300931/files/srj4305733). In particular, no SW or primality assumption is made on the full \(q\)-coefficient. Use the lemma with maximum reduced residue, hence with the true residue \(N\), and coprime model \(1_{(n,Q)=1}/\phi(Q)\). The factor masks \((s,N)=1\) and \((q,N)=1\) remain in the coefficients; in the model both also must be units at \(Q\). If \(s\mid Q\), both contributions are absent.

For moving intervals, round their endpoints in the central \(n\)-window to a grid of mesh \(xL^{-K}\) and smooth each resulting cutoff. For a fixed reduced \(Q\), the original opened source at \(n\) in a rounding strip is bounded by fixed divisor powers and log powers. Shiu's short-interval divisor upper in the power-reserved progression ([Fouvry–Radziwiłł, Lemma 2.2](https://arxiv.org/pdf/1812.00562v2)) then costs \(O(xL^{-K+O(1)}/\phi(Q))\) per label. The analogous unprogressioned bound also works for the coprime model with factor \(1/\phi(Q)\). Summing \(\tau(Q)^C/\phi(Q)\) and the log-power part of the label bounds costs only log powers, and \(K\) can be made arbitrary. After smoothing, separate the continuous factors by compact Fourier expansion on dyadic logarithmic boxes. Their derivatives meet the stated requirements because \(s,q,m\) are in the physical ranges; the \(n\) phase factors into \(s\) and \(q\) phases. The label phases and signs are retained in their respective actual moduli. There are only log-power many prefixes and dyads. To pay the remaining \(\tau(Q)^C\) multiplicity, let \(\mathcal E(Q)\) be the absolute BV discrepancy of a separated term. Shiu, and the unprogressioned divisor bound in the principal, give \(\mathcal E(Q)\ll x L^{O(1)}/\phi(Q)\), including twists in absolute value. By Cauchy–Schwarz, \(\sum_Q\tau(Q)^C\mathcal E(Q)\le(\sum_Q\mathcal E(Q))^{1/2}(\sum_Q\tau(Q)^{2C}\mathcal E(Q))^{1/2}\); the second factor uses the harmonic divisor moment and the first factor has arbitrary log reserve from the unweighted lemma. Thus the total BV error is \(O_A(xL^{-A})\), and we can restore the unsmoothed weights and literal ranges in the principal with the same error.

It remains to see that the principal of (2) vanishes. At each fixed \(s,Q\) and every allowed label, put \(K_0=NQ\), \(Y=x/s\); the relevant \(q\)-interval satisfies \(q\asymp Y\) with \(Y\gg x^{.86}\). Let \(\psi\) be the physical test after fixing the labels, with log-power size and total variation on that interval. For \(q\asymp Y\) the opened \(h\)-divisors satisfy \(d\ll Y^{.400}\). For each \((d,K_0)=1\), count coprime multiples \(q=du\) with density \(\phi(K_0)/(dK_0)\) and elementary floor \(O(\tau(K_0))\). If \((d,K_0)>1\) there are none. By partial summation the floors cost \(Y^{.400}x^{o(1)}\) times log powers, power-small relative to \(Y\); the derivative of \(h(\log d/\log q)\) is uniformly bounded after scaling by \(Y\). Extending the harmonic coefficient by zeros, the principal of the integer score is
\[
 \int \psi(y)\frac{\phi(K_0)}{K_0}
       \sum_{(d,K_0)=1}\frac{\mu(d)}d h(\log d/\log y)\,dy
       +O_A(YL^{-A}).                                                 \tag{3}
\]
The finite, coprime prime harmonic identities used here are
\[
 \sum_{(d,K_0)=1}\frac{\mu(d)}d\,g(\log d/\log y)
  =\frac{K_0}{\phi(K_0)\log y}+O_A(L^{-A}),\qquad g=h\text{ or }f,       \tag{4}
\]
uniformly for polynomial \(K_0\), \(\log y\asymp L\). For completeness, at a small fixed polynomial cutoff inside the exact affine region, replace the two finite weighted Möbius harmonics by their complete mean values 0 and \(-K_0/\phi(K_0)\) for \(\mu(d)/d\) and \(\mu(d)\log d/d\) respectively. The latter sign is obtained by differentiating the Euler product \(\zeta(1+w)^{-1}\prod_{p\mid K_0}(1-p^{-1-w})^{-1}\) in \(w\) at 0. The uniform tails on polynomial cutoffs follow from coprime Möbius PNT, by convolving with the indicator of integers supported on prime divisors of \(K_0\) and splitting that convolution at the square root of its endpoint. The small-convolution harmonic weight costs log powers; the large range has polynomial decay times \(x^{o(1)}\) from Rankin at exponent \(1/4\) (the product involves \(O(L)\) prime factors with \(\log K_0=O(L)\), so its exponential is \(x^{o(1)}\)). Partial summation controls the remaining polynomial range of the smooth test. This also proves (4) for \(f\) as used in Section 1. Ordinary PNT with arbitrary log reserve gives the same principal \(\int\psi(y)dy/\log y\) as (3) on the true prime leg of (2), since excluded primes divide polynomial \(K_0\) and contribute only \(O(L^{O(1)})\). The full coprime model of (2) is therefore \(O_A(YL^{-A})\). Summing over \(s\) and \(Q\), with the outer factor \(1/\phi(Q)\) and bounded label multiplicities, preserves arbitrary log reserve. This proves the signed null for the specified physical weights.

## 3. Exact deletion of every reflected composite with a high prime

Fix \(0<\epsilon<.01\), write \(b=1/2+\epsilon\), \(B=x^b\), and choose the reflected kernel so that \(0<c_f<\min(.001,\epsilon)\). Keep the quotient kernel \(h\) fixed independently of these choices. For every central \(m\) put
\[
           T_b(m)=\sum_{\substack{d\mid m\\d<m/B}}\mu(d).
\]
The strict moving cutoff is essential for the boundary statements below. The term \(d=1\) is present for every central \(m\), and \(T_b(m)-1\) is identically zero on prime \(m\). Thus the composite restriction on \(m\) can be dropped when adding the following difference to (1):
\[
  \sum_{s,q}W_s(q) G_h(q) (\log m) H_f(m) [T_b(m)-1].                  \tag{5}
\]
Open the two **actual** divisors \(d>1\), \(e\mid m\), with weights \(\mu(d)\), \(\mu(e) f(\log e/\log m)\). The true reduced-congruence modulus is \(Q=\operatorname{lcm}(d,e)\). Its support is
\[
             Q\le d e\ll x^{1-b+c_f}<x^{1/2-\delta}
\]
for fixed power reserve \(\delta>0\), and for fixed \(Q\) there are at most \(\tau(Q)^2\) pairs of labels \((d,e)\). Overlap of labels is not discarded. Impose \((Q,N)=1\) before taking the coprime model. The true endpoint \(d<m/B\) is exactly \(n<N-Bd\) and the remaining weight is of the smooth kind of Section 2. That section gives the signed null (5) \(=O_A(xL^{-A})\), with all prime exclusions and floors already accounted for. Consequently
\[
 \boxed{\quad E_N=
   \sum_{\substack{q,m\text{ composite}\\ P^+(m)\le B}}
       W_s(q)(\log m)H_h(q)H_f(m)T_b(m)+O_A(xL^{-A}).\quad}             \tag{6}
\]
Indeed, if \(m\) is composite and \(r>B\) is a prime divisor, then \(r>m/B\) (as \(B^2>1.5x\)). It has exponent one, and no divisor carrying \(r\) is in \(T_b\). Every divisor of \(m/r\) is strictly below \(m/B\), so the complete sum \(\sum_{d\mid m/r}\mu(d)\) is zero. This reasoning does not impose squarefreeness on the cofactor. It deletes the **entire** high reflected spectrum of actual composite rows, not merely the high rank-two rows, without leaving a separately additive mark collar.

## 4. The only reflected semiprimes left, and their actual cost

If \(m=r v\) is a true semiprime with \(P^+(m)\le B\), then both prime factors lie in \([m/B,B]\subset[x^{1-b},x^b]\), so \(T_b(m)=1\) exactly, including equality at the endpoint and repeated equal factors. On this support \(H_f(m)=1\), since every nonunit divisor has normalized logarithm larger than \(c_f\). The semiprime contribution to (6) therefore has absolute value
\[
          \ll_h \epsilon M_N + O_{A,h,\epsilon}(xL^{-A}),              \tag{7}
\]
where the coefficient of \(\epsilon M_N\) is independent of \(f\) and of \(\epsilon\in(0,.01)\). This independence is important: (7) does not use a Fourier constant for a shrinking reflected kernel.

To prove (7), overcount by choosing either true prime factor \(r\in[x^{1-b},x^b]\) of \(m\). For fixed \(s,r\) on the physical unit support we have \((sr,N)=1\), \((s,r)=1\), and
\[
      q=q_0+rj,\qquad v=v_0-sj,\qquad
      q_0\equiv N\overline s\pmod r,\quad
      v_0=(N-sq_0)/r,quad 0\le q_0<r.
\]
In particular \(v\equiv N\overline r\pmod s\) on these rows. Each form is primitive because \(q_0\) is a unit at \(r\) and \(v_0\) a unit at \(s\); their determinant is \(N\). The fixed central window gives \(j\) in an interval of length \(Y\asymp x/(sr)\gg x^{.35}\) at comparable height. The coefficient heights are \(O(x^2)\) for the product of the forms. These reserves are independent of \(\epsilon\). A true prime \(v\ge x^{1-b}\) is bounded above by the multiplicative rough indicator \(1_{P^-(v)>x^{.4}}\); do not use \(1_{v\text{ prime}}\) as a multiplicative weight.

For \(H_h\) use absolute Fourier inversion with the local majorants \(a_\xi(\ell^k)=\min(2,2|\xi|\log\ell/L)\), as in [BilateralSmoothRoughReduction](BilateralSmoothRoughReduction.md), but on the just specified affine forms. Impose zero local weights at \(\ell\mid N\) to retain the two physical unit masks. The product discriminant is \(N^2\). Every nonconstant term in the corrected discriminant factor is zero under the imposed weight at a prime dividing \(N\), leaving local correction 1. Write \(\rho(\ell)\) for the number of residue classes in which either affine form vanishes. The remaining sieve local factor normalized by the dimension-two Mertens factor is \((1-\rho(\ell)/\ell)/(1-1/\ell)^2\). For odd \(\ell\nmid Nsr\) it equals \(\ell(\ell-2)/(\ell-1)^2\), since the roots are distinct. For odd \(\ell\mid N\) both slopes are units, the roots coincide, and it equals \(\ell/(\ell-1)\), the usual local factor in \(\mathfrak S(N)\). For \(\ell=s,r\), exactly one form is an everywhere nonzero constant, giving the same \(\ell/(\ell-1)\), or an extra ratio \((\ell-1)/(\ell-2)\) relative to \(\mathfrak S(N)\). These two ratios are uniformly bounded. At \(\ell=2\), both odd slopes are units and the roots coincide because \(N\) is even: the normalized local factor is \(2\), exactly the factor of \(2\) in \(\mathfrak S(N)\); Henriot's product starts above the degree 2, so omitting it changes only the corresponding bounded absolute factor. Completing the large-prime tail of the convergent twin factor changes it by a bounded factor, while omitted divisors of \(N\) have corrective ratios at least 1. Applying [Henriot's Theorem 5 and Corollary 2](https://arxiv.org/pdf/1102.1643) with the [published correction](https://doi.org/10.1017/S0305004114000280) gives, on the interval at fixed \(s,r\), the bound
\[
   \ll Y\mathfrak S(N)L^{-2}(1+|\xi|)^2.
\]
The rough majorant contributes only bounded extra Euler weight, since its primes are above \(x^{.4}\). The constants in the weight and height hypotheses are uniform in the moving target, \(s,r\), and \(\epsilon\). This is an upper over all integer \(q\), so it also holds after the original composite restriction. Integrating the rapidly decaying \(\widehat h(\xi)\), multiplying by \(\log m\ll L\) and the bounded \(W_s\), and summing \(s,r\) proves (7): \(\sum_s 1/s=O(1)\), and the ordinary prime number theorem and partial summation give
\[
   \sum_{x^{1-b}\le r\le x^b,\ r\text{ prime}}\frac1r
    =\log\frac{b}{1-b}+O_A(L^{-A})\ll \epsilon+O_A(L^{-A})
\]
with uniform endpoint power reserves. Possible equal-factor semiprimes are included in this upper.

## 5. The remaining signed criterion and its exact rank-three profile

Given any tolerance, first fix \(h\), then choose fixed \(\epsilon>0\) sufficient for (7), and only then choose an admissible \(f\). For all sufficiently large \(x\) after those choices, the only unpriced signed contribution to (6) is
\[
   \sum_{\substack{q,m\text{ composite}\\ P^+(m)\le x^{1/2+\epsilon}\\\Omega(m)\ge3}}
      W_s(q)(\log m)H_h(q) H_f(m)T_b(m).                              \tag{8}
\]
The sufficient eventual positivity criterion is a fixed-margin upper bound below \(.010 M_N\) for (8) plus the small allowance (7); the original reference and inequality are unchanged. In particular one need not pay any of the old two-sided large-prime tag packets in addition to (8).

There is an exact first-rank sign. On \(\Omega(m)=3\), every two-distinct-prime product divisor of \(m\) is \(m/\ell\) for a prime \(\ell\le B\), hence at least \(m/B\); the same conclusion applies if one of the three prime factors is repeated. The least prime factor is below \(m/B\) because \(b<2/3\). Thus
\[
 T_b(m)=1-\#\{\ell\mid m:\ell\text{ prime},\ \ell<m/B\}\le0
                   \qquad(\Omega(m)=3,\ P^+(m)\le B).                 \tag{9}
\]
If \(0\le f\le1\) on nonnegative arguments, at most one distinct prime factor of such an \(m\) can be active in \(H_f\): two would force \(m\ll x^{b+2c_f}<x\). Thus \(H_f(m)\ge0\). A positive signed term on this entire rank-three sector requires genuinely negative \(H_h(q)\); it is not a bound on the difference of the two physical signs. No corresponding sign for all higher ranks, and no Goldbach conclusion, is asserted.

This subtraction relies on the new slope-matched whole source \(sG_h(q)\). It is not available from the earlier flat-at-zero quotient score with an artificial low-factor mean, and does not use either the earlier \(p> x^{.359}\) marked projection or a binary Liouville correlation.

## Related moving-endpoint work

[Ramón Moya, *A Moving-Cut Correction to the Huang–Li Conditional Goldbach Argument*, v1.0.0 (August 14, 2026)](https://zenodo.org/records/21939906) addresses a different large-divisor switch. The displayed endpoint in the Huang–Li argument must become \(n<N-\alpha k\) after \(k=(N-n)/d\), not the fixed endpoint \(n<N\). Moya repairs that conditional argument using its original Möbius-twisted distribution hypothesis uniformly in the truncation parameter. The moving endpoint here is different, is retained exactly as \(n<N-Bd\) in (5), and is estimated with ordinary unconditional convolution BV at a fixed sub-half power level. We do not claim Moya's twisted tail is estimated by this projection.
