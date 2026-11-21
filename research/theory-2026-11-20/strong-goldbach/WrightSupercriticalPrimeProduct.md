# A genuinely supercritical unmarked prime-product sector

The double-Cauchy diagonal in [SpectralSubcriticalPrimeProduct](SpectralSubcriticalPrimeProduct.md) stops at \(pr\asymp x\). In this sector a different orientation, with the **unchanged true prime \(p\) as the long Siegel–Walfisz source**, cancels genuine \(pr>x\) contributions. No cofactor is required to be prime or to contain an extra tag.

## 1. Statement

Keep the same short smooth \(h,f\), their respective exact near-zero values \(1,1-t\), positive supports at most \(.001\), and the \(a=.359,\ B=.499\) doubly high ledger. Thus \(N=2x\), \(L=\log x\), \(s\) is actual prime with \(x^{.10}<s<x^{.14}\), \(n=sq\in(x/2,x]\), \(m=N-n\), \((n,N)=1\), and
\[
 X_h(s,q)=W_s(q)(\log m)H_h(q)H_f(m)
\]
with all functions and logarithm denominators exactly as in the subcritical note. Take any fixed independent closed exponent rectangle for the actual primes \(p\mid q,\ r\mid m\) lying strictly in
\[
 \beta>.499,\qquad \beta+.001<\alpha,\qquad
           34\alpha-17<\beta,\qquad \alpha+\beta>1,
 \qquad (\alpha,\beta)=(\log_x p,\log_x r).                      \tag{1}
\]
Then at each even target, for every fixed \(C>0\), its complete original contribution is
\[
 \sum X_h(s,q)\frac{\log p}{\log q}\frac{\log r}{\log m}
              =O_{C,h,f,\mathrm{rectangle}}(xL^{-C}).            \tag{2}
\]
All \(s\) in the original band and both genuine cofactors are permitted. The constraints imply \(.500<\alpha<17/33<.516\), \(r<p\), and \(p,r\) are proper tags. In particular \(.508\le\alpha\le.513,\ .501\le\beta\le.506\) is such a rectangle, with \(pr\ge x^{1.009}\).

## 2. The applicable nearly balanced moving-residue bound

Write \(Y=UV\) for the actual product of the two source dyad lengths, \(V\) the long Siegel–Walfisz factor, and \(R\) the modulus size. We use [Wright, *Trilinear Kloosterman fractions II*, arXiv:2608.27732v1, Theorems 2.1–2.2](https://arxiv.org/pdf/2608.27732v1), for real divisor-bounded factors with the stated Siegel–Walfisz condition; split any complex factor into its real and imaginary parts. The centered discrepancy is \(1/\varphi(Q)\) times the **actual coprime** mass at each integer modulus \(Q\). In the range
\[
 V^{34}Y^{-17+\varepsilon}\le R\le VY^{-\varepsilon},
 \qquad V^{23/8}Y^{-1+\varepsilon}\le R,\qquad
 Y^{3/8}\le U\le Y^{1/2}\le V,                                  \tag{3}
\]
the proof gives the absolute sum of discrepancies \(O_A(Y(\log Y)^{-A})\) for any \(A\). The auxiliary second lower bound in (3) is included explicitly to control the second final error monomial.

We need the constant-factor residue range \(1\le |a|\le C_0 Y\), with \(C_0\) fixed, not just the printed \(1\le |a|\le Y\). Here are the requisite proof checks. The [Fouvry–Radziwiłł original dispersion proof, arXiv:1812.00562v2](https://arxiv.org/pdf/1812.00562v2), Sections 3.1–4.3, supplies the \(U,V\) estimates and all the unreplaced \(W\) terms in Wright. (In this paragraph \(U,V,W\) from those papers denote the three dispersion terms.)

* In FR §3.1, the \(n\mid a\) part is removed by the divisor bound on \(mn-a\ne0\), with an extra contribution \(O(Q)\) for \(mn=a\). The same argument works for bounded \(C_0\). The large-common-divisor removals (23)–(26) also only require the divisor bound on the nonzero \(|mn-a|=O_{C_0}(Y)\); \(U\) in (13), the zero \(V\) term, the zero \(W\) term and (32) have no size dependence on \(a\), only the coprimality mask on the modulus. The Poisson remainder is uniform in the residue. The error term in FR (26) is kept with its **negative** power \(-\varepsilon/2\), as in the full FR (43) calculation; Wright's final schematic display drops that power while referring to the same unreplaced terms.
* In FR (18)–(20), reciprocity gives a smooth factor \(e(ah/(n_1t))\), \(t\asymp R,\ n_1\asymp V,\ |h|\le (R/U)Y^{\varepsilon_0}\). Its differentiated loss is still \(O_{C_0}(Y^{\varepsilon_0})\) by \(UV=Y\). The remaining incomplete Weil gcd estimate is averaged by divisors of \(a\), whose cardinality is \(Y^{o(1)}\) uniformly for the enlarged range. The estimate (19) can safely keep \((a h,n_1)\): bound its square root by \((a,n_1)^{1/2}(h,n_1)^{1/2}\), open \(b\mid(a,n_1)\), count the \(n_1\) multiples at cost \(O(V/b)\), and use \(\sum_{b\mid a,\ b\le 2V} b^{-1/2}\le \tau(a)\). For each \(n_1\), opening \((h,n_1)\) costs at most \(O(H\,\tau(n_1))\) since \(h\ne0\). This recovers (19) without needing \((n_1,a)=1\).
* Wright changes only the off-diagonal \(W\) Fourier term, with the same smooth reciprocal factor as FR (39). Since the actual difference is \(\asymp rR\), its derivative scales in Wright (8) are unchanged with an \(O_{C_0}(1)\) factor per fixed derivative: the dimensionless phase is \(O_{C_0}(Y^{\varepsilon_0})\) before the small-divisor losses. The Kloosterman-fraction bound in Wright Theorem 2.1 retains \((1+|\vartheta|A/(MN))^{1/2}\). Here it is \(Y^{O(\varepsilon_0)}\), with a constant depending on \(C_0\), because the switched divisor satisfies \(r\ll V/R\), \(H=(R/U)Y^{\varepsilon_0}\), and the two trilinear length denominators are \(V^2\) up to the source's existing small divisors. Indeed \(|a|rH/V^2\ll_{C_0}Y^{\varepsilon_0}\). CRT residue restrictions are unaffected by the size of \(a\).
* Keeping the strict saving from FR (26), the two Wright nonzero \(W\)-terms after the final normalization by \(U^2V^2\) are, before freely small power losses,
\[
       (V^{34}/(Y^{17}R))^{1/20},
        \qquad V^{23/8}/(YR).
\]
Thus (3) gives room to choose all auxiliary Fourier, divisor and trilinear tolerances strictly smaller than the fixed rail gaps. The centered zero term uses FR (32) and \(R\le VY^{-\varepsilon}\) and is not multiplied by a fixed power loss. This verifies the constant-factor extension for (3), not an arbitrary \(a=Y^{1+\eta}\) variant.

This use of a signed unrestricted-modulus convolution estimate differs from the finite positive coefficient families in [Chan's (1+1.75) preprint, Appendices A–C](https://aixiv.science/pdf/aixiv.261111.000001v1.0.pdf). Its stated \(.599\) support is not invoked for our signed source.

## 3. Exact switch and coefficient separation

On the original rows set \(q=p u\), \(m=r v\). Since \(p,r\) lie above the short divisor scores, \(H_h(q)\) opens on \(d\mid u\), \(H_f(m)\) on \(e\mid v\), always with the original log denominators. Neither \(u\ge2\) nor \(v\ge2\) changes any central row in this box: their lengths are polynomial. Open \(e\) **as part of the modulus** \(Q=r e\); both \(r,e\) are units at \(N\), and \(r\) is prime. Then
\[
        n=p b,\quad b=s u,\quad n\equiv N\pmod Q.
\]
The true primes \(p,r\) remain prime in their respective source and modulus. Since \(r<p\) and \(e<\min(p,s,r)\), \((p,Q)=1\) identically, and the original target-unit conditions are imposed by \((p,N)=1\), \((b,N)=1\), \((Q,N)=1\). A modulus \(Q\) has at most one true \(r\) label: \(Q<x^{.517}\), whereas two distinct primes \(>x^{.499}\) have product \(>x^{.998}\). The \(r\)-log weight, after canceling the original \(\log m\), is \(O(L)\).

Replace the sharp central \(n\)-cut by a smooth approximation whose transition relative length is \(L^{-K}\), derivatives costing fixed powers of \(L\). This costs arbitrary log reserve by taking \(K\) large: the absolute weights at each pair \(n,m=N-n\) are bounded by fixed divisor powers and logarithms, so Cauchy on the endpoint interval of length \(O(xL^{-K})\) and global divisor moments cost \(O(xL^{-K/2+O(1)})\). The corresponding deletion in the model costs at most a harmonic \(\sum_Q1/\varphi(Q)\ll L^{O(1)}\) times this estimate for the \(n\)-side divisors.

Take size dyads of \(p,b,s,d,e,r\), a logarithmic number in each axis. Expand the smooth test by compact Fourier separation in the normalized logarithms of \(s,d,e,n\), keeping the literal values of \(W_s(q)\) and of both kernel arguments. The separate \(\log p,\log r\) factors belong to their own axes. Each compact Fourier integral has polylogarithmic \(L^1\) mass by normalized differentiation; truncate at a sufficiently large power of \(L\) with arbitrary log error in both true and modeled sums by the same absolute bounds. The phase on \(n=p b\) separates as \(p^{it}b^{it}\); the \(s,d\) phases enter the \(b\) coefficient by summing over the true \(s\mid b\), \(d\mid b/s\) in their dyads. This coefficient is bounded by a fixed divisor power. The \(e\) phases belong to the unique label for \(Q\), with \(\mu(e)\) and the independent size tests. There is no separate sum of errors over individual divisors or individual primes \(s\).

The coefficient on \(p\) is a true prime interval, with an optional log factor and \(p^{it}\), \(|t|\le L^{O(1)}\), and fixed mask \((p,N)=1\). Its Siegel–Walfisz bound in FR Definition 1 with auxiliary coprimality parameter follows by ordinary prime Siegel–Walfisz and partial summation for moduli at most a sufficiently large log power. Excluding primes dividing \(N\) or the auxiliary integer removes \(O(L+\omega(\text{auxiliary integer}))\) terms; the allowed divisor-factor reserve absorbs the latter. For larger moduli the interval bound \(O(V/Q+1)\) and the \(1/\varphi(Q)\) principal give the necessary log reserve. All these statements hold after restriction to any interval inside the dyad. Log-sized Fourier parameters cost only log powers, covered by choosing the initial reserve larger.

Here \(V\asymp p,\ U\asymp b,\ Y=UV\asymp x\) whenever the central test is nonzero. The actual residue \(a=N=2x\) is \(\ll Y\) with a fixed constant on every such box. The modulus has exponent \(\beta+\log_x E+o(1)\) with \(E\) the \(e\)-dyad and \(0\le\log_x E\le .001+o(1)\). Thus (1) gives both strict main rails in (3), and \((23/8)(17/33)-1<.482<.499\) gives the auxiliary rail. Fourier and dyad losses are covered by arbitrary log reserve in (3). Since the discrepancy sums **absolutely over \(Q\)**, the true signed reflected coefficients are permitted. This replaces the progression by its literal coprime model.

## 4. The model vanishes on the same physical ledger

After undoing the separations, the model contains the original smooth product test \(\Psi(s,p,d,e;y)\), with \(h(\log d/\log(y/s))\) as its only \(d\)-dependent factor. For each \(s,p,r,e\) with its required prime/short-divisor support, its inner term at \(Q=re\) is
\[
 \frac1{\varphi(Q)}
   \sum_{(d,NQ)=1}\mu(d)
   \sum_{\substack{k\ge1\\ (k,NQ)=1}}\Psi(s,p,d,e;s p d k).
\]
The separate tag factors can be left outside or absorbed into \(\Psi\). Only the exact kernel support restricts \(d\); no dyadic restriction from the temporary separation remains. The masks \((p,NQ)=(s,NQ)=1\) hold on the actual retained labels: \(r>s,\ p>r\), \(e\) is shorter than \(s\), and all target masks were imposed. Coprime interval counting in \(k\) and partial summation replace the \(k\)-sum by
\[
 \frac{\varphi(NQ)}{NQ}\frac1{s p d}\int
                      \Psi(s,p,d,e;y)\,dy
\]
with error \(O(\tau(NQ)L^{O(1)})\), since the normalized total variation of the smooth weight has a log bound. The error total is \(x^{.14+\sup\alpha+.001+o(1)}\ll x^{.658}\) after the \(\sum_{r,e}1/\varphi(r e)\ll L^{O(1)}\) harmonic sum.

At each central \(y\), the only \(d\)-dependence under the integral is now the finite harmonic
\[
 \sum_{(d,NQ)=1}\frac{\mu(d)}d\,h\!\left(\frac{\log d}{\log(y/s)}\right)
                                     =O_A(L^{-A})
\]
for every \(A\), uniformly in \(N,Q,s,y\). This is the same uniform coprime Möbius PNT harmonic as in the subcritical zero mode: convolve \(\mu(d)/d\) with the \(NQ\)-supported smooth-prime mask, split at a fixed polynomial power using Rankin, and integrate against the derivative of \(h\), supported at polynomially large \(d\) by exact flatness. This proves (2).

The sector contains genuinely positive raw profiles in dyadic aggregate. Choose true \(s,p\) in interior bands and \(u\) prime near exponent \(1-\log_x s-\alpha\); choose \(r,v\) independently with \(v\) prime near \(1-\beta\). Ordinary PNT in the last prime's product interval on each side gives actual \(q,m\) semiprimes, with disjoint prime bands, both scores 1, and \(n,m\) occupying the physical central relation. That is not a fixed-target lower assumption; (2) compares the signed row at each target via (3).

The result avoids, rather than subtracts, the diagonal of the former squared norm. It concerns \(pr>x\) where (1) genuinely fits. It neither bounds the rest of the signed complement, including the wide \(p<r\) domain with no independently groupable source factor, nor proves the original required \(.010M_N\) cap.
