# Far-angle Poisson descent with the actual prime weights

On the signed notch of [MacroShiftBurgessMajorArcs.md](MacroShiftBurgessMajorArcs.md), the **expanded physical covariance** admits a direct progression Poisson decomposition. Its genuine zero-frequency part and two large-gcd tails are unconditionally \(\ll_B xY(\log x)^{-B}\) for every \(B\). This retains both actual prime-log factors of exponent .09. The reciprocal-frequency sum is not estimated here. In particular the result does not control the full signed notch or prove binary Goldbach. The major-arc result in the previous note and the zero-frequency result here concern different decompositions.

## 1. Exact arithmetic and weights

Let \(x=N/2,\ L=\log x\). Work in one pair of dyadic boxes from (66) of the cited note, with short-label primes \(A,B\asymp Y=x^{.015+O(.0001)+o(1)}\), actual distinct prime slots \(p_1\asymp P_1,p_2\asymp P_2=x^{.09+O(.001)+o(1)}\), and \(d\asymp D,r\asymp R,h\asymp H,h'\asymp H'\) in their stated bands. Thus \(D,R=x^{.49+O(.001)+o(1)}\), \(H,H'=x^{.42+O(.002)+o(1)}\), and \(DP_1H,RP_2H'\asymp x\). The covariance after Cauchy is weighted by
\[
 \kappa_A\overline{\kappa_B}(\log p_1)(\log p_2)\mu(d)\mu(r)
 \psi_1(h/H)\psi_2(h'/H')\Psi_1(dp_1h/x)\Psi_2(rp_2h'/x).
\]
The unit restriction and fixed support \(m_1=dp_1h,m_2=rp_2h'\asymp x\) bounded away from \(N\) are exactly those of the previous note. Additional dyadic endpoint cuts on the named factors may be retained. We may impose any fixed bounded pair weight on \(A\ne B\), including the far-angle restriction \(|A-B|\asymp Y\). Take smooth compactly supported \(\psi_i,\Psi_i\) with bounded magnitudes and derivatives costing fixed powers of \(L\). The original sharp \(\psi_i\) may be recovered to arbitrary log-power precision: if one \(h\) interval is modified on boundary bands of total width \(O(HL^{-B_1})\), the resulting product coefficient is supported on at most \(O(DP_1(HL^{-B_1}+1))\) integers and is bounded by \(L\tau_3(m)\). Its squared mass is \(\ll xL^{-B_1/2+O(1)}\), by Cauchy with the global fourth divisor moment. For any such sequence \(c\),
\[
 \sum_{u>0}\left(\sum_{A\sim Y,\ A\ {\rm prime}}|c(N-Au)|\right)^2
 \ll Y\sum_m|c(m)|^2.
 \tag{1}
\]
Indeed Cauchy over \(A\), then interchange \((A,u)\) with \(m\): a positive \(N-m\ll x\) has only \(O(1)\) distinct prime factors \(\asymp Y\). Cauchy using (1) on the edge side and the full side costs \(\ll xY L^{-B_1/4+O(1)}\). This remains an upper bound after imposing arbitrary bounded additional pair masks; take absolute values then drop the mask. No smoothing of \(\mu\) or the prime slots is involved. The reference subtraction from §1 of the previous note is separately negligible at the original linear-sum scale, before Cauchy; it is not being replaced by a zero Poisson mode in this note.

The physical relations are
\[
 m_1=N-Au,\qquad m_2=N-Bu,\qquad u>0.
\]
Thus \(b d h-a r h'=Nj\), with \(b=Bp_1,a=Ap_2,j=B-A\). Conversely, that determinant equation gives \(A\mid N-m_1,\ B\mid N-m_2\) since \(A,B\) are distinct primes; the two quotients coincide and are positive on the support. For unit pairs \((m_1,m_2)\mid j\): any common factor is coprime to \(u\), since otherwise it would divide \(N\), and \(m_1-m_2=j u\). Hence \(p_1\ne p_2\), neither prime cross-divides the opposite \(m_i\), and \(A\nmid m_1,\ B\nmid m_2\) because \(A,B\) are units mod \(N\). Therefore
\[
 g=(bd,ar)=(d,r),\quad g\mid j,\quad (g,abN)=1.
 \tag{2}
\]
No coprimality is forced between \(A\) and \(r\) or between \(B\) and \(d\); repeated primes in \(ar\) or \(bd\) on these sides cause no problem. We may and do impose (2), \((d r p_1p_2,N)=1\) and \(p_1\ne p_2\) before summing \(h,h'\), since these conditions hold at every original unit solution.

## 2. Absolute tails for the real covariance

A useful elementary divisor bound is
\[
 \sum_{\substack{n\asymp X\\n\equiv c\bmod A}}\tau_3(n)^2
       \ll (X/A)(\log(2X))^8
       \quad((c,A)=1,\ A\le X^{1/9},\ A\ {\rm prime}).
 \tag{3}
\]
To see \(\tau_3^2\le\tau_9\), at each prime combine the two three-part exponent compositions into a nonnegative \(3\times3\) integer array with those row and column totals (e.g. fill greedily). Different pairs have different totals and hence different selected arrays. In a nine-fold factorization choose a largest factor; the other product \(s\) is \(O(X^{8/9})\). It is a unit modulo \(A\), and the last factor has \(\ll X/(sA)+1\) choices. Counting the remaining \(\tau_8(s)\) possibilities and summing proves (3), including the endpoint term by the stated modulus bound. The analogous global divisor-moment bounds used in (1) follow from \(\tau_3^4\le\tau_{81}\) by the same exponent-array construction. We also use \(\tau_3(m)\ll_\eta m^\eta\) for all fixed \(\eta>0\).

For any \(B_0>0\), choose \(K=K(B_0)\) large. The absolute contribution from \(g>L^K\) is \(\ll_{B_0}xYL^{-B_0}\), uniformly in the even target and the boxes. To prove this, for each \(g\mid j\) count \(g\mid m_1,m_2\), which forces \(u\equiv N\bar A\bmod g\) and hence also gives the \(B\) congruence. Set \(u=u_0+g t\), so \(m_i/g=(N-A_i u_0)/g-A_i t\) with \(A_1=A,A_2=B\). This runs in a reduced residue class modulo \(A_i\): its residue is \(N/g\) in the field \(\mathbb Z/A_i\mathbb Z\), since \((g,A_i)=1\). Use \(\tau_3(g\,n)\le\tau_3(g)\tau_3(n)\), and apply Cauchy in \(t\) and (3) at \(X\asymp x/g\). This is allowed since \(g\ll Y\), so \(A_i\ll(x/g)^{1/9}\). The absolute product of the two factorization coefficient sums costs \(\ll (x/(gY))\tau_3(g)^2L^{O(1)}\). There are \(O(Y(Y/g+1))\) ordered integer pairs \(A,B\) with \(g\mid B-A\), before requiring primality. Consequently the tail is
\[
 \ll xL^{O(1)}\sum_{L^K<g\ll Y}\tau_3(g)^2(Y/g^2+1/g)
 \ll xY L^{O(1)-K}+xL^{O(1)}.
 \tag{4}
\]
All of these are inequalities for weighted sums, not pointwise approximations to the coefficients.

In the remaining equations divide \(d=g d_1,r=g r_1\), retaining \((r_1,bgN)=1,\ (d_1,ar_1gN)=1\). Squarefreeness of \(g\) and \((d_1 r_1,g)=1\) give
\(\mu(d)\mu(r)=\mu(g)^2\mu(d_1)\mu(r_1)\); all exceptions have zero weight. Put \(C=Nj/g\), a nonzero integer. Since both row coefficients are units modulo \(N\), the remaining unit condition on \(h,h'\) is equivalent to \((h,N)=1\); expand its indicator as \(\sum_{f\mid(h,N)}\mu(f)\). In each included equation \(f\mid h'\) too, so substitute \(h=f t,h'=f t'\) and divide \(C\) by \(f\).

For any fixed \(0<\beta<1\), in this expanded identity the absolute contribution from \(f>\exp(L^\beta)\) is \(\ll_{B_0}xYL^{-B_0}\). For \(f\le x^{1/2}\), divisibility of \(m_1,m_2,N\) by \(f\) and units \(A_i\) implies \(u=f t\); then \(m_i/f=N/f-A_i t\) is a reduced class modulo \(A_i\). The same use of (3), now at \(X\asymp x/f\), gives the pair bound \(\ll (x/(fY))\tau_3(f)^2L^{O(1)}\). There is no extra sum over \(g\) in this bound: for each \(u,A,B,f\), sum the absolute product of the two factorization multiplicities over all factorizations satisfying any retained restrictions, counting each pair of factorizations once. Sum over \(O(Y^2)\) pairs and use
\[
 \sum_{\substack{f\mid N\\ f>\exp(L^\beta)}}\frac{\mu(f)^2\tau_3(f)^2}{f}
 \le e^{-\eta L^\beta}\prod_{p\mid N}(1+9p^{-1+\eta})
 \le \exp(-\eta L^\beta+O_\eta(L^\eta))
\]
for fixed \(0<\eta<\beta\). For the last bound use all integers \(\le L\) and at most \(O(L)\) prime divisors beyond \(L\). If \(f>x^{1/2}\), for each \(A,B,f\) there are at most \(O(x/(Y f))\) positive \(u\ll x/Y\) divisible by \(f\), with no additive 1. Apply the pointwise divisor bound and \(\tau(N)=x^{o(1)}\) to give \(\ll xYx^{-1/2+o(1)}\). This justifies \(f\) truncation on the physical equality. It is not a statement that the omitted expansions lack oscillatory norms in some other decomposition.

## 3. Dependent windows and the true Poisson zero mode

For fixed outer labels and \(g,f,d_1,r_1\), put \(q=a r_1\). The exact equation for \(t=h/f\) is
\[
     t\equiv (C/f)\overline{b d_1}\pmod q.
\]
Writing \(u_1=h/H\) (different from the common quotient \(u\)), the corresponding \(h'/H'\) is \(v_1=\lambda u_1-\gamma\), where
\[
 \lambda=\frac{b d_1H}{a r_1H'},\qquad \gamma=\frac{C}{a r_1H'}.
\]
These are the **actual dependent windows**, \(\lambda\asymp1,|\gamma|\ll1\). In particular neither window in \(t\) is presumed independent of \(d_1,r_1\). Define the compactly supported smooth weight
\[
 W(u_1;d_1,r_1)=\psi_1(u_1)\psi_2(v_1)
           \Psi_1(g d_1 p_1 H u_1/x)
           \Psi_2(g r_1 p_2 H' v_1/x).
\]
It is independent of \(f\), with log-power derivative bounds in the normalized variables \(u_1,d_1/(D/g),r_1/(R/g)\). The original restrictions on the product and \(h'\) appear *inside* \(W\), not as separate fixed intervals. With \(e(z)=\exp(2\pi i z)\) and \(\widehat W(\xi)=\int W(v)e(-\xi v)\,dv\), progression Poisson gives the exact identity
\[
 \frac{H}{f q}\sum_{\ell\in\mathbb Z}
          \widehat W\!\left(\frac{\ell H}{f q};d_1,r_1\right)
          e\!\left(\frac{\ell(C/f)\overline{b d_1}}q\right).
 \tag{5}
\]
At \(\ell=0\), \(f\) contributes exactly \(\sum_{f\mid N}\mu(f)/f=\varphi(N)/N\) if kept untruncated. If \(f\) is truncated, this factor has an error smaller than every log power by the harmonic Rankin bound above and in any case stays \(\ll \log\log(3x)\) in absolute value. Keeping all \(f\) for the zero-mode identity alone also has no effect on its separate bound.

For each \(r_1\), use ordinary maximal Mertens cancellation on \(\mu(d_1)1_{(d_1,E)=1}\) for \(E=a r_1 g N\). It is uniform here:
\[
 \sup_{J\subset[D/g,2D/g]}\left|\sum_{d_1\in J,\ (d_1,E)=1}\mu(d_1)\right|
       \ll_{B_0} (D/g)L^{-B_0}.
 \tag{6}
\]
Indeed \(\mu 1_{(\bullet,E)=1}=\mu*1_{\{s:\ p\mid s\Rightarrow p\mid E\}}\). Split the convolution variable \(s\) at \((D/g)^{1/2}\). For small \(s\), ordinary PNT/Mertens on each rescaled interval gives any log-power reserve, times \(\sum_s1/s=E/\varphi(E)\ll\log\log(3x)\) on this support. For large \(s\le2D/g\) the trivial count is \(O((D/g)/s)\), and the harmonic tail is \(\ll (D/g)^{-1/4}\prod_{p\mid E}(1-p^{-1/2})^{-1}\), which is power-small; that product is \(\exp(O(\sqrt L))\) since \(E\le x^{O(1)}\).

Apply (6) and partial summation with \(\widehat W(0;d_1,r_1)\), whose variation in the normalized \(d_1\) interval costs only a log power. Sum \(1/r_1\ll1\) over \(r_1\asymp R/g\), keeping actual prime weights in both outer slots. For each \(A,B,p_1,p_2,g\) the zero-mode total is \(\ll_{B_0} (H/a)(D/g)L^{-B_0}\) with arbitrary reserves. Now \(a\asymp YP_2\), \(DP_1H\asymp x\); summing over the \(O(Y^2P_1P_2)\) outer labels and the harmonic \(g\) sum proves
\[
       |\mathcal Q_{\rm Poisson,0}|\ll_{B_0}xY L^{-B_0}
 \tag{7}
\]
uniformly, including for arbitrary bounded far-angle masks. The proof used the sign of the actual \(\mu(d)\) and did not assert independent arithmetic behavior of the second \(d\)-variable.

## 4. What the reciprocal term still requires

For \(g\le L^K,\ f\le\exp(L^\beta)\), the natural frequency scale is
\[
       K_f=\frac{ f a R}{g H}=x^{.175+O(.0041)+o(1)}.
\]
Nonzero frequencies \(|\ell|\) above \(K_f x^\delta\) for any fixed \(\delta>0\) cost an arbitrarily large power saving by rapid decay of \(\widehat W\) in (5). This follows per outer box by summing \((1+|\ell|/K_f)^{-J}\) with \(J\) fixed sufficiently large, and covers sums over the polynomially many labels and the subpower \(f\) range. On a signed dyadic \(\ell\)-range, the smooth dependence of \(\widehat W(\ell H/(f q);d_1,r_1)\) on all three normalized variables \(d_1,r_1,\ell\) may be Mellin separated with log-power \(L^1\) cost. Indeed every fixed power of \(\xi\partial_\xi\) on \(\widehat W\) is the Fourier transform of a linear combination of derivatives of \(u_1^jW\), by integration by parts, and remaining parameter derivatives act on smooth \(W\) or apply more \(\xi\partial_\xi\). Thus the derivative bounds are uniform even when \(|\ell|/K_f\) is polynomially large. The rational inverse phase in (5) is retained; it is not part of this Mellin separation.

As one sufficient but unproved bound, fixing \(A,B,p_1,p_2,g,f\) and on each frequency box, the three-variable reciprocal sum *before* the prefactor \(H/(f q)\) should be \(\ll_{B_0} (DR/g^2)L^{-B_0}\) with arbitrary reserves. This would suffice by the same outer normalization, with an additional \(1/f\) harmonic weight. It asks for essentially the entire length-\(K_f\) saving compared with a trivial per-frequency sum. An aggregate in the actual outer prime labels rather than this uniform bound would also suffice if normalized to \(xY\) after the prefactor. Neither estimate is proved.

The April 2026 [partially fixed-modulus trilinear-fraction result, Theorem 2.1](https://arxiv.org/html/2604.25177v1) and the August 2026 [subdyadic trilinear-fraction result, Theorem 2.1](https://arxiv.org/html/2608.27732v1) do not directly give this bound. For example, the August result permits consecutive arithmetic progressions for both \(m=b d_1,n=a r_1\), so its sparsity hypothesis can be met *without* introducing a power-loss partition. At the center of the bands and with \(g=f=1\), the magnitudes \(M_1,M_2\) are both \(x^{.595+o(1)}\), each progression supplies \(x^{.49+o(1)}\) entries and the frequency supplies \(x^{.175+o(1)}\). The phase scale factor in its theorem is bounded on the entire natural frequency range \(|\ell|\ll K_f\), since \(|C/f|K_f/[(bD/g)(aR/g)]=|Nj|/(b D H)\ll1\), uniformly using \(|j|\ll Y\) and \(DP_1H\asymp x\). The product of the three norms has elementary upper bound \(x^{.5775+o(1)}\). The two bracket powers in their estimate are
\[
 .175/2+.595(1/2+3/8)=.608125,\qquad
 .175(7/20)+.595(3/5+7/20)-(2/5)(.105)=.5845.
\]
Even the smaller combined exponent \(1.162\) is above the required \(.98\); the larger is \(1.185625\). The paper before subdyadic refinement, with \(M_1=x^{.595}\) if absorbing \(b\) into \(m\), likewise does not meet the threshold by its stated bound. These observations address a direct application with fixed outer primes, not a theorem excluding all exploitation of their average.

Equations (4) and (7) remove actual gcd tails and the continuous main term, leaving signed nonzero inverse frequencies collectively unresolved. No estimate is asserted for the far-angle norm or for the full Goldbach residual.
