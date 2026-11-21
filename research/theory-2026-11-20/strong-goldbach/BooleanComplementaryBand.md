# A Boolean complementary band on the genuine high-reflected correction

This note extends [HighReflectedCompensationByComplement](HighReflectedCompensationByComplement.md) on the same two physical high-reflected ranks. An alternating divisor marker removes a concrete uncompensated positive-part packet whose weighted dyadic mean exceeds `0.063 M_N` in the old representation. The new representation does not bound the signed remainder or imply Goldbach.

## 1. Exact replacement

Retain that note's actual variables, unit support, exact roughness, squarefreeness, and weights. In particular \(N=2x\), \(L=\log x\), \(T=\log L\), \(\delta=T^{-1/2}\), \(X_0=x^{1-\delta}\), \(B_q=x^{.501}\), \(B_m=x^{.5+T^{-20}}\), and \(n=s q\in(x/2,x]\), \(m=N-n=r v\) with a true prime \(r>B_m\). The reflected cofactor \(v\) is either prime or the product of two distinct primes, and \(G(m)=-S_2(m)\ge0\) is as in that note. Keep the exact quotient score \(C(q;s)=\sum_{d\mid q,d<n/X_0}\mu(d)\), the giant indicator \(U\) and the original genuine-singleton count \(V\).

Let \(\mathcal A\) consist of the actual primes with \(x^{.51\delta}<p\le x^{.95\delta}\). Eventually it lies strictly inside the original lower marker band \((z_q,x^{\delta-2/T}]\). Let \(V_{1,\mathcal A}\) denote the contribution to \(V\) of those prime markers. Replace it by
\[
 V_{\mathcal A}(q)=\sum_{\substack{w>1,\ w\mid q,\ q/w>B_q\\p\mid w\Rightarrow p\in\mathcal A}}-\mu(w),
 \qquad
 V_{\rm new}=V-V_{1,\mathcal A}+V_{\mathcal A}.                  \tag{1}
\]
Then on the same true source the signed score sum with \(C(U-V_{\rm new})\) equals the original one with \(C(U-V)\), to error \(O_A(xL^{-A})\) for any fixed \(A\). No earlier reserve is being added.

To see the new centered null, open the **actual** divisor \(w\) with coefficient \(-\mu(w)\), the original \(C\)-divisor \(d\), and the original roughness Bonferroni label \(e\) of degree \(\lfloor T^2\rfloor\), so \(e\le x^{1/T}\). The modulus on the true \(r v\) source is \(s\operatorname{lcm}(w,d,e)\), with the exact moving prefix \(m<N-s w B_q\). Here \(s w\le x^{.499}\) and the lcm modulus with \(s\) is \(<x^{.4995}\) eventually. The divisor multiplicity at a modulus is bounded by a fixed divisor power, because \(w\) is just one label. Use both moving-prefix BV arguments of the high-reflected note: generalized product BV when \(v\ge x^{.0005}\), and after fixing \(v\) ordinary maximal prime BV at the actual scale \(x/v\) otherwise. In the latter branch the coprime mask really demands \((v,s\operatorname{lcm}(w,d,e))=1\); the residue for \(r\) is then \(N\bar v\). Rough-guard restoration pays the fixed divisor weights by the same factorial / Cauchy--Shiu estimate.

Fix \(s,w,e\) and the physical \(m\) (or its continuous variable in the fixed-short-cofactor principal). Write \(d=a k\) with \(a\mid w e\), \((k,w e)=1\). The primes of \(w\) and \(e\) are disjoint. If \(a\) contains two primes from \(\mathcal A\), then \(a>x^{1.02\delta}\), and the \(C\)-divisor range is empty. Otherwise \(a\le x^{.95\delta+T^{-1}}\). The actual upper bound \(k<n/(X_0 a)\) is thus at least \(\frac12 x^{.05\delta-T^{-1}}\). The prime \(s\) is larger than all primes in \(d,w,e\) and the modulus is exactly \(s w e k\), with \((k,swe)=1\). The principal is the masked finite \(\mu(k)/\phi(k)\) harmonic of the earlier proof, with threshold much larger than \(\exp(2T^4)\); it is arbitrary-log small uniformly in all retained labels. Harmonic sum over the remaining labels costs only log powers. This proves the new \(C G V_{\mathcal A}\) null. The old \(C G V_{1,\mathcal A}\) null is already proved, so (1) gives the asserted equal sum. Prime \(q\) cannot enter either marked sum, since its only nonunit divisor has quotient 1.

## 2. Sign outside an actually negligible exceptional family

Write \(q_{\mathcal A}=\prod_{p\mid q,\ p\in\mathcal A}p\). If \(q_{\mathcal A}<q/B_q\), then every nonunit divisor of this product is eligible, so
\[
 V_{\mathcal A}=1_{q_{\mathcal A}>1},\qquad
 V_{1,\mathcal A}=\omega(q_{\mathcal A}).
\]
This holds even on non-giant \(q\). On every giant \(q\) it automatically holds: its giant is not in \(\mathcal A\), and \(q_{\mathcal A}\) divides the giant's cofactor, which is strictly below \(q/B_q\). Thus outside the literal exceptional family \(q_{\mathcal A}\ge q/B_q\), \(0\le V_{\rm new}\le V\). If \(C<0\), the positive part of \(C(U-V_{\rm new})\) is no greater than before. For \(C\ge0\) and \(U=0\), there is no positive part. For \(U=1\), all actual prime factors of its nonunit cofactor satisfy the complementary quotient test. Therefore \(V_{\rm new}=0\) can only occur when every such factor lies in the old omitted gap \((x^{\delta-2/T},x^\delta]\). This is exactly the old \(O(T^{-1/2}M_N)\) positive exception. In particular the all-macro signs are unchanged.

In the remaining non-giant exceptional family, the actual \(q/B_q\) exceeds \(\tfrac12 x^{.359}\). Therefore at least \(K=\lfloor .30/\delta\rfloor\) distinct primes from \(\mathcal A\) divide \(q\). Open one subset of \(K\) such primes for a positive upper, writing its product \(f\le x^{.285}\) and \(q=f y\). At fixed genuine \(s,f,v\), the two primitive affine forms for \(y,r\) are obtained from \(s f y+v r=N\) exactly as in Section 3 of the high-reflected note: \((s f,v)=1\) is forced by the actual unit support, their determinant is \(N\), and their interval has length \(Y\asymp x/(s f v)\gg x^{.075}\), since \(v\le1.5x^{.5-T^{-20}}\). The constants and slopes have fixed polynomial heights. Apply corrected Henriot with \(2^{O(\omega(y))}\rho_q(y)\) and a fixed small polynomial rough upper for the actual large prime \(r\). Since every prime factor of \(s f v\) is large and \(v\) has at most two, the same local extra slope ratio \(\prod_{p\mid s f v}(p-1)/(p-2)\) is \(1+o(1)\); the factor at 2 and the unit conditions at \(p\mid N\) are unchanged. This bounds the total weighted population by
\[
 \ll M_N T^{O(1)}\sum_{\substack{f\ {\rm squarefree}\\
                 p\mid f\Rightarrow p\in\mathcal A,\ \omega(f)=K}}
                       \frac{2^{O(K)}}{f}
 \ll M_N T^{O(1)}\frac{C_0^K}{K!}=o(M_N).
\]
Here the fixed power of divisor weights dominates \(|C|(|U|+|V|+|V_{\rm new}|)\); the extra \(\omega(f)\) bits cost \(2^{O(K)}\). The \(v\)-harmonics are bounded by the physical \(G(m)\ll\log v/L\) or \(G(m)\ll(\log v_1)(\log v_2)/L^2\), and the prime \(s\)-harmonic is bounded. The last inequality uses the actual Mertens harmonic \(\sum_{p\in\mathcal A}1/p=\log(95/51)+o(1)\), so \(K\asymp\sqrt T\) beats every fixed power of \(T\).

## 3. A large, actual old positive-only packet disappears

Take \(q=p a b\), with distinct \(a,b\in\mathcal A\), \(p>B_q\) an actual prime. Each singleton \(a,b\) is strictly below \(n/X_0\) while \(a b\) is not. Thus \(C=-1,U=1,V=2\) and \(V_{\rm new}=1\). The old positive score on every such row was exactly +1, which vanishes in the new representation. Take the genuine reflected semiprime \(m=r v\) with \(.17<\log_x v<.45\), and genuine \(s\) with \(.105<\log_x s<.135\). The terminal \(p\) is of exponent at least \(.865-o(1)\), and \(r\) of exponent between \(.55+o(1)\) and \(.83+o(1)\); all factors on opposite legs have distinct scales, so the exact unit condition holds.

Over even \(N\in[2Y,4Y]\), count actual integer tuples by freezing exponent endpoints at \(Y\) with arbitrarily small inward and outward relative log intervals. Terminals \(p,r\) vary over independent fixed proportional boxes in \(n,m\), after fixing \(s,a,b,v\); these intervals have polynomial lengths uniformly. Ordinary prime PNT and partial summation give their density \((\log p\,\log r)^{-1}\) in the two axes; refining the boxes covers \(Y\le(n+m)/2\le2Y\), \((n+m)/4<n\le(n+m)/2\) of area \(3Y^2/2\), with boundary errors tending to zero. For the shrinking \(\mathcal A\) exponent bands, \(\log x/\log Y\to1\) and \(\delta(x)/\delta(Y)\to1\) uniformly on this dyad, and the two prime harmonics tend to \(\tfrac12\log^2(95/51)\) (the equal pair costs \(o(1)\)). All old weights and the exact high-giant and rough conditions hold in these boxes. The factor \(W_s(q)\) divided by the leading \(\log p/L=1-\log_x s+o(1)\) yields \((1-2\log_x s)^2+o(1)\), while \(G\) divided by \(\log r/L=1-\log_x v+o(1)\) gives \(8\log_x v+o(1)\). Thus the total old packet normalized by \(\sum_{N\in[2Y,4Y],\ N\ {\rm even}}M_N\) tends to
\[
 \left(\int_{.105}^{.135}\frac{(1-2t)^2}{t}\,dt\right)
    \frac{\log^2(95/51)}2\,8(.45-.17)=.0631499376\ldots .
\]
The mean binary singular series over even \(N\) is 2, so this normalizer is asymptotic to \((3Y^2/2)/\log Y\), as in DoubleHighPositiveMassBarrier. It follows that there is at least one genuine even target in every sufficiently large dyad whose old positive-only bound from these rows alone exceeds \(.063 M_N\). This is a positive-part obstruction on the old representation at some targets, not a lower bound on its signed high-reflected term. The new exact representation neutralizes the entire indicated packet and does not add significant positive-part regions, but still has other genuine \(C<0,V_{\rm new}>U\) rows.
