# Complementary-divisor exchange removes the whole A2--A2 bill, but reverses a broad A3--A3 bill

Research note, 2026-11-24. This is a second exact representation of the marked signed target, not a claim that the old high term's A2--A2 contribution cancels in isolation. It gives a concrete algebraic obstruction to retaining both parity benefits with one short divisor weight, and pinpoints a genuinely new two-prime modulus if that weight is squared.

## 1. Exact representation and the actual square-root margin

Keep the target \(P\), \(L=\log P\), fixed interior \(I=PJ\), \(m=P-n\), small radical, rough cutoffs \(y=e^{L^\delta}\), \(z=e^{L^{.24}}\) with \(0<\delta<.1\), and the actual translated first-cover indicator \(C(n)\) on \(j=2,\ldots,M+1\). Set
\[
H=L^{3/5},\qquad D=P^{1/2}e^{-H},\qquad
F_D(n)=\sum_{\substack{d\mid n\\d\le D}}\mu(d).
\]
For a genuine prime \(n\in I\), \(F_D(n)=1\), so on all integer rows in \(I\)
\[
w(n)=\log n\,F_D(n)-\log n\,F_D(n)\,1_{n\ {\rm composite}}.
\tag{1}
\]
Multiply by \(R_z(n)\) without changing \(w(n)\). This restriction is kept on the two terms of (1); putting it on the complete identity costs nothing.

The first term with \(R_z(n)\) is a true shifted Type I with \(n=d k\), \(d\le D\), coefficient \(\mu(d)\) on the \(z\)-rough \(d\)'s, and \(\log n=\log d+\log k\). Use the already verified square-root-compatible Type I proof from [the smooth source note](SmallRadicalShiftedHighChambers.md) (that proof depends only on the coefficient bound, not on the original Vaughan identity): take all complementary and marked profile expansions with auxiliary logarithms \(O(L^{.27}+L^{.24}\log L)=o(H)\), with their fixed \(M\)-fold multiplicity and power-log error choices. The actual Liouville endpoint is \(X=P/v\) for the rough-complement opened small \(v\), and \(\log v=o(H)\), while the modulus is at most \(P^{1/2}e^{-H+o(H)}\). It thus lies within \(\sqrt X/(\log X)^B\) for any fixed loss \(B\) in the known full-level weighted Liouville BV. The real endpoints and all reduced-class coprimalities are unchanged. The polynomial loop of \(d\le D\) and all auxiliary \(P^{o(1)}\) slots leave total floor \(P^{1/2+o(1)}\). Therefore for any fixed \(A\), the original actual rough-\(y\) marked target satisfies
\[
\sum_{n\in I} C(n) R_y(m)\lambda(m) w(n)
=
\sum_{n\in I} C(n)R_z(n)R_y(m)\lambda(m)T_D(n)+O_A(PL^{-A}),
\quad T_D(n)=-(\log n)F_D(n)1_{n\ {\rm composite}}.
\tag{2}
\]
This does not silently apply the endpoint bound when \(v\) is polynomial: here \(R_y(m)\) is the **original** small rough cutoff, not the large symmetric \(V\) cutoff of the previous decomposition.

## 2. Genuine exchange on complementary divisors and complete payment of A2--A2 in (2)

For any squarefree **even-rank** composite \(n\), the map \(d\mapsto n/d\) exchanges the two halves of its divisor list, with no fixed point and \(\mu(n/d)=\mu(n)\mu(d)=\mu(d)\). Since the full Möbius sum is zero, each half is exactly zero. In particular
\[
F_D(n)=-\sum_{\substack{d\mid n\\D<d<\sqrt n}}\mu(d)
\tag{3}
\]
on these even-rank rows for large \(P\) (so \(D<\sqrt n\) centrally). This is an exact reparameterization of the *same divisors* of each actual composite, not a pairing between hypothetical prime representations.

For \(A_2\), write \(n=pq\) with distinct true primes \(P^{1/4}<p<q\). As \(D^2\ll_I n\), at most one of the two primes fits below \(D\). Thus
\[
F_D(n)=
\begin{cases}
0,&p\le D,\\
1,&p>D.
\end{cases}
\tag{4}
\]
Consequently for the genuine all-large \(A_2,A_2\) pair with \(m=sr\), the high contribution in (2) vanishes pointwise unless the source short prime \(p\) lies in the actual shell \((D,\sqrt P]\). On that shell its absolute weight is at most \(\log n\); the real translated selector is at most one. To bound this entire remainder apply [the proved one-window Kloosterman estimate](SmallRadicalAdverseSemiprimeWindow.md) with the roles of the two represented semiprimes exchanged. The reflected pair is still central on the reflected fixed interval, both true factors satisfy the \(A_2\) constraints, and bounding absolute weight makes the \(\log n,\log m\) distinction a bounded-factor issue. If a paired bound is wanted, take the sum of both exceptional angular shells; it suffices to treat each separately. Quantitative Mertens gives
\[
\sum_{D<p\le\sqrt P,\ p\ {\rm prime}}\frac1p=O(H/L),
\]
since the log endpoints are \(.5L-H\) and \(.5L\). Thus the actual whole A2--A2 bill in (2) is
\[
O(PS(P)H/L^2+P^{.83})
=o(PV_y(P)/L)
\tag{5}
\]
for \(H=L^{3/5}\) and \(\delta<.1\). This statement covers the entire dispersed sector **in the new accounting**: outside the shell it is a row-wise zero, not an assumption of low multiplicity. It does not bound that sector's weight \(-\log n\) in the previous decomposition. For higher even ranks (3) still holds, but the absolute narrow-divisor-shell bound (5) does not automatically extend; those balanced divisors can be composite.

## 3. The same divisor exchange identifies a broad new odd/odd adverse term

For a true rank-three squarefree \(n=p q r\) with \(p<q<r\), write \(F_*(n)=\sum_{d\mid n,d<\sqrt n}\mu(d)\). If the largest prime \(r>\sqrt n\), exactly the four divisors \(1,p,q,pq\) are in the first half, so \(F_*(n)=0\). If \(r<\sqrt n\), exactly \(1,p,q,r\) are in the first half, so \(F_*(n)=-2\). When no divisor is in the truncation shell \((D,\sqrt n)\), \(F_D=F_*\). In particular, real all-large balanced rank-three products with each true prime \(\le P^{1/2-\varepsilon}\) for fixed \(\varepsilon>0\), and every pair product \(>P^{1/2+\varepsilon'}\) for fixed \(\varepsilon'>0\), satisfy \(F_D(n)=-2\) identically. Such angular ranges include the full fixed-size neighbourhood of the three exponents \(1/3\) with suitable constants.

Hence genuine \(A_3,A_3\) rows in that range, if present, have \(T_D(n)\lambda(m)=-2\log n\), whereas [the rough-divisor representation](SmallRadicalSmoothDivisorAlternative.md) counted their sign as favorable. Both directions of the reflection have this same adverse sign; switching \(n,m\) cannot cancel it. The formulas do not say how many such actual additive rows exist. They do show why (5) alone cannot close the total target.

## 4. Exact obstruction for one short linear divisor weight, and the nontrivial modulus for squaring

Consider any alternative arithmetic Type I first coefficient
\[
F(n)=\sum_{\substack{d\mid n\\d\le D}} a(d),\qquad a(1)=1.
\]
For a true semiprime \(p q\) with \(p\le D<q\), this value is exactly \(1+a(p)\). Requiring a row-wise zero whenever such a factorization occurs forces \(a(p)=-1\) for each short prime in those rows. If an all-large rank-three product has all its primes among such forced short primes, and all three pair products exceed \(D\), its short divisor list is exactly \(1,p,q,r\), giving \(F(pqr)=-2\). Since on odd \(m\) a nonadverse high \( -\log n F(n)\lambda(m)\) would require \(F\ge0\), one cannot have both pointwise requirements on those overlapping angular supports with a single linear short divisor coefficient. This is a conditional statement on the actual factor supports concerned, not a fabricated simultaneous prime representation.

For example a convex interpolation of \(F_D\) and the rough first coefficient \(R_V\) also has this visible trade-off: on the common high-rough core, \(F=(1-c)R_V+cF_D\) takes \(1-c\) on dispersed A2 and \(1-3c\) on this A3. Making A2--A2 nonadverse needs \(c\ge1\), while keeping the A3--A3 contribution nonadverse needs \(c\le1/3\). Even allowing arbitrary real \(c\) does not satisfy both. This calculation is pointwise in actual rows; it does not compare separate angular mass constants.

A natural nonlinear fix would be \(F_D(n)^2\): it remains 1 on primes, 0 on dispersed even A2, and 4 rather than -2 in A3, so the A3--A3 sign becomes favorable again. The obstruction is concrete at the required Type I step:
\[
F_D(n)^2=\sum_{\substack{d,e\le D\\d\mid n,\ e\mid n}}\mu(d)\mu(e)
=\sum_{\ell\mid n}\sum_{\substack{d,e\le D\\[d,e]=\ell}}\mu(d)\mu(e).
\]
For two distinct true primes \(p,q<D\) with \(pq>D\), the coefficient at \(\ell=pq\) equals \(2\), from the two ordered pairs only. There is no cancellation of this long modulus in the square. Switching it to \(n/(pq)\) makes the latter short on the rank-three angular support, but leaves the requirement that its *long* quotient split into the two actual short primes \(p,q\). This is not a smooth multiplier or an arbitrary bounded coefficient on the short variable as in the established Type I. Holding one of \(p,q\) fixed and combining it with the third true prime still gives a modulus \(>P^{1/2}\) throughout the central balanced rank-three region. Thus a real two-prime (or further mixed parity) estimate is needed to justify this repair. The divisor identity and ordinary BV alone do not yield it.
