# Four genuine tags need new dispersion or a much cheaper rank-seven removal

Written research note, 2026-11-24. Consider the fixed-target CQ extension from the [certified three-tag work](CQFlexibleThreeTagRankSeven.md). This is an obstruction to the specific certificate which uses (a) a full-level positive linear lower sieve on a true quotient, (b) only some or all of four literal named tags in the middle slot of [Lichtman's Proposition 5.2](https://arxiv.org/html/2309.08522v1#S5), and (c) the current uniform mean-proportional reverse upper for the genuine \(D_0\) rank-five arm to subtract wrong ranks. It is not a pointwise bound on the actual rank-seven term. It leaves open a different weighted sieve, a genuine switched counting result, and a substantially sharper reverse upper.

## 1. Named-only packing cannot directly force rank seven

Write \(S\) for the sum of the four named tag exponents, \(X=1-S\) for the leftover quotient width, \(E\) for the exponent of the full tested quotient-sieve level, and \(B\ge S+E\) for the full progression-level exponent. Write \(b\le S\) for the exponent of the middle slot containing just a subset of the named tags; no quotient-sieve factor enters that slot. For the first two Prop. 5.2 restrictions, write \(h\) for the source factor exponent and \(q_1,q_3\) for the first and third slot exponents, so \(B=q_1+b+q_3\) in the bounding levels. Then \(h-q_1>\varepsilon\) and \(2h+b+2q_3<1-8\varepsilon\), whence \(2B-b<1-10\varepsilon\). In particular \(B<(1+S)/2\) and \(E<X/2\). This deduction does not care which named tags occupy the middle slot. It uses the full tested level; not a statement about unsupported divisors or a separately switched range.

A nonzero ordinary positive linear lower at cutoff exponent \(z\) needs \(2z<E\), hence \(z<X/4\). Consequently this geometry cannot force total rank at most seven from quotient roughness alone: a quotient with four further prime factors is in the ordinary allowed simplex. To permit total rank eight but forbid nine by geometry alone, one needs \(z\ge X/5\) (strict inequality or a fixed collar for literal size issues). Set \(u=z/X\in[1/5,1/4)\). We give the method every advantage and grant that removing or handling all possible rank-eight rows costs zero; rank eight has no automatic sign in this argument. The rank-seven rows alone obstruct the certificate.

## 2. Exact angular mass does not rescue the present reverse upper

At fixed real tag angles, suppress their common positive harmonic differential. The old genuine \(D_0\) ordinary mass is \(m_0=969075913/7200000000\). The broad count lower supplied by the ordinary linear lower equals
\[
 L_{\rm broad}=m_0\,\frac{2\log(E/z-1)}{E}.
\]
Since \(E<X/2\) and \(z\ge X/5\), its active sieve ratio \(s=E/z\) lies in \((2,5/2)\). On this interval the normalized linear lower has the exact displayed first branch. The function \(\log(s-1)/s\) increases there because the sign of its derivative is that of \(s/(s-1)-\log(s-1)>1-\log(3/2)>0\). Thus
\[
 L_{\rm broad}\le \frac{4m_0}{X}\log\frac{1-2u}{2u}.
\]
The rank-seven ordinary measure per same named harmonic is the genuine reciprocal density for **three** remaining widths \(\ge z\), sorted and summing to \(X\). Their product is at most \((X/3)^3\), and their sorted free two-dimensional volume is \((X-3z)^2/(2!\,3!)\). The strict real free widths also lie above all named tags, as required by the literal original receiver. Accordingly, the **exact** ordinary density \(m_7\) at these fixed tag angles obeys
\[
 m_7\ge \frac{9}{4 X}(1-3u)^2.
\]
This is an ordinary angular lower, **not** a lower on the true reflected rank-seven rows. The certified budget used for subtracting those rows is an upper bound, \(C\,m_7\), where the current available fixed-target reverse upper has \(C=1.672\). Even substituting the exact mean rather than an outward simplex bound cannot by itself make this chosen upper budget smaller than \(L_{\rm broad}\).

Indeed the ratio obeys
\[
 \frac{L_{\rm broad}}{m_7}
 \le \frac{16m_0}{9}\frac{\log((1-2u)/(2u))}{(1-3u)^2}
 \le \frac{100m_0}{9}\log(3/2)<.607 .
\]
For the second inequality set \(f=\log((1-2u)/(2u))\), so \(f'=-1/[u(1-2u)]\). The derivative sign of \(f/(1-3u)^2\) is the sign of \((1-3u)f'+6f\). Use \(f\le(1-4u)/(2u)\) to make that sign nonpositive, by \(3(1-4u)(1-2u)\le1-3u\). The last comparison is \(2-15u+24u^2\le0\): it is negative at \(1/5\) and decreasing through \(1/4\). Finally, the positive atanh expansion at \(1/5\) gives \(\log(3/2)\le2(1/5+1/(3\cdot5^3)+1/(5^6(1-5^{-2})))<.4055\), sufficient for the strict rational .607. Thus the upper budget \(1.672m_7\) is larger than the broad lower pointwise, even if rank-eight removal were free and rank-seven exact ordinary mass were used. Fixed angular bins and the ordinary-limit collars cannot turn this strict continuous gap into a positive count certificate by tuning endpoints. No actual reflected population lower is asserted.

**Meaning.** If the four-tag method keeps its named-only middle slot and this broad-linear-lower/mean-proportional subtraction design, a reverse coefficient below .607 is necessary, and not necessarily sufficient (rank eight still matters and the exact ratio could be smaller). Alternatively, forcing rank seven by adding real positive-power quotient-sieve mass into the middle slot requires \(b>S\) from the first two rails alone. Implementing that with the genuine factorable coefficient, or switching the actual residue/source on a disjoint set, is a separate unresolved input. This obstruction does not change the certified three-tag count or its already disjoint ledger contributions.