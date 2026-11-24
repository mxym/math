# An exact smooth-divisor alternative to the shifted high-source sign decomposition

Research note, 2026-11-24. This changes the representation of the **same** marked signed budget; it does not claim that the previously defined \(B_3\) terms cancel by themselves. A symmetric further restriction on the complement provides exact pointwise pairing but is a smaller target. The remaining broad even/even core is explicit.

## 1. Setup and exact identity (no Vaughan coefficients needed)

Let \(P\) be large even, \(L=\log P\), \(\operatorname{rad}(P)\le L^B\), \(n\in I=PJ\) fixed interior, and \(m=P-n\). Let \(y=e^{L^\delta}\), \(0<\delta<.1\), \(z=e^{L^{.24}}\), and \(C(n)\in\{0,1\}\) be the actual translated first-cover selector across fixed offsets \(j=2,\dots,M+1\), with the exact normalized tag partition. Define \(w(n)=1_{n\text{ prime}}\log n\) and \(R_D(n)=1_{P^-(n)>D}\). Given any fixed desired log saving, choose fixed \(c>0\) sufficiently small and put
\[
V=\exp(cL/\log L),\qquad z<V<\inf I
\]
for large \(P\). Use the exact pointwise identity
\[
R_V(n)=\sum_{\substack{d\mid n\\P^+(d)\le V}}\mu(d),\qquad
w(n)= (\log n)R_V(n)-(\log n)R_V(n)1_{n\ {\rm composite}}.
\tag{1}
\]
The divisor formula follows by multiplying \(1-1\) at each small prime of \(n\), irrespective of its multiplicity; the second formula holds on every integer \(n\in I\), since every genuine prime there exceeds \(V\). Both formulas can be multiplied by \(R_z(n)\) without change. Keeping this mask during Type I ensures \(n,m\) are target units. The resulting true high coefficient is now
\[
T_V(n)=-(\log n)R_V(n)1_{n\ {\rm composite}}\le0.
\tag{2}
\]
It is exact also on nonsquarefree rows; an optional later change from \(\lambda\) to \(\mu\) on rough \(m\) costs the known super-log squareful tail.

## 2. Exact shifted Type I pays the first term in the original rough-\(y\) budget

Fix any desired \(A>0\). Take \(D_s=P^{.4}\) for the source divisor \(d\). To justify truncating (1) in actual integer sums, let \(h=1/\log V\). Since \(\ell^h\le e\) for \(\ell\le V\), Rankin and Mertens give
\[
\sum_{\substack{d>D_s\\P^+(d)\le V}}\frac{|\mu(d)|}{d}
\le D_s^{-h}\prod_{\ell\le V}(1+\ell^{h-1})
\ll L^{-.4/c+3}.
\tag{3}
\]
For fixed \(d\) the count of \(n\le P\) divisible by \(d\) is \(\lfloor P/d\rfloor\le P/d\), with no extra \(+1\) summed beyond the endpoint. With base signs and any fixed-size log weights, (3) costs \(O_A(PL^{-A})\) by taking \(c\) sufficiently small after all fixed log losses. The actual sum of normalized mark weights per \(n\) is at most one, so the bound needs no absolute tag amplification; even an extra fixed log power could be paid by further decreasing \(c\).

For the retained \(d\le P^{.4}\), write \(n=d k\), keeping \(R_z(n)\). Thus \(d\) is \(z\)-rough and its coefficient \(\mu(d)1_{P^+(d)\le V}\) is a permitted bounded Type I coefficient. The smooth weight is \(\log n=\log d+\log k\); the first part enlarges the coefficient by at most \(L\) and the second is exactly the allowed smooth Type I multiplier. The actual shifted Type I with joint-profile \(C(n)\) from [the multi-offset Type I proof](SmallRadicalTranslatedTagTypeI.md) therefore yields
\[
\sum_{n\in I} C(n)R_y(m)\lambda(m)(\log n)R_V(n)=O_A(PL^{-A}).
\tag{4}
\]
This estimates the true first term of (1), not an independent guess at its sign. Combining (1) and (4) gives
\[
\sum_{n\in I} C(n)R_y(m)\lambda(m)w(n)
 =\sum_{n\in I} C(n)R_y(m)\lambda(m)T_V(n)+O_A(PL^{-A}).
\tag{5}
\]
In this equivalent computation, **all** genuine odd-rank \(m\) (or just \(\lambda(m)=-1\)) are pointwise nonnegative, including the former wide \(B_3\)-source adverse odd complement. This is a change of representation: remaining genuine even-\(\lambda(m)\) rows with \(R_V(n)=1,\ n\) composite are negative, some of them newly moved into the bill. It does not prove that the older \(B_3\) contribution alone was negligible.

A useful consequence of two admissible cutoffs \(z\le V_1<V_2\) is an exact true signed cancellation for the source least-prime annulus \(V_1<P^-(n)\le V_2\). Such an \(n\in I\) cannot be prime. Subtract (4) for the two cutoffs (using the same Type I parameters valid for the larger cutoff) to obtain
\[
\sum_{\substack{n\in I\\V_1<P^-(n)\le V_2}}
 C(n)R_y(m)\lambda(m)\log n=O_A(PL^{-A}).
\tag{6}
\]
There is no unsupported assumption about independence of the two actual factors or parity in an individual sign class.

## 3. Symmetric \(V\)-rough comparison: the important actual BV modulus

There is a parallel valid formula for the smaller target with \(R_V(m)\) in place of \(R_y(m)\). To prove its Type I first term
\[
\sum_{n\in I} C(n)R_V(n)R_V(m)\lambda(m)\log n=O_A(PL^{-A}),
\tag{7}
\]
expand the exact \(V\)-smooth divisor sums of \(n\) and \(m\), retaining \(R_z(n)\) and \(m\) a target unit (both are already true on the original support). Truncate source \(d\le P^{.4}\) and complement \(v\le P^{.1}\). The Rankin bound (3) applies to both, changing \(.4\) to \(.1\) for \(v\); choose \(c\) once with the smaller threshold and all powers in mind. One must justify two truncations together even when their **absolute** expanded weights multiply. Let \(E(x)\) be the number of squarefree \(V\)-smooth divisors of \(x\) above the chosen cutoff. Then \(0\le E(x)\le\tau(x)\) and \(\sum_{x\le P}E(x)\ll P L^{-A'}\) for arbitrary prescribed \(A'\) after choice of \(c\), by (3). Also
\[
\sum E(x)^2 \le
\left(\sum E(x)\right)^{1/2}
\left(\sum\tau(x)^3\right)^{1/2}.
\]
Replace one exact indicator by a truncated divisor sum at a time. The first error has the other exact indicator bounded by one; the second has the other truncated sum bounded in magnitude by \(\tau\). Cauchy–Schwarz with ordinary fixed divisor moments pays the second error too, including logs and true selector weights, by choosing \(A'\) large. This establishes a genuine integer-weight truncation, not a truncation holding only for a factored model.

The rest is the same shifted Type I calculation with additional \(v\mid m\), but now \(v\) can be polynomial rather than subpower and can use the same prime **range** as translated packet moduli. Write \(m=v b\); \(\lambda(m)=\lambda(v)\lambda(b)\) even if \(v,b\) share primes. For a nonempty arithmetic term, \(v\) is coprime to the source modulus \(d e\) (where \(e\) opens the \(k\)-rough condition), since any common prime divides both \(n\) and \(m\) and hence \(P\), which \(v\) avoids under the target-unit condition. It is also coprime to each translated packet profile modulus \(a_o e_o\): a common packet prime would divide \(m\) and \(m+(o-1)P\), hence \((o-1)P\), impossible since the packet prime exceeds \(M+1\) and avoids \(P\). This is a consequence of exact congruences; range separation here would be false. Different profile slots are coprime similarly, and \(\ell\mid a_o,e_o\) **within** a slot is still allowed since \(a_o e_o\) is the actual divisibility modulus. Keep the same old relative-shift shell assignments, projection to target-unit CRT classes, and joint-profile selector.

The actual endpoint for the known maximal Liouville BV is \(X_v=P/v\), with \(P^{.9}\le X_v\le P\), while the modulus for \(b\) is
\[
d e \operatorname{rad}(P)\prod_o a_o e_o\le P^{.4+o(1)}< X_v^{.46}.
\]
All congruences after eliminating \(v\) remain reduced, using the just-proved coprimalities; prepare the residue of \(b\) at target primes exactly as in the old Type I proof. The small source/profile omission errors still count \(O(P/(de\,v\prod_o a_o e_o)+1)\) for every nonempty tuple (and may ignore a target-unit factor for an upper bound). Their full floor loop increases by at most \(P^{.1}\), and stays \(P^{.5+o(1)}\); reciprocal sums of \(v\) contribute at most \(O(\log V)\) by Mertens. Earlier packet-profile truncation tails also tolerate both extra divisor weights by fixed higher divisor moments. For fixed \(v\), the same factorization/CRT coefficient bound by fixed \(D_0^{\omega(q)}\) times log powers holds, since the old slots are unchanged and \(v\) is not counted as a decomposition of \(q\). All real \(b\) endpoints remain \(\asymp_J P/v\), and \(\log(P-vb)\) has bounded-variation nonconstant part on this interval. The known weighted maximal BV and \(\sum_v1/v\ll\log V\) now pay (7), just as in the prior proof. Nothing treats \(P\) as the endpoint when \(v\) is large.

## 4. Remove the nonsymmetric translated mark before using reflection

Assume now \(J\) symmetric under \(t\mapsto1-t\). Under \(R_V(n)R_V(m)\), the source \(R_z(n)\) is identically one **on both orientations**, so keeping it in the expansion of (7) will not break the later reflection. The translated selector \(C(n)\), however, need not equal \(C(m)\). First remove it in absolute weight by a real integer two-root sieve.

For each greedy witness of simultaneous failure at all \(M\) offsets, at packet \(\ell\) the extra forbidden classes \(jP\bmod\ell\) are mutually distinct and distinct from the baseline roots \(0,P\); \(\ell>M+1\), and \(\ell\nmid P\). At target primes the baseline roots coincide iff \(\ell\mid P\). All packet primes are below \(V\) for large \(P\). Apply the elementary Selberg square with sieving primes **all primes \(\le V\)** and divisor level \(D=P^{1/40}\); the expected divisor log under the full normalized product of Selberg \(h\) weights is \(O_M(\log V)=o(\log D)\), so the denominator is at least half the full product by Markov. The floor is \(O(D^4)\) per witness. Baseline good density is \(\asymp S(P)/(\log V)^2\); each packet exclusion saves at least its relative \(e^{-t_i/\ell}\) factor. The same strict greedy margin and poly-\(\log L\) witness count give
\[
\#\{n\in I:R_V(n)R_V(m)=1,\ C(n)=0\}
 \ll \frac{P S(P)}{(\log V)^2}L^{-M/200}+P^{.11}.
\tag{8}
\]
The identical sieve ignoring extra packet classes gives \(\ll P S(P)/(\log V)^2+P^{.11}\) for all doubly rough rows. Thus multiplying by \(L\), the original marked symmetric high term and its unmarked version differ by
\[
O\bigl(P S(P)L^{-1-M/200}(\log L)^2+P^{.12}\bigr)
=o(PV_y(P)/L)
\]
for \(M>200\) (strictly \(M/200>\delta\) suffices). The estimate also holds with the roles interchanged, or by the symmetry of the unmarked set. No pointwise equality of the marks is presumed.

On the unmarked symmetric set use \(n\leftrightarrow m\), pairing \(T_V(n)\lambda(m)+T_V(m)\lambda(n)\). Every prime/composite pair is favorable: \(\lambda\) of the prime equals \(-1\), and only the composite has nonzero \(T_V\). Both primes contribute zero to the high pair. If both are composite then:
* two positive Liouville values (even total factor counts) give \(-\log n-\log m\), the only negative **bulk**;
* two negative Liouville values give \(+\log n+\log m\);
* opposite signs give \(\pm(\log n-\log m)=O_J(1)\).

The \(O(1)\) mixed-parity total is bounded using the unmarked upper in (8) without packet factors, by \(O(P S(P)(\log L)^2/L^2)=o(PV_y/L)\). This is exact accounting on a smaller complementary rough cutoff, not a replacement for the asymmetric original \(R_y(m)\) assertion (5).

## 5. What combinations of cutoffs do and do not remove

Formula (6) pays true least-prime shells depending on the choice of \(V\), even if their absolute mass is large. But for **any** finite linear combination of decompositions (1) with coefficients \(c_i\) satisfying \(\sum_i c_i=1\) to retain the original prime coefficient, the high coefficient is still \(-\log n\) on every composite with \(P^-(n)>\max_i V_i\). On any genuine double-core pair with both factors composite and positive Liouville values, this leaves the same negative bulk. The same holds for normalized combinations of symmetrically cut marked targets on such a double core. In particular polynomial-factor semiprime pairs are already beyond all the certified \(V_i=\exp(c_i L/\log L)\) cutoffs. This is an algebraic limitation of this family of decompositions, not an assertion that these pairs exist or are abundant.

On the symmetric doubly rough set, the selector-free one-coordinate parity means are controlled by the same Type I and reflection. But the even/even count involves the mixed sign through the exact identity
\[
4\,1_{\{\lambda(n)=+1,\lambda(m)=+1\}}
=1+\lambda(n)+\lambda(m)+\lambda(n)\lambda(m).
\]
Controlling the first three terms does not alone control the last beyond its trivial absolute bound. If estimating the **net** rather than an adverse upper, odd/odd terms with primes distinguished also matter; the parity means merely re-express the original prime-weighted difficulty. No mixed parity or broad even/even bound is claimed here.
