# A signed true factor tranche of k is payable by Type I

Written research note, 2026-11-24. This is a statement about the actual multiplicative sign of a large set of prime factors of k at each fixed \(P=2^j\). It does not replace the parity of the remaining factor by an independent sign and does not pay the full G23 term.

Use the actual vectors \(B_C,H_C,A_C=H_C-B_C\), ranges, and cutoffs of the [angular projection note](G23ActualAngularProjectionCompensation.md), with \(L=\log P\), \(z=e^{L^{.24}}\), \(y=e^{L^\delta}\), \(0<\delta<.1\). Put \(k_{\le w}=\prod_{q\le w}q^{v_q(k)}\) and \(f_w(k)=\lambda(k_{\le w})\). On the genuine rough support only primes \(z<q\le w\) matter. The test vector is \(f_w(k)/k\); one never discards its dependence on k.

## Statement

For any physical k interval \(\mathcal K\), the actual unmarked rough Liouville vector obeys
\[
 \sum_{k\in\mathcal K}R_z(k)f_w(k)A_1(k)=O_A(P L^{-A}).
 \tag{1}
\]
The estimate is uniform in the endpoints and holds for each fixed \(A\), with the following choices:
1. The full original prime slopes \(P^\sigma<p\le P^{1/2}e^{-L^{3/5}}\) and \(w=e^{L^\nu}\), any fixed \(.24<\nu<.6\).
2. A fixed power separated upper slope \(p\le D'=P^{1/2-\varepsilon}\) (assuming \(\sigma<1/2-\varepsilon\)) and \(w=P^{a/\log L}\) with fixed \(a>0\) sufficiently small in terms of \(\varepsilon,A\). Both vectors and prime counts are restricted to the same cap when using this option.

There is also an explicit signed prime-layer main term on any fixed nonempty angular k interval \(u\le\log k/L\le v\) lying strictly inside the untruncated range for the chosen slope cap (so \(u>1/2\), or \(u>1/2+\varepsilon\) in option 2, and \(v<1-\sigma\)). Set
\[
 G(z,w)=\prod_{z<q\le w,\ q\ {\rm prime}}\left(1-\frac{2}{q-1}\right).
\]
Then on that actual chamber, with the notation \(V_z(P)=\prod_{3\le q\le z}(1-1/(q-1))\),
\[
\sum_{P^u\le k\le P^v}R_z(k) f_w(k)B_1(k)
 =(1+o(1))(b-a)\frac{P V_z(P)}{L}
 \left(\int_u^v \frac{dt}{1-t}\right) G(z,w).
 \tag{2}
\]
Here \([a,b]=J\); in option 2 use a different name, e.g. \(a_0\), for the positive cutoff constant in \(w=P^{a_0/\log L}\). Mertens gives \(G(z,w)=(1+o(1))(\log z/\log w)^2>0\). In option 2, choose \(A>10\) and then \(a_0\) for (1); this is more than the fixed saving needed in (2). By (1), \(B_1\) can be replaced in (2) by the genuine signed composite vector \(H_1\). The same relative matching holds for the literal marker \(C\) with fixed \(M\ge400\) in option 1 and fixed \(M\ge600\) in option 2. For arbitrary-log cancellation (1) with a marked vector, \(M\) must be chosen sufficiently large relative to the requested saving, or the explicit penalty in §3 must be kept.

## 1. Signed sieve expansion with controlled absolute error

First discard squareful rough k at absolute cost \(O_J(PL/z)\): for a physical dyadic block \(k\asymp K\), at most \(O(K/z)\) integers k are divisible by a prime square \(q^2\), \(q>z\), and each has at most \(O_J(P/K)\) candidate true p. There are \(O(L)\) blocks and all absolute row weights except the factor count are \(\le1\). Thus \(f_w(k)=(-1)^{\omega_{(z,w]}(k)}\) may be used everywhere, paying super-log-small absolute error when returning to actual multiplicities.

For \(s=\omega_{(z,w]}(k)\), Taylor's formula for \((1-t)^s\) at \(t=0\), evaluated at 2, gives
\[
 \left|(-1)^s-\sum_{i=0}^R(-2)^i {s\choose i}\right|
 \le 2^{R+1}{s\choose R+1}.
\]
For \(s>R\), use \(|1-t|^{s-R-1}\le1\) on \([0,2]\); for \(s\le R\) it is exact. The signed polynomial is therefore a sum over squarefree tranche divisors \(v\mid k\) with at most \(R\) primes, coefficients \((-2)^{\omega(v)}\), and its absolute size is at most one plus the displayed one-shell error.

Choose \(R=\lceil C_A\log L\rceil\), with \(C_A\) sufficiently large. Both rough indicators can be expanded using the usual upper Bonferroni depth \(O_A(\log L)\) and errors bounded by the next positive shell, as in the angular projection proof. The shell for the signed polynomial has reciprocal sum
\[
 \ll\frac{(2\sum_{z<q\le w}1/q)^{R+1}}{(R+1)!}=O_A(L^{-A})
\]
for any desired fixed saving after increasing \(C_A\), since the prime reciprocal sum is \(O(\log L)\). Retained absolute reciprocal sums are at most fixed powers of L, even with \(|(-2)^{\omega(v)}|\). Products of the two rough-sieve errors with this polynomial are bounded using its pointwise bound by one plus its shell. All these absolute error estimates refer to the actual p,k lattice: for retained \(d\mid k,v\mid k,e\mid m=P-pk\), \(d\) is made of primes \(\le z\), \(v\) of primes \(>z\), \(e\) of primes \(\le y\), and one may impose target units first. Shared prime between \(dv\) and \(e\) is then impossible in a nonempty tuple. Also \(p>w\) for large P in either option. The count in every nonempty lattice is \(O(P/(pdve)+1)\). The weighted harmonic tail is therefore \(O_A(PL^{-A})\), using \(\sum_p1/p=O_\sigma(1)\) and choosing larger auxiliary powers if needed. Absolute floor counts are \(P^{1/2+o(1)}\) in option 1, and \(P^{1/2-\varepsilon}(w^{R+1})P^{o(1)}\) in option 2, with log-power coefficient factors harmless. Take \(a_0 C_A<\varepsilon/4\) (or an even smaller \(a_0\) to cover the extra layer).

## 2. Pay the signed variable by actual BV; retain the true prime normalization

For fixed \(p,d,v,e\) in the Liouville expansion, intersect the real \(\mathcal K\) with \([aP/p,bP/p]\) before reflecting into \(m'\!=m/e\). The literal interval has endpoints comparable to \(P/e\), and the reduced modulus is \(pdv\) with the exact target unit test, representable as \(2pdv\). The modulus log increases by \(O_A(L^{.24}\log L)+(R+1)\log w\) beyond \(\log p\). This is \(o(L^{3/5})\) with the prescribed full-range \(w\), or at most \((\varepsilon/4+o(1))L\) with the reduced-slope \(w\). The full Liouville BV input of the [near-root shifted Type I note](SmallRadicalShiftedHighChambers.md) (from [Granville–Shao, Thms. 1.1(b), 2.1](https://arxiv.org/html/1706.05710v1) and the actually removed coprime mean) applies at this endpoint \(P/e\), even accounting for maximal endpoints by polylog grids and partial summation. By unique factorization and the disjoint ranges of \(p,d,v\), the physical modulus identifies the tuple \((p,d,v)\). Coefficients \(2^{\omega(v)}\) are log powers, absorbable into the requested BV saving, and summing \(e\) costs its harmonic mass. Complete multiplicativity only takes out \(\lambda(e)\); the genuine reflected \(\lambda(m')\) is what BV estimates. This proves (1).

For the true prime layer the same expansion has no need for the \(e\) factor: genuine primes \(m\asymp P\) already pass \(R_y\). The profile for \(d\) contributes \(V_z(P)\), while the tranche expansion for \(v\) contributes the exact factor \(\prod_q(1-2/(q-1))\), because the genuine residue tested at each \(q\mid v\) is \(m\equiv P\) in a reduced class and the true prime local density is \(1/(q-1)\). Prime BV, now at actual endpoint comparable to P and modulus \(pdv\), gives the usual main term plus arbitrary log saving (and the same absolute tails). After interchanging k integration with the genuine p sum, the established prime angular-bin calculation gives the \((b-a)\int_u^v (1-t)^{-1}dt\) factor, since the entire true p interval sits under the cap. The actual reciprocal prime product has the positive Mertens equivalent stated above; its absolutely convergent relative product error is \(O(\sum_{q>z}q^{-2})\). This proves (2) and the true signed composite matching in that direction.

## 3. Marker transfer and what factor remains

A true uncovered marker row contributes at most its original absolute cost; multiplying by \(f_w\) does not increase it. The suited count is \(O(P\kappa_z V_y(P)L^{-M/200})+O_A(PL^{-A})\) by the actual marker co-sieve, since the source n has at most \(1/\sigma\) candidate prime slopes. This is little-oh of (2): option 1 has relative extra decay of at most \(L^{-.72}\) beyond \(P\kappa_z/L\); option 2 has \(G(z,w)\asymp L^{-1.52}(\log L)^2\) up to its fixed factor. This justifies the stated choices 400 and 600.

For option 2, the genuine prime-energy distribution also shows that the unhandled part \(k_{>w}=k/k_{\le w}\) contains only \(O(\log\log L)\) prime factors outside a set carrying \(o(P^2\kappa_z/L^3)\) prime energy. Indeed \(\sum_{w<q\le CP}q^{-1}=\log\log L+O(1)\). The true factorial-subset high-tail proof of the [rank-concentration note](G23TruePrimeRankConcentration.md), using only those primes for d and taking \(s_0=(1+\eta)\log\log L\) and \(r=a_1\log\log L\) small relative to \(s_0\), gives a decaying \((\log L)^{-c_\eta}\) upper relative to the prime scale. As before squareful k are negligible in that energy, so distinct and multiplicity counts agree. Thus number-wise most rough prime factors of a typical prime-energy k are captured, by the previously proved \(\Omega(k)\sim .76\log L\) concentration.

However the included product is only \(P^{o(1)}\) in the corresponding energy sense. For squarefree k, \(\log k_{\le w}=\sum_{z<q\le w,\ q\mid k}\log q\). In the true prime square select one such divisor q, open \(k=qt\) and use the actual two-prime / one-rough upper count \(O((K/q)\kappa_z S(|p-p'|)/L^2)+P^{.04+o(1)}\) on a dyadic k block, as in the rank-concentration proof. The factor q is already rough; at q itself the reflected roots disappear, a factor \(1+O(1/q)\). The genuine slope singular average and \(\sum_{q\le w}\log q/q\ll\log w\) give total log-weighted energy \(O((P^2\kappa_z/L^3)\log w)\). Aggregate floors over \(q\le w=P^{o(1)}\) are still a power saving; include the diagonal separately even with \(\log k\ll L\). Hence for any fixed \(\rho>0\), the subset \(k_{\le w}>P^\rho\) costs only \(O((P^2\kappa_z/L^3)(\log w)/(\rho L))=o(P^2\kappa_z/L^3)\). The omitted large-prime factor still has almost the full polynomial size of k.

The exact original sign is \(f_w(k)\lambda(k_{>w})\). The few remaining factors cannot be deleted, treated as constant on k bins, or inferred to be independent. Directly opening them in ordinary BV increases \(p d v\) beyond the true endpoint's square-root level in general. A true shifted bilinear input or correlation with the remaining long multiplicative coefficient is still needed; the paper notes no full G23 or Goldbach conclusion.
