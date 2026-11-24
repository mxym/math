# A true adverse B3 chamber paid in a one-sided product-log strip

An unsigned upper bound used only with the known adverse sign, not a cancellation of two unrelated sign libraries. Unlike the all-large \(A_2\) source where a prime complement is favorable, the prime complement here is genuinely adverse.

## 1. Statement

Let \(P\) be large even, \(L=\log P\), \(\operatorname{rad}(P)\le L^B\), \(I=PJ\) fixed interior, \(y=e^{L^\delta}\), \(0<\delta<.1\), and \(z=e^{L^{.24}}\). Use the smooth high-source \(B_3\) chamber from [the verified sign table](SmallRadicalShiftedBilateralSignTable.md): \(n=pq R\in I\) squarefree with true primes \(z<p\le q\le U_-\), \(R>P^{1/4}\), \(t=pq>U_-\), where \(U_-=\exp(L/4-2L^{3/5})\). Its actual coefficient is
\[
T(n)=(1-g(\log t))\log R\ge0,\qquad 0\le g\le1.
\]
For any fixed \(\epsilon\) with \(\delta<\epsilon<1\), require
\[
0<\log(t/U_-)\le W_0:=L^{1-\epsilon}.
\tag{1}
\]
Let the true complement \(m=P-n\) be \(y\)-rough, squarefree, and either prime or of **rank three**. Then \(\lambda(m)=-1\). The magnitude of these genuinely adverse terms is
\[
\sum_{\text{actual rows in (1)}} T(n)
\ll PS(P)L^{-1-\epsilon}(\log L)^3+P^{.94}
=o(PV_y(P)/L).
\tag{2}
\]
No size restriction or additional angular narrowing is put on the rank-three complement: in particular it can be balanced. A normalized actual translated selector can only decrease this negative mass. Since these complements have rank at most three, they are also all base-uncovered once \(K>3\). The conclusion does not pay the dispersed \(B_3\) region outside (1).

## 2. A true joint two-prime lattice sieve

Write \(m=w r\), where \(r\) is the unique largest true prime of the squarefree \(m\). If \(m\) is prime, \(w=1\); otherwise \(w\) is the product of its two smaller true primes. Thus \(w\le P^{2/3}\), \(r\gg_J P^{1/3}\), and
\[
\sum_{\substack{\text{allowed }w}}\frac1w
\le 1+\tfrac12\left(\sum_{y<\ell\le P^{2/3},\,\ell\text{ prime}}\ell^{-1}\right)^2
\ll 1+(\log L)^2.
\tag{3}
\]
The product \(t=pq\le U_-e^{W_0}\le P^{.25+o(1)}\) has a unique unordered prime pair. On a true row \(tR+wr=P\), \((t,w)=1\): a common prime divisor exceeds \(y\), and could not divide \(P\). Thus skip fixed \(t,w\) with gcd \(>1\). Fix the rest. All actual solutions are on the same lattice
\[
R=R_0+w k,\qquad r=r_0-t k,
\]
and \(n=tR\in I\) restricts \(k\) to an interval of length \(O_J(P/(tw))\). Ignoring any extra inequalities that designated the largest prime only enlarges the count. On the true rows both prime slots \(R,r\gg_J P^{1/3}\): for \(R\) this follows also from \(t\le P^{.25+o(1)}\).

Take the squarefree Selberg sieve of divisor level \(D=P^{1/200}\) and sieve primes up to \(Z=D^\gamma\) for sufficiently small fixed \(\gamma>0\). All actual \(R,r\) exceed \(Z\) and hence must survive at every sieve prime. If a prime \(\ell\) divides neither \(t\) nor \(w\), each affine form has a single bad root in \(k\bmod\ell\), and the roots coincide iff \(\ell\mid P\), by the exact equation and unit slopes. If \(\ell\mid t\) or \(\ell\mid w\), only one form has a root and the other is a fixed target unit there. Such \(\ell\)'s all exceed \(y\), and relative to baseline the total Euler product changes by \(1+O(1/y)\), since \(t\) and \(w\) together have at most four prime factors. Thus the local survival product is
\[
\ll S(P)/L^2
\]
by the standard target singular factors and Mertens. In particular there is no fictitious independence between the two zero roots at primes dividing \(P\).

The same finite Selberg square with \(\lambda_1=1,\ |\lambda_d|\le1\) used in [the earlier Selberg proof](SmallRadicalShiftedNaturalScaleReservoir.md) gives a uniform upper bound
\[
\ll \frac{P S(P)}{tw L^2}+D^4
\tag{4}
\]
on the count of actual \((R,r)\). The local expected divisor log is \(O(\log Z)\) (at most two bad residues per prime before normalization), so the fixed \(\gamma\) makes the denominator comparison valid by Markov. The floor \(D^4\) uses at most \(D^2\) ordered weights and at most \([d_1,d_2]\le D^2\) bad residue classes. This bounds actual count even if a pair has fewer values in its \(k\)-interval than the formula's expected main.

## 3. One-sided angular saving and the whole signed bill

Put \(U=\log U_-\). For \(p\le q\) satisfying (1), \(\log p\le (U+W_0)/2\), so every admissible \(q\) has \(\log q\ge U-\log p\gg L\). At fixed \(p\) its permitted log interval is contained in
\[
(U-\log p,\ \min(U,U+W_0-\log p)],
\]
of width at most \(\min(\log p,W_0)\). The prime reciprocal asymptotic with arbitrary-log error at polynomial endpoints gives uniformly
\[
\sum_{\text{such }q}q^{-1}
\ll \frac{\min(\log p,W_0)}{L}+O_A(L^{-A}).
\tag{5}
\]
This also handles an empty interval by reading its sum as zero. By splitting \(\log p\le W_0\) and \(\log p>W_0\), and using \(\sum_{p\le e^{W_0}}(\log p)/p\ll W_0\) plus \(\sum_{p\le P}1/p\ll\log L\), we obtain
\[
\sum_{\text{allowed }t}t^{-1}
\ll \frac{W_0}{L}(1+\log L)+O_A(L^{-A}\log L)
\ll L^{-\epsilon}\log L.
\tag{6}
\]

Now sum (4) with the true high weight \(0\le T(n)\le L\). The main from (3),(6) is \(O(PS(P)L^{-1-\epsilon}(\log L)^3)\). The floor is \(O(L D^4 P^{.25+o(1)} P^{2/3}) = O(P^{.94})\); the two cofactor loops only count possible \(t,w\), and the prime pair factorization of each is unique, so there is no uncounted log-factor such as a second source-factor ordering. This proves (2). The sign is known row-wise since \(T(n)\ge0\) while \(\lambda(m)=-1\), and does not depend on statistical conjectures about the parity of either prime library.

A quick refinement in a much smaller lower-factor slice is available if desired: when \(\log p\le L^\beta\), \(\beta<3/5\), then \(\log t-U\le\log p\) because \(q\le U_-\). Since the smooth \(g\) is identically one up to \(U\) and is flat at that boundary, for any fixed \(j\) the genuine source weight in this slice is bounded by \(O_j(L(\log p/L^{3/5})^j)\). Applying the same sieve and (5) gives an arbitrarily strong power-log saving by choosing \(j\); it is not needed for (2).
