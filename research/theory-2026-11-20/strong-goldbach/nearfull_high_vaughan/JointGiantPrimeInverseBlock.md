# A larger signed block for the two actual prime marks

Use the notation and the actual coefficients \(P_{F,\mathcal R}\),
\(P_{G,\mathcal Q}\) of [the joint mark-block theorem](JointGiantActualMarkBlock.md).
In particular \(N\) is even, \(J\Subset(0,1)\) is fixed,
\(x\in NJ\), \(y=N-x\), \(L=\log N\), and
\(M_N=|J|N\mathfrak S(N)\). The profiles \(F,G\) are fixed
smooth real functions supported on \([0,b_F]\), \([0,b_G]\),
respectively, with \(b_F,b_G\le .002\). The genuine prime mark
windows \(\mathcal R=(R_-,R_+]\), \(\mathcal Q=(Q_-,Q_+]\)
are independent real intervals, with both lower endpoints at
least \(N^\xi\) for any fixed \(\xi>0\).

**Theorem.** On any of the following three rails, with the two
arms interchangeable,
\[
 (R_+,Q_+)\le (N^{.518},N^{.518}),\qquad
 (N^{.505},N^{.530}),\qquad
 (N^{.499},N^{.536}) ,
\]
where each bound is coordinatewise, the true, signed physical
subsum is
\[
 \sum_{\substack{x\in NJ\\(x,N)=1}}
       P_{F,\mathcal R}(x)P_{G,\mathcal Q}(y)
 =
 F'(0)G'(0)M_N
 \frac{\log(R_+/R_-)}{L}\frac{\log(Q_+/Q_-)}{L}
 +o_{F,G,J,\xi}(M_N).
\]
The statement is uniform in the indicated mark windows. If
either profile is constant on a fixed interval right of zero,
the left side is \(O_{A,F,G,J,\xi}(NL^{-A})\) for every fixed \(A>0\).

In particular for the actual flat profiles and cutoffs of the
[joint finite-rank theorem](JointGiantFiniteRank.md), the whole
matched covariance is supported, up to arbitrary-log error,
on mark pairs with \(\max(r,s)>N^{.518}\), rather than
\(\max(r,s)>N^{.510}\). The other two rails also delete named
mixed rectangles beyond this square. Overlapping bounds
must not be counted twice. No sign or lower bound is asserted
on the surviving joint block.

## Proof

**Literal Poisson.** Apply §1 of
[the joint mark-block theorem](JointGiantActualMarkBlock.md):
open the real divisors as \(A=dr,B=es\), where \(r,s\)
are the actual prime marks, \(d\le N^{b_F}\), \(e\le N^{b_G}\),
and \((AB,N)=(A,B)=1\). The conditions \(r<x\) and \(s<y\)
are automatic by the fixed upper powers. Smooth the spatial
interval in an arbitrary-log thin collar, at arbitrary-log
cost by the true crossed divisor moments. The resulting
test \(\Psi_{d,e}\) has compact interior support and each
fixed derivative is log-power bounded. After opening target
units, \(u\mid N\) with \(u>N^{.0001}\) are power-small by
the actual \(u\mid x\) counts and divisor envelope; for the
remaining \(u\) put \(X=N/u\). For each fixed \(u,d,e,r,s\)
the real progression formula is
\[
 \frac{X}{AB}\sum_{\nu\in\mathbb Z}
   \widehat\Psi_{d,e}\!\left(\frac{\nu X}{AB}\right)
                                   e_B(\nu X\overline A),
 \qquad e_B(t)=e^{2\pi i t/B}.
 \tag{1}
\]
The coefficients also contain the actual prime logs and
\(\mu(d)\mu(e)\mu(u)\).

Subdivide each mark interval by the standard dyads, keeping
its exact endpoints in each. Let \(R,S\) be the left dyad
edges for \(r,s\). If \(deRS\le N^{.9999}\), the real
progression floor and variation cost \(O(1)\) up to fixed
log powers for each prime pair. At fixed \(d,e\) their number
is \(O(RS)\ll N^{.9999}/(de)\). Hence after summation these
dyads have power-small error from their zero mode.

On the remaining dyads orient the marks so \(R\le S\), swapping
the profiles and reflecting the spatial test if necessary.
Both scales are \(\gg N^{.4599}\), since \(de\le N^{.004}\)
and the maximum mark is at most \(N^{.536}\).
In particular \(r,s\) cannot divide the short \(d,e\).
Cut (1) at
\[
 V=\left\lceil N^{\rho}(1+deRS/X)\right\rceil,\qquad
                         \rho=.00004.
\]
Rapid Fourier decay, with a sufficiently large fixed derivative
norm as above, makes the total discarded tail power-small
even after all labels. Indeed the rescaled frequency
\(|\nu|X/(AB)\) in the tail is \(\gg N^\rho\), and summing
the decreasing tail with step \(X/(AB)\) absorbs the
prefactor \(X/(AB)\) and saves any fixed power.
The retained nonzero frequencies
satisfy \(0<|\nu|<s\): indeed \(V/S\ll N^\rho/S+
 N^\rho deR/X=o(1)\). Retain the exact residue conditions,
not an independent distribution model.

**Recovery of one of the true prime marks.** Fix
\(u,d,e,\nu\) on such a dyad. Write \(g=(|\nu|,e)\),
\(E=e/g\) and \(q=sE\). Because \(|\nu|<s\),
\((|\nu|,B)=g\) and
\[
 e_B(\nu X\overline{dr})
   =e_q(c_s\overline r),\qquad
 c_s=(\nu/g)X\overline d\bmod q,\qquad (c_s,q)=1 .
 \tag{2}
\]
Here \((X,q)=1\) follows from the actual \(B\)-unit
mask. Coprimality of \(A,B\) reduces to \((d,e)=1\)
and \(r\ne s\); the latter is exactly enforced in the
prime reciprocal sum by \((r,q)=1\), since \(s\mid q\)
and \(r>e\). The actual \(r\)-unit mask with respect to
\(N\) omits only \(O(L)\) prime labels per \(s\), costing
at most \(O(L^2)\) with prime-log weights.
For fixed \(e,\nu\), the map
\(s\mapsto q=sE\) is injective into the true integer
modulus dyad \(Q<q\le2Q\), \(Q=ES\).

The primary input is
[Baker, Acta Arith. 156 (2012), Theorem 2](https://www.impan.pl/shop/en/publication/transaction/download/product/82065).
For \(Q^{1/2}\le T\le2Q\) and each fixed \(\varepsilon>0\),
\[
 \sum_{q\sim Q}\max_{(a,q)=1}
  \left|\sum_{\substack{T<p\le2T\\(p,q)=1}}
                  e_q(a\overline p)\right|
 \ll_\varepsilon Q^\varepsilon
                   (Q^{11/10}T^{4/5}+QT^{11/12}).
 \tag{3}
\]
For any **common** endpoint \(t\le2R\le2Q\), split the
prime prefix up to \(t\) into dyadically decreasing intervals
of the displayed form, stopping at the first left edge below
\(\sqrt Q\). The remaining initial segment has length
\(O(\sqrt Q)\), costing \(O(Q^{3/2})\) for all these moduli.
Thus, for any common prefix endpoint in the true \(r\)-window,
subtracting its fixed lower prefix and then using partial
summation for \(\log r\) gives
\[
 \sum_{\substack{s\text{ actual}\\S<s\le2S}}
 \left|\sum_{\substack{r\text{ in its window}\\r\le t,\ (r,qN)=1}}
           (\log r)e_q(c_s\overline r)\right|
 \ll_\varepsilon L^{O(1)}N^\varepsilon
    \big(Q^{11/10}R^{4/5}+QR^{11/12}+Q^{3/2}\big).
 \tag{4}
\]
The cost \(O(SL^2)\) of omitting target primes is absorbed
by this estimate. The arbitrary unit numerators in (3)
allow \(c_s\) to vary with \(s\).

At fixed \(s,\nu\) the amplitude in (1), as a function of
the real \(r\in[R,2R]\), obeys
\[
 |W_s(r)|+R|W'_s(r)|\ll
                  \frac{X}{deRS}L^{O(1)}.
\]
Indeed \(W_s(r)=X/(dres)\cdot \widehat\Psi_{d,e}(\nu X/(dres))\);
\(\widehat\Psi_{d,e}(v)\) and \(v\widehat\Psi'_{d,e}(v)\)
are uniformly log-power bounded. Endpoint values and
the integrated partial summation error are therefore
controlled by (4) at the **same** \(t\) for every \(s\);
we do not take a supremum of independently chosen endpoints
inside the modulus sum. The outer prime log costs only \(L\).

Now \(Q\le eS\), and summing \(|\nu|\le V\) costs the
factor
\[
 \frac{X}{deRS}V\ll N^\rho(1+X/(deRS))\ll N^{\rho+.0001}.
\]
Consequently, apart from \(N^{\rho+.0001+\varepsilon+o(1)}\),
the summed nonzero exponents are bounded by
\[
 .004+
 \max\big\{1.1(\sigma+.002)+.8\alpha,\ \
                \sigma+.002+11\alpha/12,\ \
                1.5(\sigma+.002)\big\},
\]
where \(R\le N^\alpha,S\le N^\sigma\).
The \(.004\) pays all actual short label pairs, irrespective
of the dyadic orientation. After that orientation the
three allowed pairs \((\alpha,\sigma)\) are
\((.518,.518),(.505,.530),(.499,.536)\).
The respective maxima including \(.004\) are
\(.9988334\ldots,.9989167\ldots,.9994167\ldots\)
(as upper decimal roundings). Choose \(\varepsilon\)
small; every summed nonzero term is power-small,
also over the \(O(L^2)\) dyad pairs and the \(N^{o(1)}\)
actual target divisors \(u\).

**Zero mode.** The zero term of (1) and the elementary
floor cases are exactly those of §3 of
[the joint mark-block theorem](JointGiantActualMarkBlock.md),
with unchanged masks \((d,Ns)=(e,Nr)=(d,e)=1\).
That harmonic computation uses no restriction on the
upper mark beyond the polynomial lower size of each
actual prime and the automatic \(r<x,s<y\). In brief,
restoring \(u\) gives exactly \(\varphi(N)/N\);
the signed short harmonic in \(d,e\) vanishes to order one
in each log-angle. Its product derivative local factor
after insertion of the CRT unit density is
\(\mathfrak S(N)c(rs)/L^2\).
Here \(c(rs)=1+O(N^{-\xi})\); genuine separate prime-log
harmonics over the literal windows give the two
displayed angular lengths, with the diagonal power-small.
If either profile is flat the entire short-box harmonic
has arbitrary-log saving instead. This proves the theorem.
