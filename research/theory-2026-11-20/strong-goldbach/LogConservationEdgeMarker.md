# A logarithmic marker with fixed-target cancellation at the long edge

The following is an unconditional cancellation result on a complete low-overlap slice for actual reflected primes. It does not prove the required inequality for the whole low residual, or strong Goldbach.

Use \(x=N/2,\ I=(x/2,x],\ L=\log x,\ M=M_N=\mathfrak S(N)x/(2L)\), and the actual and reference weights \(a,b\), \(w=a-b\), from [SinglePrimeRoughRowCriterion.md](SinglePrimeRoughRowCriterion.md). Write \(\alpha=31/200,\ \varepsilon=e^{-s/2},\ \delta=(s+2)\varepsilon,\ \beta=1/2-\delta,\ y=x^\varepsilon,\ z=x^{1/3-2\varepsilon},D=x^\beta\), at sufficiently large fixed \(s\). For any \(T>0\) define
\[
 F_T(n)=\sum_{\substack{d\mid n,\ d\le T\\ P^-(d)\ge x^\alpha}}\mu(d),\qquad F=F_D,\qquad t_j=\log_x j,\qquad \tau=t_n.
\]
The replacement for \(F\) is
\[
 G(n)=(2\tau-1)F(n)-2\sum_{\substack{q\mid n,\ q<x^\alpha\\q\ {\rm prime}}}t_q F_{D/q}(n).
 \tag{48}
\]
The sum is over distinct primes, whether or not \(n\) is squarefree. Put \(H_v(n)=1_{P^-(n)\ge v}\). Uniformly in the even target and with \(o_s(1)\) denoting \(N\to\infty\) at fixed \(s\),
\[
 \left|\sum_{n\in I} w(n)H_y(n)G(n)\right|
       \ll_\alpha [e^{-s}/\varepsilon+o_s(1)]M .
 \tag{49}
\]
Moreover \(G=(2\tau-1)F\) on \(H_{x^\alpha}=1\), including the high residual and the \(z\)-rough test. Their bounds in [CenteredMarkerHighRows.md](CenteredMarkerHighRows.md) therefore remain valid, up to \(o_s(M)\).

For \(2\delta\le\Delta\le .005\) fixed at that \(s\), let \(\mathcal E_\Delta\) comprise all \(n\in I\) with \(y\le P^-(n)<x^\alpha\) and a prime label \(P\mid n\) in \([x^{1/2-\Delta},D]\). Then
\[
 \left|\sum_{n\in\mathcal E_\Delta} w(n)G(n)\right|
   \ll_\alpha \left(\frac{\Delta^2}{\varepsilon}+\Delta+
                    \frac{e^{-s}\Delta}{\varepsilon}+o_{s,\Delta}(1)\right)M .
 \tag{50}
\]
The constants outside the final little-oh are independent of the large fixed \(s\) and the choice of \(\Delta\). For example \(\Delta=\varepsilon^{2/3}\) gives an arbitrarily small multiple of \(M\) uniformly in all sufficiently large even \(N\), by first choosing \(s\) large. This edge class itself has labelled rough reference mass of order \((\Delta/\varepsilon)M=\varepsilon^{-1/3}M\), not \(o(M)\). Its old marker \(F\) leaves a smooth-cofactor signed contribution on that larger scale (§4).

## 1. Transfer of the new total marker

The first term of (48) uses just the eligible divisor \(d\le D\). On \(I\), \(2\log_x n-1=1+O(1/L)\). The unmarked rough upper sieve gives \(\sum_{n\in I}(a+b)H_y\ll M/\varepsilon\), and \(F=O_\alpha(1)\). Thus the factor can be replaced by 1 in the absolute discrepancy bound at cost \(O_\alpha(M/(\varepsilon L))=o_s(M)\). For the second, expanding \(F_{D/q}\) introduces the physical modulus \(dq\le D\). Here \(q<x^\alpha\) and every prime of \(d\) is \(\ge x^\alpha\), so \(q\) is unique and coprime to \(d\). Terms with \(q<y\) vanish on the rough set. Separately enclose the nonnegative \(a,b\) sequences in each progression by the dimension-one sieves of level \(y^s\) and cutoff \(y\); the new modulus divides a product at most \(D y^s=x^{1/2-2\varepsilon}\). A prime of this local sieve is \(<y\), so its factor in the modulus can be identified separately from \(q,d\). Their unmarked/marked common main terms thus compare using the divisor-weighted ordinary BV estimates from (3) of the original criterion. Summing the fundamental lemma errors costs at most
\[
 \ll_\alpha e^{-s}\frac{M}{\varepsilon}
  \left(\sum_{d\ {\rm eligible}}\mu^2(d)g_N(d)\right)
  \left(1+\sum_{y\le q<x^\alpha}\frac{\log_xq}{q-1}\right)
 \ll_\alpha e^{-s}M/\varepsilon,
\]
where the eligible \(d\) sum is \(O_\alpha(1)\) by the bounded reciprocal sum on \([x^\alpha,D]\), and the last weighted sum is \(O(1)\) by Mertens. Moduli sharing a prime with \(N\) have zero main in both sequences and remain covered by the summed discrepancies. This proves (49).

Both \(|F|\) and \(|G|\) are \(O_\alpha(1)\), since the number of distinct eligible primes dividing \(n\le x\) is bounded by \(1/\alpha\), and \(\sum_{q\mid n}t_q\le1\). On the high or \(z\)-rough carrier the explicit small-prime term vanishes and \(2\tau-1=1+O(1/L)\). Absolute \(a+b\) mass of either carrier is \(O_\alpha(M)\) by (35) of the high note, so this change costs \(o_s(M)\) even for a signed sum. The test on prime \(n\in I\) remains positive, with weight \(1+O(1/L)\).

The underlying log conservation is \(\sum_{q\mid v}t_q=t_v\) on squarefree \(v\), the squarefree version of the identity behind [Goldfeld's large-prime-factor theorem](https://www.math.columbia.edu/~goldfeld/PrimeShifts.pdf). In particular the new weight where no small primes appear is unchanged to leading order; the logarithmic term in (48) principally modifies the low part.

## 2. Pointwise signature on the edge

Repeated prime factors of rough \(n\) have total \(a+b\) weight \(O(x^{1-\varepsilon}L)\) and bounded marker and label weights, so henceforth use squarefree \(n\). Fix a label \(P\) and put \(v=n/P,\ u=1-t_P,\ h=\Delta+\delta\). Then \(.5+\delta\le u\le .5+\Delta\). Call the primes in \([x^\alpha,D]\) eligible; let \(J(T)\) be the alternating subset sum of the eligible primes of \(v\), restricted to subset log-exponent \(\le T\). Products involving \(P\) and another eligible prime exceed \(D\). Write \(S_0=\sum_{q\mid v,\ q<x^\alpha,\ t_q\le\beta-t_P}t_q\). Exactly,
\[
 G=(2\tau-1)(J(\beta)-1)-2\sum_{q\mid v,q<x^\alpha}t_qJ(\beta-t_q)+2S_0 .
 \tag{51}
\]
There are at most three eligible primes in \(v\). Declare exceptions if \(v\) contains a prime \(Q>D\), or if its eligible radical has \(t\)-exponent \(>\beta\). If it has no eligible prime and is not exceptional, \(S=\sum_{q\mid v,q<x^\alpha}t_q=t_v\) and \(G=-2(S-S_0)\). Thus \(|G+1|\ll\Delta+1/L+S_0\) there. If its eligible radical \(m_v\) lies in \((1,D]\), then \(J(\beta)=0\), and only an eligible subset \(d\mid m_v\) with \(dq>D\) can change \(J(\beta-t_q)\) from zero. Since every contributing pair satisfies \(dq\mid v\) and \(t_v\le u\), equation (51) implies
\[
 |G+1|\ll_\alpha 1/L+S_0+
 \sum_{\substack{d\mid v,\ d\ {\rm eligible}\\d\le D}}
 \ \sum_{\substack{q\mid v,\ q<x^\alpha\\\beta<t_{dq}\le u}} t_q .
 \tag{52}
\]
The error \(|G+1|\) is \(O_\alpha(1)\) on both exceptions. If \(n\) has a second edge label, its exponent lies between \(.5-\Delta\) and \(u\), an interval of width at most \(2\Delta\). There are at most two labels overall.

## 3. Reference counting at the necessary scale

For fixed \(P\) set \(X=x/P\). All ordinary counts below are of \(y\)-rough \(v\in(X/2,X]\). The uniform rough count bound \(\Phi(T,y)\ll T/(\varepsilon L)+1\) for every \(T\ge1\) follows from the upper rough-number theorem for \(T\ge y\) and the singleton bound for \(T<y\) (e.g. [Fan, arXiv:2306.03347](https://arxiv.org/abs/2306.03347)). Its constant can be absolute as \(s\) varies. We first work with all rough \(v\), dropping the low cutoff for nonnegative upper estimates.

- A marked prime \(Q>D\) has exponent in \((\beta,u]\), and a second label belongs to the strip in §2. In either case its reciprocal sum is \(O(h)+o(1)\), from the bounded-away-from-zero endpoints of the strip. For each \(Q\), count the remaining rough cofactor by the displayed bound at \(T=X/Q\). The \(+1\) sums to \(O(X/L)\) because the number of possible \(Q\le X\) is at most \(O(X/L)\).
- On the eligible radical exception choose a product \(d\) of \(j\le3\) eligible primes with \(\beta<t_d\le u\). The reciprocal sum of such \(d\) is \(O_\alpha(h)+o(1)\), by fixing \(j-1\) factors with bounded total reciprocals, then using a prime reciprocal interval in exponent of width \(h\) and lower endpoint at least \(\alpha\). For the \(+1\), fix the same \(j-1\) factors with product \(d'\). If the range of the final prime is nonempty then \(X/d'\ge x^\alpha\); its count is \(O_\alpha(X/(d'L))\). Summing over \(d'\) gives \(O_\alpha(X/L)\).
- For \(S_0\) and the crossing sum (52) the small marked prime \(q\) is weighted by \(t_q\). Fix the eligible subset \(d\) (take \(d=1\) for \(S_0\)). The allowed exponent interval for \(q\) has width at most \(h\), since \(0\le\beta-t_P\le\Delta\), or since \(\beta<t_d+t_q\le u\). By \(\sum_{q\le Y}(\log q)/q=\log Y+O(1)\), its weighted reciprocal sum is \(O(h+1/L)\), uniformly even for lower endpoint \(t_q\) close to \(\varepsilon\). The \(+1\) cost, weighted, is at most \(\sum_{q\le X/d}(\log q)/L\ll X/(dL)\) by Chebyshev, with absolute constant independent of \(\varepsilon\) and also valid for \(X/d<y\). The other factors of \(d\) have bounded total reciprocal sum. This argument is why the elementary boundary error does not introduce powers of \(1/\varepsilon\).

The \(\Delta+1/L\) bulk term uses \(\Phi(X,y)\ll X/(\varepsilon L)\) here. Every upper calculation therefore gives, for one label and normalized by \(X/L\), at most \(O_\alpha(h/\varepsilon+1)+o_{s,\Delta}(1)\) of ordinary weighted counts. The prime sum \(\sum_{P}1/P=O(\Delta)+o_{s,\Delta}(1)\) yields
\[
 O_\alpha\left(\left(\frac{\Delta^2}{\varepsilon}+\Delta\right)x/L\right)
     + o_{s,\Delta}(x/L).
\]
Translation to \(b\) costs the singular factor \(\mathfrak S(N)\), and \(a\) is at most four times the leading \(b\) bound, by (35) for each nonnegative labelled polyhedral weight, with fixed-\(s\) minimal exponent \(\varepsilon\) and rank at most \(1/\varepsilon\). This is a use of that estimate at fixed \(s,\Delta\); no uniform factorization theorem as \(\varepsilon\to0\) is asserted. The leading constants are uniform because they were supplied by the ordinary count estimates just proved. Signed bounds are not inferred from factor 4 itself. The resulting estimates bound both the labelled \(a+b\) mass weighted by \(|G+1|\) and the unweighted \(a+b\) mass of duplicate-labelled elements by \(O_\alpha((\Delta^2/\varepsilon+\Delta)M)+o_{s,\Delta}(M)\).

By §2 of [CenteredMarkerLongOverlap.md](CenteredMarkerLongOverlap.md), restricted to this band, the **total** labelled rough \(w\) sum is \(O_\alpha(e^{-s}\Delta M/\varepsilon)+o_{s,\Delta}(M)\): \(P\ell\le Dy^s\) as before and the reciprocal sum of labels is \(O(\Delta)\). Removing all \(x^\alpha\)-rough products from this sum costs \(O_\alpha(\Delta M)+o_{s,\Delta}(M)\) on each of \(a\) and \(b\). Indeed the compact fixed-rank simplex in (35), with all exponents at least \(\alpha\), lies within a strip of width at most \(\Delta\) in a labelled coordinate; each possible label has this bound, and only a fixed number of ranks and labels occur. The net labelled \(w G\) sum can now be written as \(-\sum w+\sum w(G+1)\). Correcting duplicate labels costs only the duplicate mass just bounded, because \(|G|\ll_\alpha1\). These estimates prove (50).

## 4. What changed and what remains

At \(\Delta=\varepsilon^{2/3}\), first let \(N\to\infty\) at fixed \(s\). Then let \(s\to\infty\). The ambient labelled \(b\) mass satisfies
\[
 \frac{\varepsilon B_\Delta}{\Delta M}\longrightarrow 2e^{-\gamma},
\]
in the corresponding uniform iterated limit. This follows as before from \(\sum_P 1/(P-1)\sim\log((.5-\delta)/(.5-\Delta))\sim2\Delta\) and the sieve-density formula; the high labels removed cost \(O_\alpha(\Delta M)\). The subfamily where \(v\) is \(x^\alpha\)-smooth has positive relative \(b\) mass tending to \(\rho(100/31)>0\). The marked Buchstab inclusion-exclusion in §3 of the long-overlap note is uniform in \(u\) in this band, and gives this ratio as \(u\to.5\).

To identify the old unresolved term on **the same** edge: outside the exceptions of §2, \(F=0\) when \(v\) is smooth and \(F=-1\) otherwise. The old labelled discrepancy is therefore the smooth-cofactor \(a-b\) discrepancy plus errors bounded by the right side of (50); the same holds after deleting duplicate labels. The previous envelopes compared that smooth class only by a fixed sieve factor, on reference scale \((\Delta/\varepsilon)M\). The new marker treats its dominant contribution together with the common labelled total, attaining \(o(M)\) on the edge for the new observable. It does not establish the old smooth-cofactor discrepancy itself is small.

For a fixed-width band, the same bound costs \(\Delta^2M/\varepsilon\), not \(o(M)\). The key errors are actual bands where the eligible radical or \(dq\) lies near \(\beta\), and the variation \(t_v-.5\) on smooth cofactors. Nor is the change freely localizable. In \(G-F\) the \(2(\tau-1)F\) term is negligible on the full rough carrier at fixed \(s\). Expanding the other term, the only eligible divisor containing an edge label \(P\) that can ever appear is the singleton \(P\). Thus the part of the correction whose Type I moduli already contain an edge label is exactly \(2\sum_{P\mid n,\ P\ {\rm edge}}S_0(P,n)\), with absolute weighted edge mass \(O_\alpha((\Delta^2/\varepsilon+\Delta)M)+o_{s,\Delta}(M)\) by §3. The dominant correction instead comes from divisor terms not containing that edge label, including \(d=1\). Inserting \(P\mid n\) to localize those terms would replace \(dq\le D\) by \(Pdq\), which already exceeds \(D\) whenever \(t_{dq}>\beta-t_P\). On a smooth cofactor this is exactly the dominant part \(-2\sum_{q>D/P}t_q\). In particular this argument cannot preserve the original \(F\) outside the edge at no cost: proving a freely localized replacement on this edge would already control the old smooth-cofactor discrepancy.

For example, in general low rows with macro-radical \(m\), if \(m=1\) then
\[
 G=2\sum_{q\mid n,\ q\ge x^\alpha}t_q-1;
\]
it reverses the old sign on the entirely \(x^\alpha\)-smooth class. If \(1<m\le D\), then
\[
 G=2\sum_{q\mid n,q<x^\alpha}t_q\sum_{d\mid m,dq>D}\mu(d).
\]
It vanishes when \(m\le D/x^\alpha\), and is nonpositive for a single eligible prime. But an open chamber with eligible exponents near \((.20,.22)\) and small exponents near \((.10,.11,.115,.12,.135)\) has \(F=0\) and \(G\approx1.16\), since each small factor crosses the pair only. A positive \(m>D\) chamber with eligible exponents near \((.190,.200,.240)\) and small exponents near \((.112,.123,.135)\) has \(F=1\) and \(G\approx2.48\): all eligible pairs are retained at \(D\) but none at \(D/q\). These are stable under sufficiently small changes of exponents at large fixed \(s\), and can occur with a genuine reflected prime across even targets by choosing that prime independently and setting \(N=n+p\). No control of the remaining broad low residual or unconditional proof of Goldbach is claimed.

For scope comparison, [Chan’s November 2026 preprint](https://aixiv.online/pdf/2611.00586) uses a different weight to tighten the prime-plus-semiprime alternative. [Jain, arXiv:2611.21136](https://arxiv.org/abs/2611.21136) studies progression distribution for smooth carriers, not the signed prime-reflected discrepancy for this carrier with a long label. Neither result is used to infer (50).
