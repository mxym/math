# Extreme imbalance in the raw complementary Vaughan partition

Addendum to [the same raw identity](Proof.md). Retain its \(N,J_0,J,I,S,z,V=\exp((\log\log N)^3),T_y,Q_y(m)\) and (1), with no small-radical restriction. Use the unchanged actual rough/unit masks. Write \(x=ab,\ y=mcv=N-x\). At arbitrary fixed logarithmic precision, the **whole raw** part of the product complement
\[
                       a(mc)>N/V^3                                  \tag{1}
\]
may be deleted if either
\[
 a\le N^{1/6-\eta}
 \qquad\hbox{or}\qquad
 mc\le N^{1/3-\eta}                                                   \tag{2}
\]
for any fixed \(\eta>0\). The two sets cannot intersect on (1) for large \(N\). More generally, in raw dyads \(a\asymp N^\alpha,\ c\asymp N^\gamma,\ m\asymp N^\beta\), a whole box is negligible if
\[
       \alpha<\gamma/2
       \qquad\hbox{or}\qquad
       \beta+\gamma<\alpha/2,                                       \tag{3}
\]
with fixed positive slack, subject to the corresponding Möbius source being polynomial-sized. Enforcing (1) is not necessary for the dyadic formulation (3). The active arithmetic progressions use genuine \(\mu\), not prime support of the opened slots. Inner or overlapping angular pieces are not new additive credits against the long-label expansion.

## Weighted maximal input and endpoint conventions

Use the true unit-masked maximal Möbius B--V estimate (2) in [SecondTypeI.md](../reverse_giant_typeI/SecondTypeI.md), including its extension to a mask \(H\le N^{O(1)}\) via convolution over integers supported on the primes of \(H\). The proof there permits this extension: the two Euler-product bounds use only \(\log H=O(\log N)\), with exactly the same split. If \(X\ge N^\delta\), \(q\le X^{1/2-\delta'}\) for fixed \(\delta,\delta'>0\) and \((q,H)=1\), the estimate gives an arbitrary fixed logarithmic saving, summed over \(q\), for the maximum over reduced residues and all real prefixes at length \(X\).

The same estimate can carry \(L^{C_1}\tau(q)^{C_2}\) as an absolute weight, where \(C_1,C_2\) are fixed. To see this, clip \(\tau(q)\) at \(L^K\), use the stronger requested unweighted estimate on the clipped part, and on the rest use the true floor bound \(O(X/q+1)=O(X/q)\) and
\[
 \sum_{q\le X^{1/2}}\frac{\tau(q)^{C_2}1_{\tau(q)>L^K}}q
 \ll L^{-K}\sum_{q\le X^{1/2}}\frac{\tau(q)^{C_2+1}}q
 \ll L^{-K+O_{C_2}(1)}.
\]
All cuts used below at fixed outer variables are intervals in the active Möbius variable. Moving \(d<T_y=y/B\) is retained by opening \(d\mid m\) and using the literal inequality \(y>Bd\). The central \(\log\)-weights have supremum and total variation \(O_{J_0}(L)\) in that variable. Thus maximal B--V and ordinary partial summation suffice; no independent restriction on \(d<T_y\) or uniform prime count above root is being substituted.

When opening a \(z\)-roughness mask, use the same successive Bonferroni truncations as the main raw proof. All label products are \(V^{o(1)}\) and their absolute reciprocal sums cost fixed log powers. Any omitted sieve label divides the actual \(x\) or \(y\); the weighted error is paid globally by \(N\sum_e1/e\), Cauchy, and the physical fixed divisor moments. This applies to several presieves by telescoping their product, since every truncated assignment is contained in the same fixed divisor-power envelope. No error is multiplied by the raw cardinality of the short prescribed labels after invoking the arithmetic progression estimate.

## Active \(\mu(c)\): small \(a\), including arbitrarily supercritical product

Fix the actual \(m,v\). Keep \(\lambda_{>V}(v)\), its \(z\)-roughness and unit conditions as given, and open only the left \(\lambda_{>V}(b)\) by \(\log b\) or \(b=f G_0,\ f\le V\) with actual coefficient \(-\Lambda(f)\). In the log choice put \(f=1\). In each term \(a,f\) are \(z\)-rough, and \(G_0\) is \(z\)-rough. Open the latter by \(e\mid G_0\), and the \(c\)-roughness by \(d_0\mid c\). The actual modulus is \(q=a f e\), since \(q\mid x=N-m v c\). All raw variables except \(c\) and the remaining free \(G\) are now fixed. If \((q,mv)>1\) or \((q,d_0)>1\), then the class is impossible under target units. Otherwise put \(c=d_0 u\). Since \(d_0\) is squarefree,
\[
 \mu(c)=\mu(d_0)\mu(u)\,1_{(u,d_0)=1},\qquad
 u\equiv N\overline{m v d_0}\pmod q .
\]
The mask is precisely \((u,N d_0)=1\); \(N d_0\) is a unit modulo \(q\). No coprimality of \(f\) and \(a\) is imposed or needed. If \(f=1\), the optional log is \(\log((N-m v c)/a)\), in its actual interval.

For \(X=N/(mv)\), allowable \(c\) is comparable to \(X\) by centrality. Condition (1) and \(m\le \sqrt N/S^2\), \(a\le N^{1/6-\eta}\), imply
\[
 c>N^{1/3+\eta}S^2/V^3,\qquad
 q\le N^{1/6-\eta} V^{1+o(1)} .
\]
Since \(d_0=V^{o(1)}\), this is within a fixed power below the square root of \(X/d_0\). In (3)'s first branch the reserve follows directly from \(\alpha<\gamma/2\). At an actual \(q\), \(e\) is recovered as its smooth part; for each \(f\mid q/e\) the value of \(a=q/(fe)\) is forced. With \(\sum_{f\mid q}\Lambda(f)\le\log q\), the two choices carry only log powers even if their maximum-prefix endpoints differ. The \(c>V\) and \(c v\in I\) cuts, the raw inequalities, and the \(d\mid m\) threshold all give literal real endpoints after fixing these labels. Apply weighted maximal B--V at length \(X/d_0\). Sum \(d_0\) by its reciprocal harmonic and the remaining \(d,m,v\) in the absolute harmonic \(\sum_{m,v}\tau(m)\lambda_{>V}(v)/(m v)\ll L^{O(1)}\). This pays the entire raw first orientation.

## Active \(\mu(a)\): small \(mc\), for arbitrary factorization of \(m\)

Fix the actual \(b\), retaining its independent rough/unit masks and \(\lambda_{>V}(b)\). Open the right \(\lambda_{>V}(v)\) by \(\log v\) or \(v=t K_0\), \(t\le V\) with coefficient \(-\Lambda(t)\), assigning \(t=1\) in the log choice. Open \(K_0\)-roughness by \(e\mid K_0\), and \(a\)-roughness by \(d_0\mid a\). The real modulus \(q=m c t e\) divides \(y=N-ba\). The presence of \(m\) does not assert that any of its factors are \(z\)-rough or coprime to other factors of \(q\). For unit-compatible \(q\) and labels \((q,b d_0)=1\), put \(a=d_0 u\). The active sum has \(\mu(u)1_{(u,N d_0)=1}\) in the actual reduced class \(N\overline{b d_0}\bmod q\), with the exterior sign \(\mu(d_0)\). If \(t=1\), its only optional log is \(\log((N-b a)/(mc))\).

Now \(X=N/b\) is comparable to \(a\). On (1) and \(mc\le N^{1/3-\eta}\),
\[
 a>N^{2/3+\eta}/V^3,\qquad q\le N^{1/3-\eta} V^{1+o(1)},
\]
giving the same strict square-root reserve; for the second branch of (3) use \(\beta+\gamma<\alpha/2\). At fixed \(q\), the number of factorizations \(m c t e=q\) and of additional \(d\mid m\) labels is at most a fixed divisor power, and all remaining weights, including \(\Lambda(t)\) and the variation in the source log, cost fixed log powers. At each allowed factorization the \(m\) restriction \(y/m\in I\), the actual \(d<T_y\) and all raw cuts only impose endpoints in \(u\), so weighted maximal B--V pays arbitrary log precision at \(X/d_0\) without any uniformity assumption on the separate factorizations. Sum \(d_0\) by its reciprocal harmonic and \(b\) against \(\sum_b\lambda_{>V}(b)/b\ll L^2\). This proves the two orientations and their fixed-margin dyadic formulations.

These are estimates for the actual signed raw expanded remainder. They leave a true middle open: for a subpower \(m\), even with the original reciprocal region additionally removed, there are raw product-supercritical boxes with \(1/2\le\alpha/\gamma\le 2\). Neither this proof nor a unilateral distribution of \(\mu\) forces a singular-series comparison on those boxes.
