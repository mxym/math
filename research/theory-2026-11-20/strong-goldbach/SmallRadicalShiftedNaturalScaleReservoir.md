# Natural-scale favorable shifted high-term rows, including the actual translated cover

This extends [the genuine semiprime reservoir](SmallRadicalSemiprimeNearFullPositive.md), using its checked genuine-prime centered coefficient and reflected comparison unchanged. The no-cover theorem is independent of the upper sieve below.

## Statement

Let \(P\) be large prescribed even, \(L=\log P\), \(\operatorname{rad}(P)\le L^B\), \(I=PJ\) for fixed nondegenerate compact interval \(J\subset(0,1)\), and \(0<\delta<.1\). Put \(y=e^{L^\delta}\), \(z=e^{L^{.24}}\), \(V_y(P)=\prod_{\ell\le y,\,\ell\nmid P}(1-1/(\ell-1))\asymp S(P)/L^\delta\). Fix a full admissible base packet family \(\mathcal T\) with a sufficiently large fixed **even** \(K\), and reciprocal mass \(\mathcal V=\sum_{u\in\mathcal T}u^{-1}\asymp_K1\). Base tags are distinct-prime products of one prime from each of the \(K\) bands in the verified fixed-family projection; every prime in these bands is \(>y\) and \(<z\).

There are \(\gg P S(P)/L^{1+\delta}\) pairwise distinct \(n\in I\) with genuine
\[
n=pq,\qquad m=P-n=u v r,\qquad P^{.32}\le p\le P^{.35},\quad p<q,\quad u\in\mathcal T,
\]
where \(p,q,r\) are primes, \(r>P^{.8}\), \(v\le P^{.1}\) is squarefree of even rank with all primes in \((y,P^c]\), and no prime factor of \(v\) is in any of the \(K\) full base bands. One can take sufficiently small fixed \(c>0\); \(v=1\) is allowed. Both \(n,m\) are squarefree, \(P^-(m)>y\), and \(\lambda(m)=-1\). Thus each row has \(T(n)\lambda(m)=+\log n\), where \(T\) is the actual smooth high source coefficient, and the total favorable mass is \(\gg P V_y(P)\).

The same assertions hold with the rows required to pass the **actual** translated cover across any fixed number \(M\ge2\) of offsets \(j=2,\dots,M+1\) (and fixed admissible order parameter \(K_{\rm cov}\)). The lost positive weight is \(O(PV_y(P)L^{-M/200})\). By the exact selector partition on the real shifted numbers \(jP-n\), this surviving positive weight is present at full weight in the original marked high budget. The base tag \(u\mid m\) is only a counting device here and is **not** identified with the proof's covering tags \(u'\mid jP-n\). No lower bound on the net signed budget follows.

## 1. An even, small, rough cofactor library with power-log reciprocal mass

Write \(\mathcal P\) for primes in \((y,P^c]\) outside the entire \(K\) base bands. Then
\[
\sum_{\ell\in\mathcal P}1/\ell=(1-\delta)\log L+O_{c,K}(1),\qquad
Z_{\mathcal P}:=\prod_{\ell\in\mathcal P}(1+1/\ell)\asymp_{c,K} L^{1-\delta}.
\]
Mertens gives the first formula before band removal, and the total reciprocal mass in the fixed complete bands is \(O(K)\). Normalize the reciprocal weights on squarefree products of \(\mathcal P\) by \(Z_{\mathcal P}\). Their primes are then included independently with probability \(1/(\ell+1)\). The mean log size is \(\ll cL\) by \(\sum_{\ell\le X}(\log\ell)/\ell\ll\log X\). Fix \(c\) small enough that the probability of \(\log v>.1L\) is at most \(1/8\). Meanwhile the mean parity is
\[
\prod_{\ell\in\mathcal P}\left(1-\frac{2}{\ell+1}\right)=o(1),
\]
so the even ranks have weight \((1/2+o(1))Z_{\mathcal P}\). Imposing both even rank and \(v\le P^{.1}\) retains a positive fraction. The resulting set \(\mathcal A\) therefore satisfies
\[
D_{\mathcal A}:=\sum_{v\in\mathcal A}v^{-1}\asymp_{c,K} L^{1-\delta}.
\tag{1}
\]

## 2. Genuine prime count of the whole library before imposing the translated cover

Take the same \(\asymp_J L\) disjoint short-coordinate rectangles as in the verified earlier theorem: \(I_1\subset[P^{.32},P^{.35}]\), \(I_2\asymp P/I_1\), each relative width a fixed small constant, \(I_1 I_2\subset I\) and area \(\asymp_J P\). Endpoints of the short intervals can be half-open to avoid repeated boundary points. Set \(w(t)=1_{t\ {\rm prime}}\log t\) and \(\kappa_z=\prod_{\ell\le z}(1-1/\ell)\).

For \(1\le h\le P\), let \(b(h)=w(r)/L\) when \(h=v r\) with \(v\in\mathcal A\) and true prime \(r>P^{.8}\), and zero otherwise; set it zero beyond \(P\). The factor \(r\) is unique because two such prime factors cannot occur in an integer \(\le P\). Thus \(b\) is one bounded function of \(h\) alone even though its cofactor library grows. In the actual equation \(P-xq=u h\), \(r\gg_J P/(uv)=P^{.9-o(1)}>P^{.8}\) on this library. The genuine log triple sum can be written with residual \(L b(h)\).

Apply the already proved centered-prime estimate \(\alpha=w-\kappa_z^{-1}R_z\) and the full-target reflected comparison twice, once to \(x\) and once to \(q\). No new character statement or \(u\)-dependent test occurs: the only replacement in the proof is of \(w(h)/L\) by the bounded \(b(h)\), which does not involve \(u\). The combined replacement error is \(O_A(PL^{-A})\) per rectangle with sufficiently large fixed \(K\) (one fixed large \(A\) suffices here). **This error is not multiplied by a count of \(v\)'s**, since the single \(b\) already contains all \(v\)'s. The last prime \(r\) is not replaced.

For the Type I evaluation after both replacements, fix \(a_0=uv\) and an integer \(x\in I_1\) with \(P^-(x)>z\). **It is not automatic that \((x,a_0)=1\): a prime factor \(>z\) of \(v\) may divide \(x\).** But an actual solution forces \((x,a_0)=1\), since a shared prime would divide \(P\), whereas every prime of \(a_0\) exceeds \(y>\operatorname{rad}(P)\) for large \(P\). In the model restrict \(x\) accordingly. Removing the rough \(x\)'s divisible by any prime of \(v\) above \(z\) costs uniformly
\[
\sum_{\substack{\ell\mid v\\\ell>z}}\left(O_J(X_1/\ell)+O(1)\right)
 \ll X_1 L/z+L,
\]
where \(X_1\) is the short-coordinate scale. This remains negligible compared to \(\kappa_z |I_1|\) in **each** rectangle. The bound uses \(\omega(v)\le L/\log 2\), needs no independence, and has no floor multiplication beyond the displayed \(L\). Also \((x,P)=1\) and \(x/\varphi(x)=1+O(L/z)\) uniformly.

The interval for the last prime is \([(P-xq_+)/a_0,(P-xq_-)/a_0]\) of length \(x|I_2|/a_0\). In the rough test on \(q=(P-a_0r)/x\), primes \(\ell\le z\) dividing \(a_0\) cannot divide \(q\) (as \(\ell\nmid P\)); primes dividing \(P\) cannot divide \(q\) either (as \(r>z\) is prime and \((a_0,P)=1\)). For other small primes, opening \(q\)-roughness with a squarefree \(d\) gives the reduced progression \(r\equiv P a_0^{-1}\bmod xd\), with \(x,d\) recovered uniquely from opposite prime ranges. Use upper/lower Bonferroni depth \(C_A\log L\), then ordinary maximal prime Bombieri–Vinogradov at the **actual** endpoint \(P/a_0\ge P^{.9-o(1)}\). All moduli \(xd\le P^{.35+o(1)}<\sqrt{P/a_0}/\log^{C}(P/a_0)\) for any fixed \(C\) needed in BV. Both endpoints vary, within the maximal range. The summed BV error before \(a_0\)-summation is \(O_A((P/a_0)L^{-A})\): for each fixed \(a_0\) the assignment of \((x,d)\) to the modulus remains injective, and the reciprocal Bonferroni remainder is made arbitrarily log-small by increasing \(C_A\). Separating \(\varphi(xd)\) in the model gives, before the outer \(\kappa_z^{-2}\), the main term
\[
\frac{|I_2|}{a_0}
 \prod_{\substack{\ell\le z\\\ell\nmid Pa_0}}\left(1-\frac1{\ell-1}\right)
 \sum_{\substack{x\in I_1,\,P^-(x)>z\\(x,a_0)=1}}\frac{x}{\varphi(x)}.
\]
The last sum is \(\kappa_z |I_1|+O_A(X_1L^{-A})\) uniformly in \(u,v\) by pure-integer rough counting and the explicit shared-prime exclusion. The local factor after normalization is
\[
\kappa_z^{-1}\prod_{\substack{\ell\le z\\\ell\nmid Pa_0}}\left(1-\frac1{\ell-1}\right)
=S(P)\bigl(1+O(L/y+1/z)\bigr),
\]
by the usual prime-by-prime product and \(\sum_{\ell\mid a_0}1/\ell\ll L/y\). This is uniform even if \(v\) has many factors. The remaining errors sum using \(\sum_{u,v}1/(uv)=\mathcal V D_{\mathcal A}\); fixed log losses are covered by requesting a larger \(A\).

Consequently the genuine log triple weight per rectangle is
\[
|I_1||I_2|\,\mathcal V D_{\mathcal A} S(P)(1+o(1)).
\tag{2}
\]
The rectangles give total \(\asymp P S(P)L^{2-\delta}\). Since all \(p,q,r\) are polynomial in \(P\), each log triple product is \(\asymp L^3\); and \(\log(pq)\asymp_J L\). There is no multiplicity: the true smaller prime \(p\) determines its box and then \(q\); \(m\) has a unique prime \(r>P^{.8}\); in \(m/r=uv\) the primes from the full base bands determine \(u\) uniquely because \(v\) is disjoint from those bands, and \(v\) is then fixed. Rank \(K+\omega(v)+1\) is odd. Both \(p,q>P^{1/4}\), so the checked smooth source formula gives \(T(pq)=-\log(pq)\). This proves the no-cover assertion.

## 3. A genuine two-affine upper sieve removes uncovered rows

Use exactly the translated packet grid and greedy witness in [the earlier multi-offset note](SmallRadicalTranslatedTagTypeI.md): each offset with no admissible cover has occupied centres in \(\le K_{\rm cov}-1\) rightward short intervals of width \(1/(20K_{\rm cov})\) on the grid with spacing \(h_0=\log 4/\log L\), so at least \(.04/h_0-O(K_{\rm cov})\) packets at that offset are forced empty. For a fixed choice of these short intervals at every offset let \(t_i\) be the number of offsets forced empty at packet \(i\). Thus \(\sum_i t_i\ge M(.04/h_0-O(K_{\rm cov}))\) and there are at most \(O_{M,K_{\rm cov}}((\log L)^{M(K_{\rm cov}-1)})\) short-interval choices.

Fix **genuine** short prime \(p\) and actual \(u,v\), with \(a_0=uv\). Then \((p,a_0)=1\) (even \(v\)'s largest permitted prime is \(<p\)). On the same lattice of physical solutions,
\[
q=q_0-a_0 k,\qquad r=r_0+p k,\qquad p q+a_0r=P .
\]
The \(k\)-interval is finite of length \(O_J(P/(p a_0))\). Take sieve divisor level \(D=P^{1/40}\) and sieving primes up to \(W=D^\rho\), where \(\rho>0\) is sufficiently small fixed depending only on \(M\). All packet primes lie below \(W\) for large \(P\), while both actual prime slots \(q,r\) exceed \(W\).

At \(\ell\le W\) the short \(p\) is a unit. If \(\ell\mid a_0\), then \(q\equiv P/p\ne0\bmod\ell\), and there is one \(r\)-root. If also \(\ell\) belongs to a translated packet, all its forced emptiness tests already hold, since \(jP-n=a_0r+(j-1)P\) and \(\ell>M+1\), \(\ell\nmid P\). If \(\ell\nmid a_0\), parameterize its residues by \(a_0 r\). The usual two bad residues are \(0,P\), coinciding iff \(\ell\mid P\). A packet prime does not divide \(P\); for it the other \(t_i\) forbidden residues are \(-(j-1)P\) at the prescribed offsets, all mutually distinct and disjoint from \(0,P\), since \(\ell>M+1\). Thus the genuine density is \(\nu(\ell)/\ell\) with \(1\le\nu(\ell)\le M+2\) and \(\nu(\ell)<\ell\). At each packet prime not dividing \(a_0\) the density of good residues relative to baseline is
\[
(1-(2+t_i)/\ell)/(1-2/\ell)
=1-t_i/(\ell-2)\le e^{-t_i/\ell}.
\]
Dropping packet primes of \(a_0\), and adjusting the baseline at those primes, costs only a factor \(\exp(O_M(L/y))\) by \(\sum_{\ell\mid a_0}1/\ell\ll L/y\). This treats even those primes of \(v\) that happen to lie in the *translated* packet grid; excluding the \(K\) base bands alone would not justify discarding them. By the reciprocal packet mass, the product of baseline and packet local densities is therefore
\[
\ll \frac{S(P)}{L^2}\exp\bigl(-\tfrac14\sum_i t_i\bigr).
\tag{3}
\]
Here the baseline product without \(a_0\) is \(\prod_{\ell\le W}(1-(2-1_{\ell\mid P})/\ell)\asymp S(P)/(\log W)^2\): divide by the square of the Mertens product to recover the usual singular factors exactly up to the absolutely convergent tail. All target primes are below \(W\).

For clarity the elementary fixed-dimension Selberg upper bound for this actual lattice can be obtained as follows. For squarefree \(d\) supported on primes \(\le W\), put \(g(d)=\prod_{\ell\mid d}\nu(\ell)/\ell\) and \(h(d)=\prod_{\ell\mid d}g(\ell)/(1-g(\ell))\). The interval count in the \(d\)-bad set is its length times \(g(d)\) plus \(O(\nu(d))\) by CRT. For \(\lambda_1=1\), the square of the sum of weights \(\lambda_d\) over bad \(d\le D\) majorizes the fully surviving indicator. The main quadratic form is \(\sum_{r\le D} h(r)^{-1}(\sum_{r\mid d}\lambda_d g(d))^2\) by expanding \(1/g((d,e))\). Choosing the inner sums equal to \(\mu(r)h(r)/G(D)\), where \(G(D)=\sum_{r\le D}h(r)\) on the same support, makes the form \(1/G(D)\) and gives \(\lambda_1=1\). Inverting gives
\[
\lambda_d=\frac{\mu(d)}{G(D)}\prod_{\ell\mid d}(1-g(\ell))^{-1}
   \sum_{\substack{j\le D/d\\(j,d)=1}}h(j),\qquad |\lambda_d|\le1.
\]
The last bound follows by supplementing each \(j\le D/d\) with every divisor of \(d\) in the full sum \(G(D)\). Thus the total remainder is \(O(D^4)\), using at most \(D^2\) pairs and \(\nu([d,e])\le[d,e]\le D^2\); the weaker \(O(D^6)\) is ample. Under the normalization of the full (untruncated) product of \(h\)'s, include each prime independently with probability \(g(\ell)\). Its expected \(\log d\) is at most \((M+2)\sum_{\ell\le W}(\log\ell)/\ell\le C(M+2)\rho\log D\). Choose \(\rho\) such that Markov shows at least half the mass at \(d\le D\). Therefore \(1/G(D)\le2\prod_{\ell\le W}(1-g(\ell))\), proving the upper sieve with (3) for every witness.

Summing the witnesses gives \(L^{-M/200}\) times the ordinary sieve main because \(.04/(4\log4)>1/200\), with a true fixed margin absorbing the fixed power of \(\log L\). Therefore, for fixed \(p,u,v\), the number of true uncovered \(q,r\) solutions is bounded by
\[
\ll \frac{P S(P)}{p u v L^2}L^{-M/200}+P^{.15+o(1)}.
\]
Multiplying by the three actual log weights and summing in the rectangle, we get at most
\[
\ll P S(P)\mathcal V D_{\mathcal A}L^{-M/200}+P^{.60+o(1)} .
\tag{4}
\]
For the main, bound \((\log q)(\log r)\le L^2\) and use \(\sum_{p\in I_1}(\log p)/p=O(1)\). For the floor, count independently \(\#p\le P^{.35}\), \(\#u=P^{o(1)}\), \(\#v\le P^{.1}\), and absorb the log weights. All these errors remain negligible under the \(O(L)\) rectangles. Converting log triple weight to the actual positive source weight uses the uniform \(O(L^{-2})\) ratio \(\log(pq)/((\log p)(\log q)(\log r))\), proving the \(O(PV_y(P)L^{-M/200})\) loss in the statement.

The no-cover lower bound and this upper sieve operate on the **same genuine** rows; the sieve never assigns a prime status to an individual model row. Since the selector sums to one on each truly covered \(n\), (2)–(4) show the full marked budget really has a favorable piece of size \(\gg P V_y(P)\). Even taking \(M>200\), so the loss is \(o(PV_y(P)/L)\), does not bound any adverse piece or justify comparing unrelated lower/upper constants. The higher translated residual remains outside the one-variable reflected comparison.
