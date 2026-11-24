# Two-level exact small-factor profiles at powers of two

This is an unconditional dichotomy about actual factors of \(N-p\) and their complements. It uses [the square-root-window P4 theorem with prescribed local profiles](PrimeOppositeSquareRootPlantedP4.md), with the notation \(B_0\) of that theorem. It neither forces the high-factor branch nor proves a prime pair.

Fix \(c>0\) and \(0<a<b<1\), set \(N=2^k\), \(L=\log N\), and \(Y=\log L\). Let \(D\) be the set of odd primes \(\ell\le cY\), \(d=\prod_{\ell\in D}\ell\), and let
\[
 V=\{v\text{ prime}:2cY<v\le5cY,\ v\nmid d-1\},\qquad v_0=\prod_{v\in V}v,\qquad m=d\,v_0^2.
\]
The PNT gives \(\log d=(c+o(1))Y\), \(\log v_0\le (3c+o(1))Y\), and \(|V|\ge (2c+o(1))Y/\log Y\). For the last bound, the interval has \((3c+o(1))Y/\log Y\) primes, and at most \(\log(d-1)/\log(2cY)\le(c+o(1))Y/\log Y\) can divide \(d-1\). In particular \(|V|\to\infty\) and \(dm\le L^{8c+o(1)}\).

Use a single CRT class \(r\) with
\[
 r\equiv-N\bmod\ell\quad(\ell\in D),\qquad
 r\equiv N-v\bmod v^2\quad(v\in V).
\]
It is a unit modulo \(m\), since all these primes are odd and \(N=2^k\). At \(\ell\in D\), \(N-dr\equiv N\not\equiv0\bmod\ell\). At \(v\in V\), \(N-dr\equiv(1-d)N\not\equiv0\bmod v\) by definition. Thus the source progression modulo \(dm\) is reduced. Fix any \(A>8c\) and apply the planted-profile theorem. We obtain \(\gg B_0\) real prime-root rows \(p\in(aH,bH]\) whose true complement contains every \(\ell\in D\) with valuation one, none of \(V\), and a squarefree \(Q=(N-p)/d\) of rank one to four, with all its prime factors at least \(z=N^{.05}\). Rank zero is impossible because \(Q\asymp N/d\to\infty\). Every starting row is itself composite, since the first dictionary is nonempty and \(Q>1\).

Partition these genuinely occurring rows according as \(Q\) has a prime factor at most \(H\) or not.

* If at least half have a low factor in \(Q\), there are \(\gg z/L^2\) distinct actual low labels \(\ell'\in[z,H]\) in these first layers. For a fixed \(\ell'\) and each root containing it, \(\ell'\not\mid dm\) for large \(N\) because \(\ell'\ge z\); \(p\) lies in the fixed reduced class modulo \(dm\) and also \(p\equiv N\bmod\ell'\). Its multiplicity is therefore \(O(H/(dm z)+1)=O(H/(dm z))\), uniformly since \(dm\) is polylogarithmic. Dividing the lower \(\gg B_0 \gg H S_1/(\phi(dm)L^2)\) by this multiplicity gives \(\gg z\,S_1\,dm/(\phi(dm)L^2)\gg z/L^2\). This counts the first layers of these actual roots, not necessarily vertices of any single root's orbit.

* Otherwise at least half have no low factor in \(Q\). Because \(Q<N=H^2\), \(Q\) must be one actual high prime \(q>H\). The many such \(q\) are distinct: any two parents give \(p\equiv N\bmod q\), but both parents are in a window below \(H<q\), so they coincide. At every such high vertex the true row \(N-q\) has **none** of the first dictionary \(D\), since \(q\equiv-N\bmod\ell\) entails \(N-q\equiv2N\not\equiv0\bmod\ell\). It has **every** prime \(v\in V\) to exact valuation one, since \(q\equiv N-v\bmod v^2\). Thus these genuine high rows give an entire, new and disjoint controlled low dictionary at depth two; they are truly composite at large \(N\), because \(|V|\ge2\). There is no need to assume a no-prime-pair target. Any further high successor of such a \(q\)-row is at most \(N/v_0\), because all factors in \(V\) occur in that row and are different from the high successor. This last bound does not assert that there is a further high successor.

Thus either the common planted source set already creates many distinct mesoscopic low children, or it creates many distinct high children whose true second rows necessarily exit the first small dictionary in a fully prescribed exact way. This is stronger than a statement about first-step markers alone, but it does not force the high branch, provide a bound on total reachable labels from one root, put the controlled second rows in a prescribed SCC, or prove Goldbach. 
