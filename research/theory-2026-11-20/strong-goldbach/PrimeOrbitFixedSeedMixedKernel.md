# A fixed menu forces independent directions and additional mixed rows in its actual forward orbit

Fix a finite set \(F\) of primes and \(\delta>0\). Put \(N_F=\prod_{\ell\in F}\ell^{v_\ell(N)}\). For even \(N\) assume \(N_F\ge N^{1/2+\delta}\). In the directed factor graph \(z\to y\iff y\mid N-z\), start from a prescribed set \(S\) of \(s\ge1\) distinct odd primes coprime to \(N\), and let \(C\) be their full joint forward orbit (the union of the seed orbits). We call a row mixed if there are at least two distinct prime factors in its complete factorization, and pure if \(N-z\) is a prime power. There is no upper bound on \(|C|\).

**Theorem.** On \(S\) alone draw the actual arcs \(p_i\to p_j\) for \(p_j\mid N-p_i\), and let \(\alpha=\alpha(N,S)\) denote the maximum size of a subset inducing **no directed cycle**. For all sufficiently large \(N\), depending only on \(F,\delta,S\), either \(C\) reaches a genuine prime complement, or its number \(t\) of genuinely mixed rows satisfies
\[
                         t\ \ge\ s+\alpha+1.
\]
In particular \(t\ge s+2\), since there are no self-arcs, and \(t\ge 2s+1\) if the seed graph is acyclic. In the no-pair case each of the \(s\) seed rows is mixed, so at least \(\alpha+1\) mixed rows lie outside the named menu. For a single preassigned seed there is a genuine pair or at least three mixed rows even if its orbit is reducible. If all the seeds lie in one factor-closed strongly connected component, the theorem applies inside that component. It does not assert that the extra rows all occur in one terminal component in the reducible case or that every such orbit reaches a pair. In the proof we assume the orbit has no prime complement.

## Fixed seeds are mixed

We use the rational specialization of [Yu, *p-adic logarithmic forms and group varieties II*, (1.1), (1.8) and the bound just before (1.2)](https://matwbn.icm.edu.pl/ksiazki/aa/aa89/aa8944.pdf): at a fixed prime \(\ell\), for \(h\) nonzero rational \(\ell\)-unit bases, a nonzero form \(\prod a_i^{b_i}-1\) has valuation at most \(C_{h,\ell}\prod_i\max(1,h(a_i))\log(3+\max|b_i|)\), with \(h(a_i)\) their logarithmic heights. Constants here can absorb \(\log\ell\). The cited consequence preceding the auxiliary field conditions is valid in the rational specialization; alternatively extend to the fixed field containing the indicated roots of unity. We also use the [\(p\)-adic Subspace Theorem, Evertse, Theorem 11.1.2](https://pub.math.leidenuniv.nl/~evertsejh/Padicsubspace.pdf) in dimension two: fixed independent forms at each of finitely many places, on primitive integer vectors, with product bounded by a negative power of their sup-norm, allow only finitely many rational projective lines.

If a fixed \(p\in S\) were pure, \(N-p=y^e\), \(e\ge2\), for a prime \(y\ne p\). Apply Yu at every \(\ell\in F\) dividing \(N\) to \(y^e(-p)^{-1}-1=-N/p\); both bases are local units. It follows that
\[
 (1/2+\delta)\log N\le\log N_F\ll_{F,p}(\log y)\log(3+e)
       \le { \log N\over e}\,O_{F,p}(\log(3+e)).
\]
Thus \(e\) is bounded. On any alleged unbounded sequence fix \(e\). For each \(\ell\in F\) dividing \(N\), there is an algebraic root \(\beta_\ell\) of \(T^e+p\) in \(\overline{\mathbb Q}_\ell\) such that \(|y-\beta_\ell|_\ell\ll_{p,e,\ell}|N|_\ell\). Indeed the monic polynomial has distinct roots, and all except possibly the nearest are separated from \(y\) by at least the minimum distance between distinct roots. Fix the occurring subset of \(F\) and the finitely many root choices on a subsequence. For the primitive pair \((y,1)\) take coordinate forms at infinity and \((X-\beta_\ell Y,Y)\) locally. The product is \(O(y/N_F)\ll N^{-\delta}\), and \(y\le\sqrt N\) tends to infinity. The resulting finite rational lines cannot contain these different \((y,1)\). Thus every fixed seed row is genuinely mixed.

## Small inputs cannot feed a large pure predecessor of a fixed seed

Every label in this orbit satisfies \(z\le N/3\) for large \(N\): the initial fixed seeds do, and every later label occurs as a prime factor of an odd composite row whose cofactor is at least 3. Every label is a unit because a divisor of \(N-z\) is coprime to \(N\) when \(z\) is.

Suppose \(q\in S\) has a prime pure predecessor \(R\in C\) with \(N-R=q^a,\ a\ge2\). In particular \(q^a\ge 2N/3\) and \(a\to\infty\) at unbounded centers. For every fixed \(\eta>0\), eventually
\[
                              R>N_F N^{-\eta}.                       \tag{1}
\]
In fact \((q^a,R)\) is primitive. Use coordinate forms at infinity and at \(q\), and \((X+Y,Y)\) at all \(\ell\in F\) dividing \(N\) (these exclude \(q\)). The product is \(R/N_F\); if (1) failed it would be at most \(N^{-\eta}\) at height \(\le N\). A fixed rational projective ratio \(q^a/R\) is impossible on an unbounded sequence by the \(q\)-adic valuation \(a\) and \(R\ne q\). This proves (1) with the stated eventual quantifier.

Suppose a prime input \(z\in C\) feeds this \(R\), and let \(w=(N-z)/R\). Exactly
\[
                    w q^a-z=(w-1)N.
\]
Here \(w>1\), since \(w=1\) would give \(z=q^a\) nonprime, and \((z,w)=1\). The integral pair \((wq^a,z)\) is primitive if \(z\ne q\), and its gcd is exactly \(q\) if \(z=q\). In the latter case divide both coordinates by \(q\), a fixed factor. Use coordinate forms at infinity and at \(q\), and \((X-Y,Y)\) at primes of \(F\) dividing \(N\). The product is \(\le wz/N_F\) before scaling. The fixed scaling in the \(z=q\) case changes this by at most a fixed factor (the infinity and \(q\)-adic scaling actually cancel). The height is at most \(N^2\). A fixed rational ratio \(wq^a/z\) cannot occur along an unbounded sequence: its \(q\)-adic valuation is at least \(a-1\), since \(z\) is prime. For every fixed \(\eta>0\) the Subspace Theorem therefore gives \(wz>N_F N^{-\eta}\) eventually. Since \(w<N/R\), (1) yields, after using \(\eta/2\) in both bounds,
\[
                         z> N_F^2 N^{-1-\eta}                         \tag{2}
\]
for all sufficiently large centers. In particular none of the fixed seed primes can feed any such \(R\), and \(R>\sqrt N\) eventually. This argument covers moving \(z\) as well. In (1)–(2) the thresholds can be chosen uniformly over the finite prescribed seed choices: otherwise take an unbounded violating subsequence with that choice fixed.

## The free directions and the first-return matrix

Write \(k=|C|\), \(A_{ij}=v_{p_j}(N-p_i)\) on the full orbit, \(B=I-A\) and \(\nu=k-\operatorname{rank}_{\mathbb Q} B\). If \(t\ge2s+1\) there is nothing to prove, so assume \(t\le2s\). By the [short-interval count](PrimeOrbitCompulsoryBranching.md) there are \(O(L/(\log L)^2)\) pure inputs at most \(\sqrt N\). There are at most \(t\) labels above \(\sqrt N\): none is an initial fixed seed for large \(N\), each has an incoming actual edge, no pure composite power can have such a base, and each mixed complement supplies at most one such large target. Thus
\[
            k\ll {L\over(\log L)^2}+t,\qquad L=\log N.
\]
Every minor of \(B\), square of any size, thus has absolute value at most
\[
                H=(1+L/\log3)^k,\qquad \log(2H)\ll_s L/\log L       \tag{3}
\]
for large \(N\), by the row norm bound and Hadamard. This remains valid when the full determinant vanishes.

The coordinate vectors of the \(s\) fixed seeds are linearly independent modulo the rational row span of \(B\). To see this, if a relation exists then removing the \(S\)-columns strictly lowers the column rank: this is exactly the assertion that the row space contains a nonzero vector supported on \(S\). Select \(u\) basis columns outside \(S\) and one seed column extending them. Select \(u+1\) rows giving a nonzero \((u+1)\)-minor on those columns. Use the signed \(u\)-minors of the \(u\) basis columns on these rows for the coefficients of a row combination, via Laplace expansion (when \(u=0\) use coefficient 1). Its multiplier coordinates have size \(\le H\). The resulting vector \(c\) vanishes on all outside columns by their span, is nonzero on the chosen seed column, and has seed coordinates of size \(\le H\) because each is itself a \((u+1)\)-minor, possibly zero. All coefficients and the combination are integral.

Each actual row gives \(\prod_j [p_j]^{B_{ij}}=1\) modulo \(N\) up to sign. Hence \(\prod_{q\in S} q^{2c_q}-1\) has valuation at least \(v_\ell(N)\) at each \(\ell\mid N\). It is a nonzero rational number since \(c\ne0\) and these primes are distinct. All involved bases are fixed local units, so Yu gives \(\log N_F\ll_{F,S}\log(3+2H)=o(L)\), a contradiction. In particular \(\nu\ge s\), with actual independent directions, not just a dimension inferred from graph size.

Delete the outgoing arrows from mixed vertices. The remaining pure arrows have distinct targets: two different powers of one odd prime cannot both belong to \([2N/3,N)\). A directed cycle of pure rows here would be a genuine factor-closed nongoldbach terminal component by itself. This is impossible for our targets by [the all-size pure-component obstruction, (5)](PrimeOrbitCompulsoryBranching.md), since the fixed primes of \(F\) eventually lie below \(\sqrt{\log\log N}\) and \(N_F\ge N^{1/2+\delta}\). This is the one step where the earlier pure-component exclusion replaces strong connectivity. Consequently this subgraph is \(t\) disjoint simple chains (some can be singletons), each ending at a mixed vertex. Eliminate the pure coordinates in \(B\), or expand along these finite chains. The resulting effective matrix is \(I-M\) on the mixed vertices, where \(M_{ij}\) is the sum of the positive multiplicity products along all paths from mixed row \(i\) first returning to the mixed set at \(j\). The acyclic pure block has invertible \(I-A_{\rm pure,pure}\); hence \(\operatorname{nullity}(I-M)=\nu\). Every row sum of \(M\) is at least two, because every mixed row has at least two initial outputs and each continues to a mixed vertex with weight at least one. The reduced directed graph may be reducible; only its row sums are needed.

The submatrix \(M_{S,S}\) is **exactly** the direct-factoring submatrix \(A_{S,S}\). Indeed consider its column for a fixed \(q\). If its chain has no pure predecessor, all first returns there are direct. Otherwise the pure predecessor \(R\) supplied above is \(>\sqrt N\); it cannot itself have a pure predecessor since a composite pure power cannot have base \(>\sqrt N\). Thus the chain is just \(R\to q\), and (2) excludes every initial edge from a fixed seed to \(R\). This proves the equality including its zero diagonal.

Finally pick a subset of \(S\) of size \(\alpha\) inducing no directed cycle. Its \(M\)-block is acyclic by the just-proved equality. It cannot be all \(t\) vertices since \(M\) has no zero row. Eliminate this acyclic block once more. Every remaining effective row still has sum at least two: each original outgoing contribution either stays or its finite expansion across the acyclic deleted block reaches retained vertices with total positive multiplicity at least as large. The new matrix is therefore \(I-M'\) of positive dimension \(t-\alpha\) and is **not** identically zero, so \(\nu\le t-\alpha-1\). Together with \(\nu\ge s\) this proves the theorem.

Inside a **strongly connected no-pair terminal** with \(s=1,t=2\), one can also read the last obstruction directly: the irreducible two-by-two \(M\) would have \((M_{11}-1)(M_{22}-1)=M_{12}M_{21}>0\). Its only possibility with both diagonals below one is zero diagonals, unit off-diagonals, contrary to both row sums being at least two. Otherwise both diagonals are at least two, contrary to the zero diagonal for the fixed seed. This special case is not an assertion that Perron growth excludes eigenvalue one in general.