# Independent moving prime directions at every center with a large fixed-prime part

For \(N\) even, write \(L=\log N\) and \(N_F=\prod_{\ell\in F}\ell^{v_\ell N}\), for a fixed finite prime set \(F\). Fix \(\delta>0\) and \(0<\eta<1\). Assume \(N_F\ge N^\delta\), with **no square-root threshold**. Arcs are \(z\to y\) when \(y\) divides \(N-z\), weighted by its actual valuation. A mixed row has at least two distinct complementary prime factors. For a factor-closed, no-pair forward orbit with exponent matrix \(A\) on its prime labels, a prime's *direction* is its coordinate vector modulo the rational row space of \(I-A\). This is a linear invariant of its real integer prime factorizations; it is not the abstract generator rank of the finite unit group.

**Theorem.** There is \(c>0\) depending at most on the fixed parameters such that, at every sufficiently large such \(N\), there is a single unit prime
\[
 x\le\exp\!\left(O_{F,\delta,\eta}\!\left({(\log L)^2\over\log\log L}\right)\right)
\]
with \(s=\lfloor c\log L/\log\log L\rfloor\) specified distinct unit prime successors \(q_i\in[L,4L]\), all of exact multiplicity one. One of the following holds:

1. The actual forward orbit of \(x\) reaches a genuine prime complement.
2. It contains at least \(L^{1-\eta}\) genuinely mixed rows.
3. The directions of the \(s\) moving successors are linearly independent over \(\mathbb Q\) in that same orbit. In fact \(x\) itself adds another independent direction, and the number of mixed rows is at least \(s+2\).

Thus in the absence of a reachable pair the number of genuinely mixed rows diverges with an explicit rate, without a uniformity assumption on an earlier fixed-seed theorem. The root and the displayed fan are allowed to depend on \(N\). Independence or the branch count need not hold inside any single terminal component of a reducible orbit.

If every prime factor of \(N\) belongs to \(F\), then for **any prescribed \(\epsilon>0\)** the root can instead be required to satisfy \(x\le L^\epsilon=(\log N)^\epsilon\), retaining \(s\gg_{F,\epsilon,\eta}\log L/\log\log L\) and the same conclusions. Here use \(s\) small odd primes outside \(F\) of size \(O_F(s\log(2s))\) (rather than \(q_i\in[L,4L]\)).

## The root and the sharp minor-height input

Use the [one-root construction](PrimeOrbitSingleRootPacking.md) on the selected \(s\) unit primes in \([L,4L]\); there are \(\gg L/\log L\) available even after omitting divisors of \(N\), by the prime number theorem and \(\sum_{q\mid N}\log q\le L\). Set \(W=\prod q_i\) and impose \(x\equiv N-W\bmod W^2\), with \(x\) odd. This is reduced and gives all \(v_{q_i}(N-x)=1\). Use a further prime \(b\in[L^2,2L^2]\) with the \(b-1\) different nonzero classes for \(x\) modulo \(b\). [Linnik's theorem](https://www.impan.pl/shop/publication/transaction/download/product/83078) gives \(b-1\) distinct primes \(x\ll(2bW^2)^\lambda\) for an absolute \(\lambda\); discard divisors of \(N\) and primes \(\le4L\) as before. Since \(\log W\le s\log(4L)\), the asserted bound follows. In the \(F\)-smooth variant choose the first \(s\) odd primes outside \(F\); then \(\log W\ll_F s\log(2s)\). Instead of the auxiliary \(b\), impose \(x\equiv1\bmod\prod_{\ell\in F}\ell\) and odd parity consistently. Linnik gives \(\log x\ll_F 1+s\log(2s)\); reduce \(c\) depending on \(\epsilon\). The root cannot be one of its \(q_i\) since its class is a unit modulo \(W\).

Assume no true pair is reached. Every label is a unit prime \(\le N/3\) for large \(N\): the root is \(N^{o(1)}\) and every descendant divides an odd composite complement. We use [Stewart, *On heights of multiplicatively dependent algebraic numbers*, Theorem 2, \(k=2,\theta=1/2\)](https://uwaterloo.ca/pure-mathematics/sites/default/files/uploads/documents/aa133-2-01.pdf). It gives, for some absolute \(C\), at most
\[
         V(L)=\exp\big(C\sqrt{\log L\cdot\log\log L}\big)=L^{o(1)}
\]
integer perfect powers in the whole interval \([N-\sqrt N,N]\). Indeed cover it by two intervals of the theorem's type \([u,u+\sqrt u]\), with \(u_1=\lfloor N-\sqrt N\rfloor\), \(u_2=u_1+\lfloor\sqrt{u_1}\rfloor\); both starts are asymptotic to \(N\), and the height of an integer in those intervals is \(\le2u\). This primary theorem is an external improvement on the elementary short-interval count in [the branching note](PrimeOrbitCompulsoryBranching.md), not a new short-interval perfect-power bound.

Writing \(t\) for the number of mixed rows and \(k\) for the number of labels in the no-pair orbit, there are at most \(V(L)\) pure inputs \(\le\sqrt N\) by Stewart. A label \(>\sqrt N\) must have an incoming arc (it is not the root); its predecessor must be mixed and one row cannot produce two such large primes. Hence
\[
 k\le V(L)+2t,\qquad \log(2H_*)\ll(V(L)+t)\log L,\qquad
 H_*=(1+L/\log3)^k.                                              \tag{1}
\]
Hadamard bounds every square minor of \(I-A\) by \(H_*\), not only its full determinant.

## Uniformity in the number of directions

Suppose that some nontrivial dependence among the coordinates of \(x,q_1,\ldots,q_s\) holds in the rational row quotient. By the [supported minor argument](PrimeOrbitFixedSeedMixedKernel.md) there is a nonzero *integer* vector in the integer row span supported on those labels, with each coordinate bounded by \(H_*\). In brief, choose basis columns outside the named coordinates, extend by one named column, take an invertible row minor, and combine its rows using signed cofactors of the outside columns. All resulting coordinates are minors of the enlarged size; at least one named coordinate is nonzero. Squaring removes the sign in the actual congruences modulo \(N\): the resulting nonzero rational \(\prod p_i^{2c_i}-1\) has valuation at least \(v_\ell(N)\) at every \(\ell\mid N\). It is nonzero by distinct prime factorization.

The explicit rational consequence preceding (1.2) in [Yu, *p-adic logarithmic forms and group varieties II*](https://matwbn.icm.edu.pl/ksiazki/aa/aa89/aa8944.pdf) with the coefficient bound (1.8) gives, after summing over the fixed \(F\),
\[
 \log N_F
    \le \exp\!\big(C_F(s+1)\log(2s+2)\big)
        (C_F\log(4L))^s\,(C_F(1+(s+1)\log(4L)))\,
        \log(3+2H_*).                                             \tag{2}
\]
Unused bases can be omitted (enlarge \(C_F\)). All bases are \(\ell\)-units for \(\ell\in F\) dividing \(N\), their logarithmic heights are \(\log p_i\), and \(\log x\ll(s+1)\log(4L)\). The dimension growth stated here follows directly from Yu's displayed first-page factor \(19(20\sqrt{n+1}\,d)^{2(n+1)}\log(e^5nd)\), with rational \(d=1\) and fixed local factors. No hidden fixed-dimension Siegel–Walfisz or Subspace Theorem uniformity is used.

If \(t<L^{1-\eta}\), (1) makes \(\log(3+2H_*)\le L^{1-\eta+o(1)}\). The first factor in (2) is \(L^{O_F(c)+o(1)}\), the second is \(L^{c+o(1)}\), and the single root-height factor is \(L^{o(1)}\). Choose \(c>0\) sufficiently small that the total exponent is less than \(1-\eta/2\) for large \(N\). This contradicts \(\log N_F\ge\delta L\).

Thus the \(s+1\) directions are independent in the third alternative. The [all-size pure-cycle bound (5)](PrimeOrbitCompulsoryBranching.md) excludes any closed pure cycle on this fixed-\(F\) positive-power sector, regardless of the square-root threshold. Eliminate the acyclic matrix block on pure rows. If there were no mixed vertices, finiteness and positive outdegree would force a pure cycle. On the \(t\) mixed vertices the effective return matrix has every row sum at least two. Therefore \(I\) minus that matrix is not zero, and its rational nullity (the original row-quotient dimension) is at most \(t-1\). The third alternative has \(t\ge s+2\).

## Separation at minimal fixed-menu branching

As a different consequence, in the [fixed-seed theorem](PrimeOrbitFixedSeedMixedKernel.md), with \(N_F\ge N^{1/2+\delta}\), suppose the actual no-pair orbit attains the minimum allowed there: \(t=s+\alpha+1\) for its fixed menu \(S\). The rational nullity then equals \(s\), by the two opposed inequalities in that proof. For **each** other reached prime \(z\) a dependence on \(S\cup\{z\}\) exists, and its integer supported-minor relation must have nonzero \(z\)-coordinate since the \(S\) directions are independent. Here the number of bases is fixed. Using (1) (all original roots are fixed and small) and Yu just as above gives
\[
 \delta L\ll_{F,S}(1+\log z)\,(V(L)+t)\log L .
\]
Consequently every nonseed label of such an extremal orbit satisfies
\[
       \log z\ \ge\ L\exp\big(-O_{F,S,\delta}
                         (\sqrt{\log L\cdot\log\log L})\big).
\]
This is uniform among reached labels at that center, but it is not the assertion \(z\ge N^\epsilon\) for any fixed \(\epsilon>0\). No conclusion about the existence of a prime pair in every orbit follows.