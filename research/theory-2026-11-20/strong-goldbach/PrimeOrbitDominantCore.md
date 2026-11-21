# A common prime-factor core and a growing number of reachable Goldbach pairs

Use the arc x→y for primes y|N−x, the reverse of [Bożek's Definition 2.1](https://arxiv.org/abs/1909.09900). Fix a nonempty finite menu of odd prime seeds and any fixed progression admitting even integers coprime to all of them. Write \(\mathcal A_X\) for those admissible even centers in [X,2X], and \(L=\log\log X,\ R=\lfloor\sqrt L\rfloor\). All displays concern sufficiently large X with the initial data fixed.

1. Outside \(o(X)\) centers of \(\mathcal A_X\), all the seeds and every odd prime \(r\le 2R\) not dividing N belong to a single strongly connected component \(C_N\). Each of those r has a path in each direction of length at most two to a fixed seed. Also, all but \(o(\pi(N))\) prime vertices have a directed path into \(C_N\), uniformly outside a set of \(o(X)\) centers. This is a *backward* basin statement; generic terminality of the core is not asserted.
2. At \(\gg X\) centers in \(\mathcal A_X\) the same core reaches
\[
          \gg \frac{\sqrt{\log\log X}}{(\log\log\log X)^2}
\]
**distinct genuine Goldbach pair sinks**, each with a prime summand \(Q\in[X^{1/20},X^{1/12}]\). In particular all the seeds, and all but \(o(\pi(N))\) prime input vertices, can reach *each* of these pairs by a suitable choice of path. This common core is nonterminal on this positive-density set. The positive fraction and the two implied constants in part 2 depend only on the fixed inputs, not on a requested number of pairs.

This strengthens [the fixed-seed positive-density sink theorem](PrimeOrbitCommonGoldbachSink.md). Neither part 1 nor part 2 proves density one of sink access or gives a pointwise binary Goldbach theorem.

## Two steps are enough for small primes on typical centers

First a qualitative principle: for fixed primes a,r with r∤N, condition on the nonzero residue \(u=N\bmod r\). For every sufficiently large prime \(t\equiv u\bmod r\), the single condition \(t\mid N-a\) forces \(a\to t\to r\). The density of integers avoiding any finite list of these divisibilities is, inside that residue class, the CRT product \(\prod_t(1-1/t)\), which tends to zero by divergence of the reciprocals in a reduced progression. This explains the direction of the edges and the necessity of keeping only targets coprime to N.

Here is a uniform quantitative version. For a target prime r≤2R not dividing N, condition on \(N=u\bmod r\), \(u\ne0\). A bridge t may be sought among primes
\[
        \exp(L^2)<t\le X^{1/1000},\qquad t=u\bmod r.
\]
For any source prime \(a\le 2R\) (which includes all fixed seeds eventually), the absence of such a bridge means the progression index of N must avoid one class mod each such t, independent of the size of a. Let \(H=X/r+O(1)\), \(z=X^{1/4}\). The arithmetic large sieve gives an avoidance count at most \((H+O(1)+z^2)/G\), with G the sum over squarefree d≤z supported on these t of \(\prod_{t|d}1/(t-1)\). The unrestricted Euler mass is \(\prod_t(1-1/t)^{-1}\); under its normalized weights the mean \(\log d\) is \(\sum_t\log t/t\le (\log X)/1000+O(1)\). By Markov at least half its mass has d≤z. Consequently the count is
\[
             \ll (X/r)\exp\big(-\sum_t1/t\big).
\]
The prime number theorem of Siegel–Walfisz (in the uniform range \(r\le\log v\) for \(v\ge\exp(L^2)\)) and partial summation give uniformly
\[
 \sum_t \frac1t
 =\frac{\log\log(X^{1/1000})-\log\log(\exp(L^2))}{r-1}+o(1)
 \ \ge\ \frac{L}{2(r-1)} .
\]
Indeed the integrated error from the uniform exponential remainder \(O(v\exp(-c\sqrt{\log v}))\) is \(o(1)\); the main numerator is \(L-2\log L-O(1)\). The estimate is uniform over the relevant nonzero classes. Union over u, then over \(r\le2R\), costs \(O(XR\exp(-L/(4R)))=o(X)\) for each fixed source p. In reverse, with target p fixed, union over all sources \(r\le 2R\) costs \(O(XR\exp(-L/(2(p-1))))=o(X)\). Ignore a source equal to the target, which requires no path to itself. Intersect this result with the fixed admissible set and do so for the finite seed menu. The claimed SCC follows. All bridge primes lie strictly between the source labels and X, and both bridge-input complements exceed their next divisors for large X.

## Backward basin

For N satisfying the two-step result, any prime x congruent to N modulo an odd unit prime r≤2R has an arc to \(C_N\). Let \(D=\prod_{3\le r\le 2R}r\) over primes, which satisfies \(D\le\exp(O(R))\le\log X\). Uniformly for X≤N≤2X, Siegel–Walfisz in this single modulus, summed over at most D reduced classes, shows that the fraction of prime vertices missing all these congruences is at most
\[
   \prod_{\substack{3\le r\le2R\\r\nmid N}}
       (1-1/(r-1))+o(1).
\]
Primes dividing D or lying beyond N−2 affect the fraction by \(o(1)\). At a prime \(r\nmid N\) exactly one reduced class is deleted; at \(r\mid N\) no reduced class is deleted. The unrestricted product over all indicated r is \(O(1/\log(2R))\) by Mertens, and restoring the primes dividing N costs at most \(G(N)=\prod_{r\mid N,\,r\ge3}(1+3/r)\), since \((1-1/(r-1))^{-1}\le1+3/r\). Its first moment over [X,2X] is \(O(X)\): expand over squarefree d, bound the number of multiples by \(2X/d\), and use \(\prod_r(1+3/r^2)<\infty\). Outside \(O(X/\sqrt{\log R})\) centers we have \(G(N)\le\sqrt{\log R}\). This gives the asserted basin statement also after restriction to a fixed admissible progression. No measure concentration at a fixed individual N is inferred.

## Many roots and many different terminal pairs

For a lower bound we may select one fixed class \(N=a\bmod h\) inside \(\mathcal A_X\) with h even and containing all seed primes as divisors. Put \(\mathcal R=\{r\text{ prime}: R<r\le2R\}\) and \(K=|\mathcal R|\asymp R/\log R\). Start one increasing path at each possible r. Its intermediate labels are the ordered prime factors of a squarefree \(s\le Y=X^{1/1000}\), all **strictly above \(2R\)**. Its final prime Q lies in the preceding theorem's interval \(J=[X^{1/20},X^{1/12}]\), in one fixed reduced class modulo h for which \(a-Q\) is also reduced. Such a class exists, including at 2 and 3, as proved there. Let \(Z(N)\) count these actual paths with \(N-Q\) prime in \([X,3X/2]\). In defining \(Z\) do not yet require r∤N; all non-unit root centers will be removed below. The congruences and all local primality obstructions are exactly those of the preceding proof, with initial predecessor r.

We give the uniform constants in the two moment bounds
\[
 \sum_N Z(N)\gg_h \frac{K X}{\log R},\qquad
 \sum_N Z(N)^2\ll_h \frac{K^2 X}{(\log R)^2}.                 \tag{1}
\]
For the lower bound per root, the reciprocal mass of s is \(\gg\log Y/\log R\) uniformly: in the squarefree Euler product over \(2R<\ell\le Y^{1/8}\) with local weight \(1/\ell\), the mean \(\log s\) is \(\sum\log\ell/(\ell+1)\le \tfrac18\log Y+O(1)\). At least half the mass lies below Y and the product is \(\gg\log Y/\log R\). The reciprocal mass of Q in its fixed class is bounded below by a positive h-dependent constant. The forbidden coincidences \(Q=\text{previous label}\bmod\ell\), \(\ell\mid s\), remove \(O(\log Y/R)\) of the joint reciprocal mass, by the preceding proof's Brun–Titchmarsh bound. This is \(o(\log Y/\log R)\); all constants here are independent of r∈\(\mathcal R\). As before, \(h sQ\) is unique within each root's sum and less than \(X^{1/3}\); over all roots the Bombieri–Vinogradov error costs at most \(O_{A,h}(KX/\log^A X)\). The reduced class for the true prime is counted in a fixed interval, with mass \(1/\phi(hsQ)\ge1/(hsQ)\). This proves the lower bound. The first moment upper bound is \(O_h(KX/\log R)\), by \(\prod_{2R<\ell\le Y}(1+1/(\ell-1))\ll\log Y/\log R\) and the same distribution estimate, even after dropping the admissibility restriction from the main-term sum.

For two different roots no compatible paths share a later vertex. A shared vertex would have a unique backward chain of smaller parents (each is the remainder of N upon division by the target), so one root would occur in the other path or the two roots would coincide; the former is impossible by the strict separation of scales. The terminals therefore differ too. For two distinct paths from one root the common labels constitute a shared prefix c, again with distinct terminals. In both cases the uniform two-shift sieve and terminal-difference estimate from the preceding theorem apply with identical constants (they depend on fixed h, not r). Their cost per path pair is \(O_h(X/\log^2 X)\) times the reciprocal modulus and the local factors there, with \(F(n)=\prod_{\ell|n}(1+6/\ell)\). The modulus including h is at most \(h X^{2/1000+1/6}\) in all cases.

For distinct roots the product of the two reciprocal interior masses with local factors is
\[
 \ll \left(\prod_{2R<\ell\le Y}(1+F(\ell)/\ell)\right)^2
 \ll \frac{\log^2 Y}{\log^2 R}.
\]
For equal roots the empty prefix has the same bound. With nonempty shared prefix c, all prime factors of c exceed 2R, and each tail after c has mass \(O(\log Y/\log(2P^+(c)))\). For largest prefix factor \(\ell>2R\), the total \(F(c)/c\) is
\[
  \le \frac{F(\ell)}{\ell}
       \prod_{2R<j<\ell,\,j\ {\rm prime}}(1+F(j)/j)
  \ll \frac{\log(2\ell)}{\ell\log R}.
\]
Since \(\sum_{\ell>2R,\ \ell\ {\rm prime}}1/(\ell\log\ell)\ll1/\log R\), every ordered root pair, including the same-root off-diagonal, costs at most \(O_h(X/\log^2 R)\). The terminal-difference factor has bounded mean as before because the fixed Q range and the weight \(F(Q-Q')\) did not change. Summing the \(K^2\) ordered root pairs and the first-moment upper bound for the diagonal proves (1), since \(K/\log R\to\infty\).

The second-moment lower-tail inequality (or Cauchy–Schwarz after removing small values) now shows that \(\gg_h X\) centers have \(Z(N)\gg_h K/\log R\). Both constants are independent of R. Each count here is a **different unordered prime pair**: backward uniqueness gives a distinct terminal Q, and \(N-Q\gg X^{1/12}\) belongs to the other scale. The number of centers divisible by any \(r\in\mathcal R\) is at most \(O(X\sum_{R<r\le2R}1/r+K)=O(X/\log R)=o(X)\). Remove these centers, the \(o(X)\) exceptions to mutual reachability and the \(o(X)\) exceptions to the basin statement, only after taking the second moment. Then all counted roots belong to \(C_N\). Since \(K/\log R\asymp\sqrt L/(\log L)^2\), the theorem follows.

**Inputs.** [Vaughan's account, §1](https://personal.science.psu.edu/rcv4/Bombieri.pdf) includes the Siegel–Walfisz and Bombieri–Vinogradov estimates. The arithmetic sifted-set inequality is in [Montgomery–Vaughan, Ch. 19](https://personal.science.psu.edu/rcv4/571s25/montgomery-vaughanII.pdf); the required uniform two-terminal sieve, endpoint difference average, and squarefree CRT construction are fully spelled out in [the preceding theorem](PrimeOrbitCommonGoldbachSink.md). These are structural reachability conclusions about genuine primes, not new ordinary exceptional-set estimates or a proof of Goldbach.

**Related work.** [Kelanemer, SSRN 7274460](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7274460) publicly describes a related directed factor graph and terminal-component framework. Its full text was not retrievable, so no priority or comprehensive overlap claim is made.
