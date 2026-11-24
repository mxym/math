# Distinct quarter-plus entry labels force disjoint real depth-two factor paths

Written research note, 2026-11-24. This is a many-source conclusion, never a claim for a lone root, an individual strongly connected component, or a terminal component.

## Abstract genuine graph lemma

Let \(N\) be even, \(0<\gamma<1\), and let \(\alpha>(1-\gamma)/2\) be a fixed exponent below 1. Suppose there are \(M\gg N^\alpha\) distinct genuine prime labels \(q>N^\alpha\), each supplied by a real prime root \(p\) in some fixed interval \(aN^\gamma<p\le bN^\gamma\), \((p,N)=1\), with \(q\) the actual largest factor of a retained quotient of \(N-p\) on a common profile. The needed property of the supplied root map is simply that for each p at most one q is assigned; selecting one witnessing \(p(q)\) per q is therefore automatically injective. The factors p, q are distinct, because \(p=q\mid N-p\) would imply \(p\mid N\). An edge below means genuine divisibility of the stated \(N-x\), including its sole prime when it is prime. This forward-factor convention reverses Bożek's orientation in [Definition 2.1](https://arxiv.org/pdf/1909.09900); it adds no edge to the undirected relation.

1. The union \(\mathcal R=\bigcup_q\{r:r\mid N-q,\ r\ {\rm prime}\}\) has size \(> L^\theta\) eventually for every fixed \(\theta<1/(1-\alpha)\), where \(L=\log N\). This is unconditional, allowing a prime \(N-q\) itself as a factor (and hence also allowing discovery of a Goldbach pair).
2. Either a positive fraction of supplied labels give distinct (up to order) direct Goldbach representations of N, or, for every fixed \(\theta<1/(1-\alpha)\) there are \(\lfloor L^\theta\rfloor\) pairwise vertex-disjoint genuine length-two directed paths \(p_i\to q_i\to r_i\), with \(p_i=p(q_i)\) and \(r_i\mid N-q_i\). If the common planted profile contains a nontrivial forced divisor \(d>1\), the path conclusion is unconditional because \(q\le (N-p)/d<N-p\), so no selected first edge is a Goldbach pair. If insisting **both** rows on every path be composite (a stricter convention than the divisor graph), either a positive fraction of the selected q give Goldbach representations through prime \(N-q\), or delete those q and run the same selection. In particular whole-composite paths apply at a hypothetical no-pair target. Even if the roles can overlap as sets over the full population, the greedily selected walks are genuine paths and all their vertices are distinct.

### Uniform arbitrary-dictionary count

For any dictionary \(\mathcal D\) of at most \(C L^\theta\) distinct primes, choose fixed \(0<\rho<\alpha\) with \(\theta(1-\rho)<1\). By Rankin,
\[
 \#\{1\le x\le N:\text{ every prime factor of }x\text{ belongs to }\mathcal D\}
 \le N^\rho\prod_{r\in\mathcal D}(1-r^{-\rho})^{-1}
 \le N^{\rho+o(1)}.
\]
The second bound is uniform in the dictionary: compress it to the first \(|\mathcal D|\) primes, and use \(r_j\ge j+1\) in its ordered list. The logarithm of the Euler product is \(O_\rho(|\mathcal D|^{1-\rho})=o(L)\). Since \(q\mapsto N-q\) is injective, only \(N^{\rho+o(1)}=o(M)\) first labels have all their second factors in any such dictionary, including adaptively chosen ones. Secondly \(N-q\ge p\gg N^\gamma\) because \(q\mid N-p\), so every second row has a prime factor. Taking \(\mathcal D=\mathcal R\) proves the unconditional size result. Quantitatively, for every dictionary of that size all but \(o(M)\) of the q's have some second child outside it.

### The exponent gap makes non-Goldbach mutual parent edges negligible

If both \(q\mid N-p\) and \(p\mid N-q\), then write \(N=p+Aq=q+Bp\). Coprimality of the distinct primes gives \((A-1)q=(B-1)p\), so there is an integer \(c\ge0\) with \(N=p+q+cpq\). If \(c=0\) there is a genuine Goldbach pair. Otherwise \(1\le c\le N/(pq)\ll_a N^{1-\gamma-\alpha}\), and
\[
 (cp+1)(cq+1)=cN+1.
\]
For each c the number of ordered candidate pairs p,q is at most \(\tau(cN+1)\), by the injective factor assignment at fixed c. Since \(cN+1\ll N^{2-\gamma-\alpha}\), the standard uniform divisor bound gives a total of \(N^{1-\gamma-\alpha+o(1)}=o(N^\alpha)\) such non-Goldbach mutual pairs. This is exactly where \(\alpha>(1-\gamma)/2\) enters, hence the strict quarter-plus cutoff for square-root-scale parents. For the genuine \(c=0\) pairs, if at least half the selected labels are mutual in this way, they already give \(\gg M\) distinct unordered Goldbach representations (at most two selected orientations per pair). Otherwise remove these and retain \(\gg M\) labels before deleting the negligible \(c\ge1\) pairs. It avoids the need for separate small- and large-q cases, and makes no assertion that 2-cycles never occur in the underlying factor graph.

### Greedy disjoint paths

Delete these \(o(M)\) mutual pairs. Given any already used vertex set \(\mathcal D\) of cardinality \(<3L^\theta\), exclude the q or \(p(q)\) already in \(\mathcal D\); by both injectivities this costs at most \(2|\mathcal D|\). Exclude also the \(o(M)\) q for which the whole second factor row is \(\mathcal D\)-smooth, by Rankin. An actual remaining \(q,p(q)\) has a child \(r\notin\mathcal D\). There is no equality \(r=q\), since any factor of \(N-q\) is a unit and \(q\mid N-q\) would contradict units; also there is no \(r=p(q)\) by the nonmutual deletion. Add the three new vertices and repeat. This gives the claimed number of pairwise vertex-disjoint actual paths in the non-Goldbach-many alternative (unconditional for \(d>1\) in the stated divisor convention). It does not place them in different SCCs.

## Applying the actual Dreamer label supply

The proved quarter-plus label corollary from the [planted square-root \(P_4\) work](PrimeOppositePlantedLargestLabelSupply.md) supplies \(M\gg N^{.2502}\) with \(\alpha=.2502>1/4\), in both the low-label and high-label branches. The graph lemma applies to its common-profile witness set, including the unplanted d=m=1 case. A valid nontrivial profile, for example \(d=m=3\) at powers of 2, gives unconditional disjoint paths in the divisor graph. In fact for every large even $N$ take an odd prime $\ell\le 2\log N$ not dividing $N$: one exists by the prime number theorem, since the product of all odd primes up to $2\log N$ exceeds $N$. Then $d=m=\ell$, $r=1\pmod\ell$ is admissible and $dm\le L^3$ for large $N$. Uniformity of the planted theorem therefore gives the unconditional genuine paths in the divisor graph for **every sufficiently large even $N$**, not just powers of two. The root window may have any width; only its actual root size exponent \(\gamma\) and the distinct supply enter the lemma. In particular \(\gamma=.5\) still applies to the [narrower width-$N^{.4916}$ interval at that scale](PrimeOppositeExactKernelLargestLabels.md), while \(\gamma=.4832\) requires \(\alpha>.2584\) for this argument. Under the high-label branch \(M\gg N^{.4}/L^2\), the same rankin selection gives \(\theta<5/3\): choose \(\rho<.4\) with \(\theta(1-\rho)<1\), so \(N^{\rho+o(1)}=o(N^{.4}/L^2)\), and the mutual pairs count here is \(O(N^{.1+o(1)})\). These conclusions are fixed-target and need no averaging over root locations.

## Optional exact second-generation color escape on the low harmonic branch

Suppose \(4\mid N\) (in particular \(N=2^j\), \(j\ge2\)), and the genuine largest-label set \(Q\subset(N^{.2502},N^{.4}]\) has reciprocal mass bounded below. A single residue class \(s\in\{1,-1\}\bmod4\) retains at least half this mass. Every such q has a child outside that same color-and-band. Indeed, if all genuine factors of \(N-q\) lie in the band, then there are exactly three counting multiplicities: two factors have product \(\le N^{.8}\), whereas four have product \(>N^{1.0008}\), and \(N-q\asymp N\). In this case \(N-q\equiv-s\bmod4\) forces an odd number (one or three, with multiplicity) of second factors into the opposite class. If instead a factor is below or above the band, it is already an escape. The low escape can be the same small prime for many q; do not claim different escape children on that branch. If a fixed positive harmonic submass has an opposite-color child in the band or a child above \(N^{.4}\), selecting such children gives \(\gg N^{.2502}/L\) distinct escape labels: for a fixed \(r\ge N^{.2502}\), the parents lie in the true congruence \(q=N\bmod r\), and their reciprocal sum is \(O(N^{-.2502}+L/r)=O(LN^{-.2502})\) by a harmonic progression bound. This last estimate applies to either displayed non-small escape category, not to the entire pool automatically.

One may trim a small fixed bottom exponent strip of width \(\xi>0\) (e.g. \(\xi=10^{-6}\) for the supplied harmonic lower bound \(.02/1300\), before restricting to a color) from the low harmonic supply, because the reciprocal mass of *all* primes in \((N^{.2502},N^{.2502+\xi}]\) tends to \(\log((.2502+\xi)/.2502)\); choose \(\xi\) after the lower harmonic constant. This retains positive mass and gives the corresponding slight improvement of the Rankin/path exponent. No specific fixed \(\xi\) is needed.


## Explicit logarithmic-factor endpoint

The same proof gives
\[
  \gg_\alpha \frac{(\log N)^{1/(1-\alpha)}}{\log\log N}
\]
vertex-disjoint paths in the non-Goldbach-many alternative (unconditionally for \(d>1\)), and at least that many second-generation labels. This refinement also works for the high-branch supply \(\gg N^{.4}/L^2\) by taking \(\alpha=.4\).

Indeed for \(D=|\mathcal D|\), the elementary bound \(p_j\gg j\log(j+1)\) gives uniformly for \(\rho\) in a fixed compact subset of \((0,1)\)
\[
 \log\prod_{r\in\mathcal D}(1-r^{-\rho})^{-1}
  \ll_\alpha \frac{D^{1-\rho}}{(\log(2+D))^\rho}.
\]
Compress to the first \(D\) primes as before and sum \((j\log(j+1))^{-\rho}\) by dyadic intervals (adjusting the finitely many first primes). Set \(\rho=\alpha-1/\log L\) for sufficiently large \(N\), and \(D\le \kappa L^{1/(1-\alpha)}/\log L\) for a sufficiently small fixed \(\kappa>0\). The displayed upper is then \(O_\alpha(\kappa^{1-\alpha}L/\log L)\), since \(L^{(\alpha-\rho)/(1-\alpha)}\) is constant. Choose \(\kappa\) so the Euler-product log is at most \(L/(2\log L)\). The Rankin bound becomes
\[
 N^\alpha\exp\!\left(-\frac{L}{2\log L}\right),
\]
which is negligible even compared with \(N^\alpha/L^C\) for each fixed \(C\). The earlier used-vertex exclusions and mutual-pair count are unchanged. Greedy selection can therefore continue for at least a fixed small multiple of \(L^{1/(1-\alpha)}/\log L\) steps.
