# Large-degree growth of connected vertex sets in regular graphs

For a finite nonempty simple graph $G$, let $N(G)$ count its nonempty vertex subsets inducing a connected subgraph; count singletons. Let $N_{\rm dom}(G)$ count those among them that also dominate $G$. Write $c_d$ and $\widetilde c_d$ for the limsup, as the feasible order $n\to\infty$, of the largest $N(G)^{1/n}$ and $N_{\rm dom}(G)^{1/n}$, respectively, over simple $d$-regular graphs of order $n$. This is the normalization of Cambie, Goedgebeur and Jooken, EJC 32(1) (2025), P1.20. Their conclusion (§6) asks whether $c_d=2-\Theta(2^{-d})$. Our answer is negative.

**Theorem.** As the integer $d\to\infty$,
$$
2-c_d=\Theta(2^{-d}/d),\qquad 2-\widetilde c_d=\Theta(2^{-d}/d).
$$
This determines orders, not asymptotic equivalents, extremal graphs at fixed order, or the base for any fixed small degree. The constructive side suffices even for connected dominating sets; the other side is a published bound.

## 1. The classical direction

Björklund, Husfeldt, Kaski and Koivisto's upper bound, also proved in Kangas et al., Corollary 7, is $N(G)\le n+(2^{d+1}-1)^{n/(d+1)}$ for maximum degree at most $d$. In the present regular setting the radius-one argument is especially direct: discard the $n$ singleton sets; the projection of any remaining connected set on each closed neighborhood $N[v]$ cannot be the singleton $\{v\}$. There are at most $2^{d+1}-1$ possible traces on each neighborhood, and each coordinate appears in exactly $d+1$ neighborhoods. Shearer's projection inequality gives the bound. For fixed $d$, taking the limsup of $n$-th roots therefore gives
$$
\widetilde c_d\le c_d\le 2(1-2^{-(d+1)})^{1/(d+1)}
\le 2-\frac{2^{-d}}{d+1}.
$$
The last inequality is the tangent-line bound by concavity of $x\mapsto x^{1/(d+1)}$ at 1.

## 2. A width-four strip and a local condition

Take the Cartesian product $B=C_4\square C_m$ with **even** $m\ge 10$. Its vertices are $(i,j)\in\mathbb Z/4\times\mathbb Z/m$, and edges change one coordinate by $\pm1$. The four vertices at fixed $j$ form a column. Call some of these base vertices occupied and all others vacant. Impose this rule: **each cyclic interval of four consecutive columns contains at most three vacant vertices.**

We claim (i) all occupied vertices are in one component, and (ii) every vertex, occupied or not, has an occupied neighbor. For (ii), the four distinct neighbors of any given vertex are all within three consecutive columns, so cannot all be vacant. For (i), every interval of four columns has an intact (entirely occupied) column. There are at least two intact columns because $m\ge10$. In cyclic order, the gap between consecutive intact columns $L,R$ has at most three intermediate columns. There are at most three vacancies in those intermediate columns, since they lie inside four consecutive columns; the two endpoints are intact. One of the four rows has no vacancy in the gap. Its path connects the intact columns, each of which is a connected 4-cycle. This joins all intact columns.

For an occupied vertex $u=(i,j)$ in the gap, consider its straight paths in row $i$ to $L,R$, and the two paths taking one vertical step to row $i+1$ or $i-1$ and then going straight to $L$. These four paths are pairwise vertex-disjoint outside $u$, including distinct ends (the straight left and right paths end on different intact columns). Three vacancies cannot block all four. This joins every occupied vertex to the intact columns, proving the claim including cyclic wraparound.

## 3. Blow-up, probability and every degree

Replace each base vertex by $t$ independent twins, joining neighboring fibers completely and adding no other edges. This gives a simple $4t$-regular graph $G_0$ on $n=4mt$ vertices. Choose a uniform random subset of the clones; each fiber, independently, is empty with probability $q=2^{-t}$. A nonempty fiber is called occupied. Under the local rule of §2 the chosen subset is a connected dominating set: along each edge of the connected occupied support there is a complete bipartite graph between the chosen parts. Distinct chosen clones of a single fiber are linked by a two-edge path using any occupied neighboring fiber, which exists by (ii). Every unchosen clone likewise has a chosen neighbor in a neighboring fiber. There is no need to impose equality of choices within a fiber.

Write $K=\binom{16}{4}=1820$. In a specified four-column window the probability of four or more vacant fibers is at most $Kq^4$, by a union bound. Each of the $m$ window-good events is increasing in the independent occupancy indicators. Harris's product-measure inequality, iterated (intersection preserves monotonicity), bounds the probability that all windows are good *from below* by $(1-Kq^4)^m$, for $Kq^4<1$. Disjointness or independence of these windows is not assumed. Hence $N_{\rm dom}(G_0)\ge 2^{4mt}(1-K2^{-4t})^m$.

For $d=4t+s$, $0\le s\le3$, assume $t\ge3$. For each $0\le j<m/2$ and each row $i$, pair the two fibers at $(i,j)$ and $(i,j+m/2)$. They were nonadjacent in $B$. For offsets $b=0,\ldots,s-1$ join each clone $a\in\mathbb Z/t$ in the first to clone $a+b$ in the second. These are $s$ disjoint perfect matchings across each pair and add exactly $s$ to every degree without duplicating an edge. The result is simple and $d$-regular. Previously connected dominating subsets remain so after the addition.

For each fixed large $d$, let even $m\to\infty$ first. Taking roots gives
$$
\widetilde c_d\ge2(1-K2^{-4t})^{1/(4t)}.
$$
Put $x=K2^{-4t}\le1/2$ for sufficiently large $d$. Since $-\log(1-x)\le2x$ and $1-e^{-y}\le y$ for $y\ge0$,
$$
2-\widetilde c_d\le K2^{-4t}/t
=K2^s2^{-d}/t=O(2^{-d}/d),
$$
uniformly in $s\in\{0,1,2,3\}$. Together with §1 this proves the theorem. In particular, neither gap is of order $2^{-d}$. The constants in this sufficient window rule are not optimized.
