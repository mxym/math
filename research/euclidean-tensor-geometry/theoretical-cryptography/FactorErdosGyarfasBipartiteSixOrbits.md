# The sharp 32-cycle cutoff for bipartition-preserving abelian six-orbit actions

**Theorem.** Suppose a nonempty finite simple bipartite graph has minimum degree at least three and admits a free abelian automorphism action preserving each side of a specified bipartition, with at most six vertex orbits in total. Then it has a simple cycle of length $4$, $8$, $16$, or $32$. The cutoff 32 is sharp, even for connected cubic graphs under a free cyclic action with exactly six orbits.

This completes the bipartition-preserving six-orbit case; it does not cover arbitrary six-orbit quotients or actions that exchange the two sides. The sharpness examples are the [previous cyclic covers of $K_{3,3}$](FactorErdosGyarfasSixOrbitBarrier.md), whose specified action preserves each part. The result differs from [Gebendorfer's cubic bipartite vertex-transitive girth-six theorem](https://doi.org/10.5281/zenodo.22666267): we do not require vertex transitivity, cubic degree, or girth six, but require the stated abelian action. For voltage cover background see [Exoo](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v11i1n2/pdf). This is a restricted result for Erdős–Gyárfás, not the general conjecture.

## 1. The three quotient reductions

Write the acting group additively as $A$. A free orbit is a layer labeled by $A$, so each edge orbit between layers is a translation matching. Within-layer edges are impossible because the two sides are preserved. If there are at most five layers, the [five-orbit theorem](FactorErdosGyarfasAbelianFiveOrbits.md) gives the conclusion.

By the local reductions of the [four-layer theorem](FactorErdosGyarfasAbelianFourOrbits.md), it suffices to consider quotients of multiplicities $0,1,2$ with the doubled pairs disjoint. Three matchings between two layers give a dyadic cycle by the [two-orbit theorem](FactorErdosGyarfasAbelianTwoOrbits.md). If two doubled pairs are incident with the same layer, their respective label differences are two nonzero steps $x,y$ in that layer. The length-two paths to the same endpoint give a square if $y=\pm x$; otherwise use the rectangle $0,x,x+y,y$ in the common layer and replace the four sides by length-two paths. The two middle layers are distinct and the repeated uses of a middle layer differ by the other nonzero step, so this is a simple 8-cycle.

The remaining six layers must split $3+3$. If one side has only one layer the other cannot reach degree three; if it has two and the other has four then each opposite layer would need its own doubled pair, contrary to disjointness. Thus write a $3\times3$ matrix of cross multiplicities, with row and column sums at least three and at most one 2 in each row and column. Each row or column has at most one 0.

* If there are two full rows, keep one matching along each edge between those rows and the three opposite layers. The result is a cover of $K_{2,3}$. Its three length-two paths between the two outer layers contract to three translation matchings. If two have equal shifts there is a simple 4-cycle via the two different middle layers. Otherwise the two-orbit theorem gives a simple contracted cycle of length $4,8,$ or $16$; expanding each edge gives a simple cycle of length $8,16,$ or $32$. A repeated vertex in a middle layer would use the same path from the same pair of endpoints, impossible in the simple contracted cycle.
* Otherwise there are at least two 0 entries. If there are exactly two, they occupy different rows and columns. Every row or column with a 0 has one 2 and sum three. If there is excess, it is one unit in the single other row and column; their intersection is positive, and deleting a matching there leaves every row and column of sum three. With exactly two 0 entries the resulting cubic array is, after relabeling, $(0,2,1),(2,0,1),(1,1,1)$.
* With three 0 entries, they form a permutation matrix in the support complement. The support is a six-cycle, every layer must have one doubled incident edge, and the three doubled edges form an alternating matching around it.

These reductions depend only on the orbit quotient; deleting matchings keeps a subgraph of the original graph.

## 2. Two weighted theta lemmas

Take two endpoint layers and three matching paths between them of lengths $1,1,\ell$, with the middle layers of the long path distinct and different from the endpoints. After choosing origins the three contracted endpoint shifts are $0,x,y$; the two direct matchings are distinct, so $x\ne0$. If there is no simple cycle of length at most 32 that is a power of two, the following alternatives hold:
\[
\begin{array}{c|l}
 \ell & \text{necessary alternative}\\\hline
 3 & y=2x\text{ or }y=-x,\\
 5 & 2y=0\text{ or }2(y-x)=0.
\end{array}
\tag{1}
\]
Only the implication shown is used; the alternatives are not asserted to be sufficient for the absence of such a cycle.

Here is an exact small certificate for (1). Use formal generators $(1,0),(0,1)$ for $x,y$. A state is a subgroup $R$ of $\mathbb Z^2$ required to vanish under evaluation. A word in $0,1,2$ gives the alternating endpoint walk with weights $1,1,\ell$ from the listed shifts. The successor vertices come from their layer and partial voltage. For an accepted candidate the weighted length is $4,8,16,$ or $32$, the total voltage is in $R$, and every difference between distinct partial voltages in the same endpoint layer is **outside** $R$. This makes the contracted lift simple over $\mathbb Z^2/R$. For an actual evaluation extending $R$, either the same simple lift persists, or one of those differences vanishes. In that case the relation lattice strictly increases by that difference, and its child is checked. A child forcing $x=0$ is impossible. Inside the long path, each intermediate vertex is matched bijectively to its two endpoint coordinates; repeating it would repeat a long-path traversal or an endpoint of the simple contracted lift. Thus checking the endpoints suffices also for each expanded cycle.

The frozen table has 38 reached cells in the length-three case and 25 in the length-five case, with at most three proper collision steps. Every non-word row implies one of the displayed alternatives by exact integer containment, and all other rows specify walks. The checker computes integer row Hermite forms and checks every possible collision, not only a list of finite group orders. In particular it accommodates torsion and additional relations.

## 3. Two doubled pairs: glued length-three thetas

Use $U,V$ for the central edge and $(A_1,B_1),(A_2,B_2)$ for the doubled pairs. Each one has a long path $A_i,V,U,B_i$ of length three, and the two paths share $UV$. Normalize the five tree shifts on the union of these paths to zero. In a graph with no dyadic cycle through 32, (1) holds for both pairs. Swapping the direct matching order sends $(x,y)$ to $(-x,y-x)$, so we can arrange $y=-x$ in both. In these tree coordinates the forward direct shifts of pair $i$ must therefore be $x_i,2x_i$, with $x_i\ne0$.

This leaves a two-generator graph on the six layers, with zero shift on the five tree edges. The same relation-lattice check now has just three reached states: the empty state with a 16-step candidate; its only admissible collision states impose $x_1=\pm x_2$, each with an 8-step candidate and no admissible further collision. Here the checker records every layer of the original six-layer graph and verifies total voltage and all partial differences. Thus this template always supplies a dyadic cycle, a contradiction.

## 4. Three doubled pairs: a voltage cube

Orient the support six-cycle cyclically. Choose one primary shift per edge and let $z$ be their sum. For the three doubled edges let $x_i\ne0$ be alternative minus primary shift, in the same directed orientation. For double $i$, the complementary path of length five can use any primary or alternative matching at each other doubly covered edge. Its shift relative to the primary shift of double $i$ is
\[
 y=-z-\sum_{j\ne i}\varepsilon_j x_j,\qquad \varepsilon_j\in\{0,1\}.
\]
By (1), its length-five theta forces either $2y=0$ or $2(y-x_i)=0$ if there is no dyadic cycle. Equivalently, on every edge of the binary cube of choices, at least one of the two values
\[
 D_\varepsilon=2\left(z+\sum_j\varepsilon_j x_j\right)
\]
is zero. If $2x_i=0$ for some $i$ the parallel matchings already make a simple 4-cycle. Otherwise neighboring cube vertices have different values. Exactly one endpoint of each edge is zero, so the zero vertices are one entire parity class.

Put $X_i=2x_i$. If the zero class is even, then $2z=0$ and $X_i+X_j=0$ for every distinct pair. All three $X_i$ are equal and twice each is zero. If the zero class is odd, the three singleton vertices give $2z+X_i=0$, and the all-one vertex gives $2z+X_1+X_2+X_3=0$. Again the three $X_i$ are equal and twice each is zero. Since the $X_i$ are nonzero, $x_i$ has order four. Alternating the two direct matchings now gives a simple 8-cycle, again a contradiction.

These cases complete the upper bound. The earlier family has no $4,8,16$ cycles and has a 32-cycle, so it proves the stated sharpness.

**Exact replay.** Run `python3 -O verify_erdos_gyarfas_bipartite_six.py` beside `erdos_gyarfas_bipartite_six_certificate.json`. The verification separately checks the quotient census, both weighted thetas, and the glued template. No solver or bound on the acting group's order is used.
