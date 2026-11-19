# The cycle-count spectrum of simple 3-connected graphs

**Theorem (computer-assisted).** A positive integer is the total number of undirected simple cycles of a finite simple 3-vertex-connected graph if and only if it is not one of
$$
1\text{–}6,\quad8\text{–}12,\quad16\text{–}20,\quad27,\quad30,\quad32\text{–}34.
$$
These are exactly the 21 entries in McCulloch–McKay–Salahshoori–Zaslavsky, [*The Cycle Counts of Graphs*](https://doi.org/10.1007/s00373-026-03047-3), §6(a). We do not use their finite reported counts as premises. The host degrees are **unrestricted**; this theorem does not solve the authors’ 3-connected cubic or planar cubic questions. We use 3-connectivity in the usual sense of at least four vertices and connectivity after removal of any set of at most two vertices.

The proof separates a quadratic family with an infinite covered tail, its finite arithmetic bridge with direct residual graph witnesses, and an independent exhaustive small-budget exclusion.

## 1. Templates and the cycle polynomial

Start with a finite simple graph $J$ on vertices $0,\ldots,n-1$, with terminals $s=0,t=1$. Between them add $m$ ordinary paths, internally pairwise disjoint and disjoint from $J$, with $x_i\ge1$ new internal vertices on the $i$th path. Call the resulting graph $H$. Add a hub adjacent to all ordinary internal vertices and precisely a specified subset $B$ of the core vertices. There are no parallel edges. Only templates whose unit-length parameters $x_i=1$ pass the 3-connectivity test are used.

All positive integer lengths in such a template preserve 3-connectivity. To lengthen a branch, subdivide one of its edges $uv$ by $w$ and also join $w$ to the hub $h$, distinct from $u,v$. If $w$ survives up to two vertex deletions, paths between old surviving vertices can still use the subdivided edge when both endpoints survive, and at least one of $u,v,h$ survives to attach $w$. If $w$ is deleted, at most one old vertex $z$ is deleted. The previous graph, with $z$ removed if applicable, is still at least 2-connected; hence losing the edge $uv$ cannot disconnect it. Iteration proves the assertion.

Write $p_0$ for the number of simple terminal paths in $J$ and $P=m+p_0$. Write $N=\sum x_i$ and $T=\sum_i\binom{x_i}{2}$. There are two template constants $a,b$ independent of the lengths such that the cycle count is
$$
k=b+aN+(P-1)N(N-1)-(P-2)T. \tag{1}
$$

To obtain those constants, count the cycles not meeting the hub first. There are the cycles of $J$, $m p_0$ cycles using one ordinary branch and a core terminal path, and $\binom m2$ cycles using two ordinary branches. Each remaining cycle consists of the hub, two distinct neighbors and a simple path in $H$ joining them. For two core neighbors that path count is unchanged by ordinary branch subdivisions. Add the counts for all unordered pairs in $B$ to the hub-free count to get $b$. For an ordinary internal vertex and one core neighbor, the path count is independent of the ordinary vertex's branch, position and lengths: keep the distinguished vertex and smooth all other unnecessary ordinary degree-two vertices. Sum over the core neighbors to get $a$ by taking one ordinary vertex in the unit template. This class contributes $aN$.

Two ordinary vertices on the same branch have $P$ paths: the direct segment, or a route around the terminals using one of the other $P-1$ terminal paths. Two ordinary vertices on different branches have $2(P-1)$ paths: via one of the two terminals only, or through another terminal path in either direction. There are $T$ pairs of the first kind and $\binom N2-T$ of the second, giving (1). In particular the term for two ordinary vertices does not double-count a traversal of the same undirected cycle.

## 2. An infinite covered tail via four squares

The 87 high templates marked H in `core-styles.txt` have five core vertices, nine ordinary branches, $P=12$, $0\le a\le161$ and $0\le b\le266$. A row gives a core-edge mask (lexicographic unordered vertex-pair order, least significant bit first) and a hub-neighbor mask (bit $j$ for vertex $j$). There are 87 distinct coefficient pairs. The following ten small finite checks depend only on the rows, not on $N$ beyond its residue. For every $u=0,\ldots,9$,
$$
\{\,b+au+11u(u-1)\bmod10:\ (a,b)\text{ from a high row}\,\}=\{0,1,\ldots,9\}. \tag{2}
$$
The supplied checker derives the coefficients from the actual graphs, checks 3-connectivity in each base and verifies all 100 membership assertions. Thus the residue obstruction for a cone over a plain theta graph is not being assumed away.

Put $N=8L+r$ with $1\le r\le8$. Take the first eight lengths as four pairs $L\pm z_j$, and the last length as $r$. Relative to $z_j=0$, the statistic $T$ increases by $\sum z_j^2$. Lagrange's four-square theorem represents every integer $0\le u\le(L-1)^2$ by four squares with each $|z_j|\le L-1$, so both signs yield branch lengths at least one, including the endpoints. Define
$$
V(N)=11N(N-1)-10\bigl(8\tbinom L2+\tbinom r2\bigr).
$$
For a high row all values $V(N)+aN+b-10u$ occur for the indicated consecutive $u$. By (2), every integer in the closed interval
$$
[\,V(N)+161N+266-10(L-1)^2,\ V(N)\,]                         \tag{3}
$$
occurs if that interval is nonempty: select a row of the candidate's residue, then its top is at least $V(N)$ and its bottom is at most the common left endpoint.

As $N$ increases by one, $V(N+1)-V(N)\le22N+280$: either the last length increments ($T$ increases by $r$), or $r=8$ resets to 1 and $T$ changes by $8L-28$. These formulas also show that $V(N)$ increases without bound. For $N\ge1500$, the squared-radius allowance at $N+1$ is at least $10(N/8-2)^2\ge 10(N/9)^2\ge185N$. This is at least $(22N+280)+161(N+1)+266$. Thus (3) at $N+1$ contains the full interval from $V(N)$ to $V(N+1)$. We obtain every count at least $V(1500)=23,342,160$. This large number is only an intermediate sufficient threshold.

## 3. The finite bridge is an exact interval proof

`bridge.py` proves coverage up to and including that same endpoint. An interval $[l,h]$ of attainable triangular sums $T$ under a single high row and fixed $N$ gives an interval of integer quotients in the residue $r'=K\bmod10$, where $K=b+aN+11N(N-1)$. Precisely the quotients from $\lfloor K/10\rfloor-h$ to $\lfloor K/10\rfloor-l$ are then attained. The checker merges these inclusive intervals separately for every residue, without interpolating between different residues.

* For $9\le N\le90$, all attainable $T$ are obtained by the exact recurrence $D(0,0)=\{0\}$ and $D(j,N)=\bigcup_{x=1}^{N-j+1}(\binom x2+D(j-1,N-x))$ (other base cells empty). A bitset holds each finite set. Consecutive runs yield the intervals.
* For $91\le N\le1500$ it suffices to take each $y=\max(1,L-h)$ with $h\in\{0,1,2,3,4,8\}$. Four pairs centered at $y$, with ninth branch $N-8y\ge1$, give the interval of $T$ from $8\binom y2+\binom{N-8y}2$ through that value plus $(y-1)^2$, by the same four-square argument. Only the positive inclusion for these intervals is needed.

The union leaves precisely 2,645 positive integers through 23,342,160, the largest 99,661. For those values, 118 low templates (L rows) with $m\le N\le150$ use (1) and the same exact triangular-sum recurrence; successful choices are reconstructed to actual branch lengths. Six small masks are available as literal alternatives for $7,29,47,48,49,50$. In total 2,624 residual integers receive literal full graph witnesses. The 21 not covered are exactly the displayed exception list. `literal.cpp` verifies every one of the 2,624 residual edge lists directly: no loops, no repeated edge, successful connectivity for all zero-, one-, and two-vertex deletions, and the total cycle count by depth-first traversal anchored at the cycle's least vertex (both directions, divide by two). This does not reuse (1). It additionally checks 615 expanded graphs from all 205 template styles at three test vectors per style, including varied non-unit lengths. The finite residuals include concrete order-nine graphs for 47–50. The generation formulas, not a large precomputed witness file, suffice to reproduce all these tests.

## 4. No graph with a listed count is missed

The separate program `exhaust34.py` starts from the three parallel edges of a theta core (three digons). It exhausts all reduced loop-free inseparable multigraph cores of cycle count at most 34 that are relevant to a minimum-degree-three host. Vertices of the final simple 3-connected hosts already have degree at least three, so no final vertex is suppressed.

Here is the completeness argument. Start with a cycle in the desired host. A component of the complement of a current 2-connected prefix attaches to at least two distinct prefix vertices, or its unique attachment would be a cut vertex. Join two attachments by an open ear through that component. When all vertices are present, add each unused edge as a one-edge ear. Each extension preserves 2-connectivity, and the first ear with the initial cycle suppresses to three parallel edges. Every later ear has two distinct ends, each either an existing core vertex or an interior position along an edge of the suppressed core. The two interior positions may lie on the same edge occurrence or on two distinct parallel copies. A vertex endpoint and an incident-edge position are allowed, as are two distinct old vertices even when adjacent. Replace the ear by a fresh edge, subdividing the chosen positions first. This realizes the reduced next prefix. No loop is needed: once there are at least two branching vertices in an inseparable prefix, a suppressed loop would exhibit its one attachment as a cut vertex. The usual open-ear argument here is that of Whitney; McCulloch et al.’s Lemma 4 gives the incremental count below.

Every operation keeps the old cycles after subdivision and adds one cycle for each simple path between the two ends of the proposed ear in the subdivided graph before it is added. Edge copies are distinguished, so digons count correctly. There is at least one new cycle. The search discards only above the budget, or when a graph is equal or isomorphic to one already retained in the level. Exact relabeling checks multiplicities and nonedges for every pair of mapped vertices; color refinement just groups candidates. The rank $|E|-|V|+1$ increases by one per ear, including an ear between existing vertices. No maximum order or degree is imposed. The recursion stops at an empty level.

|Cycle rank|Retained cores|Simple 3-connected outputs|
|---:|---:|---:|
|2|1|0|
|3|4|1|
|4|17|3|
|5|118|11|
|6|895|1|
|7|2,134|0|
|8|0|0|

Testing the simple graphs with at least four vertices after removal of up to two vertices gives precisely the missing counts stated in the theorem over $1,\ldots,34$. The finite bridge and the infinite tail establish occurrence for every other positive integer.
