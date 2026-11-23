# Overlaps of two norm-18 vectors and the switch at norm 16

These arguments apply to a strongly regular graph with parameters $(99,14,1,2)$ at each of the remaining Seidel ranks $36,38,40,42$. Write $N_s$ for the number of **oriented** integral $-4$ eigenvectors of squared norm $s$. A unit labeling has all entries in $\{-1,0,1\}$. Write $U_{a,t}$ for their number at $Ab=-4b-2a\mathbf1$, $b^tb=t$.

## Nine shared sites force a tenth

Fix a positive vertex $o$ of a norm-18 vector and its four negative neighbors $Q$. For each pair $a,b\in Q$, denote their common neighbor other than $o$ by $z_{ab}$. The six vertices so obtained are distinct since each has just two common neighbors with $o$. Choose four of these labels required to be positive. Call this choice, including $o,Q$, a window. Any norm-18 marking through $o$ has at least four positive pair labels by counting its twelve incidences from $Q$ to the other eight positives.

**Theorem.** Two different markings in the same window have dot product ten. Their difference has squared norm sixteen.

The [rooted distance and sign argument](../short-shell-moments.md#bounding-the-norm-18-alternative) leaves only nine and ten for the dot product, with no opposite-sign intersections. Suppose it is nine. The common part $C$ consists exactly of the nine specified sites. The exclusive parts $T,V$ also have nine sites each. The difference is a third norm-18 vector. By the [small-support theorem](../../short-support-packing/README.md), all three supports induce 4-regular bipartite graphs, with parts given by signs. Color the sites of $C$ by the original signs and the sites of $T,V$ by the reversed original signs. Each panel has five sites of the first color and four of the second. Internal edges change color and cross-panel edges preserve it. At a site with internal degree $d$, exactly $4-d$ edges go to each other panel.

In $C$ the only edges are the four edges from $o$ and both parent edges of each designated label. Up to relabeling $Q$, the two omitted pairs meet or are disjoint. To enumerate $C\cup T$, each designated label gets two of the five remaining negatives, and the root gets none. Each remaining positive can see no parent, a single parent, or an omitted pair. This follows from the common-neighbor bound with $o$ and the uniqueness of the second common neighbor of a parent pair. Fill the remaining $5\times4$ incidence matrix with the degrees required for a 4-regular support. Sorting equal contact masks and permuting equal columns exhaust the freedom to reorder the exclusive sites. For two such charts the two cross-panel matrices between $T,V$ have prescribed row and column sums $4-d$. Trying all binary rows exhausts the gluing. At any stage a pair exceeding its allowed number of common neighbors can be discarded. The [degree enumeration](direct_charts.py) and [catalogue-based enumeration](enumerate_cores.py) use different constructions of the one-support charts and compare the colored canonical forms of the glued inputs with the archive.

| Omitted pairs | Charts | Gluings | Distinct cores | Integer separator | DRAT refutation |
|---|---:|---:|---:|---:|---:|
| Meet | 434 | 2,463 | 1,578 | 1,550 | 28 |
| Disjoint | 616 | 19,416 | 4,487 | 4,313 | 174 |

For an exterior site its contact set $w$ must have equal signed balances in $C,T,V$ by the eigenvector equations. It cannot contain both ends of a pair whose remaining common-neighbor quota is zero. Its intersection with any closed core neighborhood has size at most two, since a neighbor of the exterior site is allowed one common neighbor and a nonneighbor two. Enumerating cliques of pairs with positive quota includes all such $w$, including the empty set. A column records one site, its incident vertices, and its incident pairs. The target $b$ records 72 sites, the missing degrees and the missing common-neighbor counts. Any completion supplies nonnegative integer multiplicities with $Mx=b$. The [exact verifier](exact_overlap.py) checks $M^ty\ge0>b^ty$ over the integers in 5,863 cases. In the other 202 cases, two exterior sites sharing any triple would have three common neighbors. Encode the degree and pair equalities and these triple inequalities, allowing the site total to vary. The verifier regenerates an unsatisfiability proof for each relaxed system and passes it to an independent DRAT checker. This excludes dot product nine.

## Counting windows

For a fixed $o,Q$ let $I$ be the number of independent four-subsets of the six labels. Split their induced edges into $j$ joining pairs with a shared parent and $k$ joining disjoint pairs. Each parent neighborhood is a matching, so it contributes at most one transition to $j$. The [integer count](packing.py) tries the four possible choices at each of the four parents and all eight subsets of the three opposite pairs. After the common-neighbor upper bounds on the eleven vertices, every case satisfies
$$9(15-I)\ge5(j+8k).$$

There are $560=\binom74 2^4$ choices of $Q$ per root. If $P_o$ counts triangular prisms through $o$, then $\sum_Q j=8(84-P_o)$ by the [rooted transition count](../../short-support-packing/README.md). For the other edge count, the 84 vertices at distance two from $o$ induce a 12-regular graph. Among its 504 edges, 84 share a parent, leaving 420 with disjoint parent sets. For each of the seven mate pairs $a,b$ in the neighborhood of $o$, the twelve distance-two sites adjacent to $a$ and the twelve adjacent to $b$ are disjoint and are paired by a perfect matching. Indeed each vertex $x$ in the first set shares $a$ with $b$, and its other common neighbor with $b$ is a distance-two neighbor of $b$. It cannot be another neighbor of $o$ because $b$'s only neighbor there is $a$. Thus there are 84 bad incidences in total from matching across mate groups. Of these, $P_o$ already have a shared parent, by the same rooted prism bijection. At least $336+P_o$ of the 420 edges avoid every bad incidence. Each has four parents in distinct mate groups and appears once in $k$. Summing gives $\sum_{o,Q}(j+8k)\ge8\cdot99\cdot420$ and $\sum I\le646800$.

In the absence of norm-16 vectors each window holds at most one vector, and each oriented vector occurs in at least nine windows. Thus **$N_{18}\le71866$ whenever $N_{16}=0$**.

For the general bound fix an oriented norm-16 difference $f=1_P-1_N$, with eight sites on each side. Outside the support write $h(x)$ for its number of neighbors of either sign. On $P$ put a multigraph $D$ with pair multiplicities two minus the number of their common neighbors in $N$. Its degrees are $14-4\cdot3=2$. With $B$ the $P$-by-$N$ incidence matrix one has $BB^t=2J+2I-D$. On any component of size $s$, $B^t1_S$ has sum $4s$ and squared norm $2s^2$, giving equality in Cauchy–Schwarz on eight entries. Every entry is $s/2$, so each component has even size. An exterior site touching three positives would use a triangle in $D$ and exhaust its degrees in an odd component. Hence $h\le2$. The exterior has 80 incidences with $P$ and supplies eight pair coincidences. There are exactly eleven sites of height zero, 64 of height one and eight of height two.

In each occupied window choose one reference marking. Each other marking supplies a difference of norm 16 from the reference, and distinct markings give distinct unoriented difference pairs because two opposite increments of the same nonzero length cannot both stay on the sphere centered at zero from the same reference. For a fixed difference, $o$ misses its entire support and the heights at the 14 neighbors of $o$ sum to sixteen, by counting the two common neighbors of $o$ with each positive of $f$. For a parent $q\in Q$, let $d_q$ count the two omitted pairs incident with it. Among the four positive neighbors in each marking the common ones include $o$ and $3-d_q$ specified labels. Only one more site is shared anywhere since the dot product is ten. Consequently $h(q)=d_q-\epsilon_q$ with $\epsilon_q\in\{0,1\}$ and $\sum\epsilon_q\le2$. A further common positive cannot neighbor $o$, so it sees at most two parents. The [count over the seven mate pairs](packing.py) gives at most 904 choices of $Q$ and omissions for each zero-height root, even allowing all height assignments of total sixteen with at most eight twos. There are eleven possible roots and $N_{16}/2$ difference pairs. It follows that
$$9N_{18}\le646800+11\cdot904\,N_{16}/2.$$

## Every oriented norm-16 vector gives a different unit labeling of type (1,27)

Let $X,Z$ be the eight exterior double sites and the eleven exterior zero sites above. Set
$$b=A1_P-3\,1_N-\mathbf1=1_X-1_{P\cup Z}.$$
Its squared norm is 27. Applying $A^2=12I-A+2J$ and $A(1_P-1_N)=-4(1_P-1_N)$ gives $Ab=-4b-2\mathbf1$.

Suppose two oriented inputs give the same $b$. Then $X$ and $B_0=P\cup Z=P'\cup Z'$ agree. All of $P\cup P'$ is isolated inside $B_0$, and both negative sides are disjoint from $B_0$. Write $c=|P\cap P'|$ and $d=|N\cap N'|$. Squaring $A(1_P-1_{P'})=3(1_N-1_{N'})$ gives $12(16-2c)=9(16-2d)$. The possible pairs are $(8,8),(5,4),(2,0)$. The first gives identical inputs. The second gives squared distance fourteen, excluded by the [norm-16 distance bound](../norm16-packing.md).

In the last case every vertex of $N$ sees exactly one member of $P'$, necessarily in $P\cap P'$ because $P'\setminus P\subset Z$. The two common positives thus have no common neighbor in $N$. Both of their common neighbors are exterior sites in $X$. Each of these two double sites sees only the two shared positives in $P\cup P'$, by applying the height rule to each input. At $x\in X$ the equation for $b$ requires $6+|N(x)\cap X|$ neighbors in $B_0$. Each of the two double sites must therefore see at least four of the same five sites in $B_0\setminus(P\cup P')$. This violates the common-neighbor bound. The map is injective and **$U_{1,27}\ge N_{16}$**.

## Consequences for short labelings

Use the twelve unit types of the [second-moment argument](../short-shell-moments.md#when-the-nonzero-labels-must-all-be-signed-units). The injection rules out the pair $N_{16},N_{18}$ as the only two types at any rank. The [higher-degree identity](higher-moments.md) also excludes the pair $N_{18},U_{1,25}$.

At rank 36 remove any two of the twelve types. At least **113 oriented labelings** of the other ten must occur, or **8,407** if $N_{16}=0$. For the calculation, average the seven original moment equations over maximal extensions, use the four established subtractions for nonunit entries, and add the two inequalities above. On the twelve types the normalized population is the graph count divided by $p=2402$. The other bounds used are $W_{0,0}=1$, $0\le W_{0,14}\le4$, $W_{1,23}\ge99$, $N_{16}\le6930$, $N_{18}\le289520$. For each of the 66 pairs the [rational dual verifier](packing.py) checks a lower bound on the sum of the other ten populations, multiplying back by $p$. The smallest certified values before rounding in the two runs are $640164/5669$ and $8407$.

For another local consequence, let $1_P-1_N$ have squared norm eighteen. Then $s=\mathbf1+3\,1_N-A1_P$ has charge zero and squared norm 36 by the same adjacency identity. It is one on $P$, zero on $N$, and $1-h$ off support. An exterior height of at least four would give a charge-one vector $s+d_i$ of squared norm at most 17, where $d_i=3e_i-Ae_i$. This is excluded. Two adjacent sites of height three give $s+d_i+d_j$ of charge two and squared norm sixteen, also excluded. If two height-three sites are nonadjacent the resulting squared norm is thirty. It has only unit entries by the short-shell classification, so a third height-three site, nonadjacent to both, is impossible. In particular in the remaining two-type case there is at most one site of height three. If it occurs, it cannot neighbor a height-two site since that pair again gives a charge-two vector of squared norm thirty.

The [height-three counting argument](height-three.md) strengthens the last two restrictions to every norm-18 marking, at every rank and for every short-labeling population.

## Replay

From this directory run the following with Python, pynauty, python-sat, python-flint and a compiled drat-trim. The last three commands also use nauty's genbg. The original numerical search is unnecessary.

```sh
python direct_charts.py
python exact_overlap.py /path/to/drat-trim
python packing.py
python higher_moments.py
python forced_pair.py --genbg /path/to/genbg
python one_panel.py --genbg /path/to/genbg --drat-trim /path/to/drat-trim
python high_contact_search.py --genbg /path/to/genbg --drat-trim /path/to/drat-trim
```
