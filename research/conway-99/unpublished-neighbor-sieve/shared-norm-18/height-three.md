# An unconditional restriction around every norm-18 eigenvector

Let $A$ be the adjacency matrix of a hypothetical strongly regular graph with parameters $(99,14,1,2)$. For any integral $-4$ eigenvector of squared norm 18, write $P,N$ for its nine positive and nine negative sites. Its support induces a 4-regular bipartite graph on these two sides. For an exterior vertex $y$, let $h(y)$ be its number of neighbors in $P$, equivalently in $N$. The same reasoning applies to any induced 4-regular bipartite subgraph on two sides of nine. Its signed indicator $t$ has $At=-4t$ on the support. The identity $A^2=12I-A+2J$ gives $\|At\|^2=16\|t\|^2$, so $At$ vanishes off the support.

**Theorem.** There is at most one exterior vertex of height three. If it exists, its neighbors consist of six support sites, five exterior sites of height zero and three of height one. Its six support neighbors form three disjoint edges. This applies at every remaining rank and for every population of short labelings.

First, $h\le3$. If an exterior vertex saw four positives, their four neighbor sets in $N$ would each have size four. Any two sets meet in at most one site because their positives already share the exterior vertex. Their union would have at least $4\cdot4-\binom42=10$ sites in $N$, which has size nine.

Let $H_i$ count the exterior sites of height $i$. There are 81 exterior sites and $9(14-4)=90$ exterior incidences with $P$. The pairs in $P$ have $2\binom92$ common-neighbor incidences, of which $9\binom42$ occur in $N$. Thus
$$
\sum H_i=81,\quad \sum iH_i=90,\quad \sum \binom i2 H_i=18.
$$
Writing $m=H_3$ gives $(H_0,H_1,H_2,H_3)=(9-m,54+3m,18-3m,m)$.

For exterior $y$ of height $h$, counting two-step walks from $y$ to $P$ gives $18-h$ walks. Exactly $4h$ have their middle vertex in the support. Consequently the $14-2h$ exterior neighbors of $y$ have total height $18-5h$.

A height-three site has eight exterior neighbors of total height three, at least five of them zeros. If there were two such sites, the whole graph would have at most seven exterior zeros. Two sets of five zeros would share at least three, contradicting the common-neighbor bound. Hence $m\le1$.

Suppose the unique height-three site $x$ neighbors a height-two site $y$. The other seven exterior neighbors of $x$ then have total height one, so six are zeros. The site $y$ has ten exterior neighbors of total height eight. After its neighbor $x$ uses three, the other nine have total height five and must include at least four zeros. There are only eight zeros. Hence the adjacent pair $x,y$ has at least $6+4-8=2$ common zero neighbors, although its quota is one. It follows that the eight exterior neighbors of $x$ have heights $0,0,0,0,0,1,1,1$.

Finally, each of the three positive neighbors of $x$ has four neighbors in $N$. Two of these positives share $x$ and hence have at most one common neighbor in $N$. Their three four-element neighbor sets cover at least $12-3=9$ sites, so they cover $N$. In particular each negative neighbor of $x$ sees one of these positives. An edge incident with $x$ can have only one common neighbor, so these contacts are a perfect matching on the six support neighbors. Each height-one neighbor of $x$ therefore has both its support contacts among the other twelve support sites.

There is also a direct way to locate all three height-one neighbors. Among the six sites of $P$ outside the neighborhood of $x$, three see two of the three negative neighbors of $x$, and three see one. Indeed those three negative neighbors have twelve incidences with $P$ and cover all nine sites, their three pairwise intersections are singletons, and none is a triple intersection. The three positive neighbors of $x$ each receive just one incidence in the perfect matching. A remaining positive receiving two incidences already has both common neighbors with $x$. Each receiving one must get its second common neighbor via a height-one neighbor of $x$. Each such neighbor sees only one positive. The same holds on the negative side. The three height-one sites therefore give a bijection between the three designated positives and the three designated negatives. Once the support and the six neighbors of $x$ are known, there are at most six choices for all their support contacts together.

The exterior height census is exactly $(9,54,18,0)$ or $(8,57,15,1)$. Both the height-three budget and the forbidden height-three to height-two adjacency can consequently be used without the two-type hypothesis in any future completion test. The theorem leaves open whether either census is realizable in a 99-vertex graph.

## A different norm-36 marking for each oriented norm-18 marking

There is an injective map on the fixed graph from oriented norm-18 eigenvectors to integral norm-36 eigenvectors. For $t=1_P-1_N$ take
$$s(t)=\mathbf1+3\,1_N-A1_P.$$
The adjacency identity $A^2=12I-A+2J$ and $At=-4t$ give $As=-4s$. The values of $s$ are one on $P$, zero on $N$ and $1-h$ off the support. Either exterior census gives $s^ts=36$.

Suppose $s(t)=s(t')$ and write $c=|P\cap P'|$, $d=|N\cap N'|$. The positive sites of $s$ are $P$ together with the exterior zeros of $t$. Thus every site in $P'\setminus P$ misses both $P$ and $N$. In particular $P\cup P'$ is independent. From
$$A(1_P-1_{P'})=3(1_N-1_{N'})$$
take squared norms. The vector on which $A$ acts has sum zero and is supported on an independent set, so $12(18-2c)=9(18-2d)$. The possibilities are $(9,9),(6,5),(3,1)$.

Each common negative must have all four of its positive neighbors in $P\cap P'$, since it lies in $N$ and misses $P'\setminus P$. This excludes $(3,1)$. At $(6,5)$ the five common negatives give five four-subsets of the six common positives. Any two must meet in at most two sites. Their two-element complements must therefore be pairwise disjoint, which is impossible on six sites. Only identical inputs remain.

If $M_0,M_1$ count the oriented inputs with zero and one height-three sites respectively, this map gives at least $M_0$ **unit** norm-36 vectors. It gives at least $2M_1$ **nonunit** oriented norm-36 vectors: each image from this case has exactly one entry $-2$, while its negative has an entry $+2$ and cannot be another image. In particular $N_{36}\ge N_{18}+M_1$.

For a unit affine consequence, when $x$ is the height-three site put $b=s+3e_x-Ae_x$. Then $Ab=-4b-2\mathbf1$. Its positive sites are $x$, the six positives of $t$ missing $x$, and the three exterior zeros missing $x$. Its negatives are the fifteen height-two sites, the three negative neighbors of $x$ in the support, and its three height-one neighbors. It is a unit vector of squared norm 31. Given $b$ and $x$, subtraction recovers $s$ and hence at most one oriented $t$. As $b$ has ten positives, at most ten inputs give any one $b$. With $U_{a,t}$ denoting the unit counts at charge $a$ and squared norm $t$, every rank therefore satisfies
$$U_{0,36}+10U_{1,31}\ge N_{18}.$$
