# Excluding four orthogonal Fano configurations

**Theorem.** A Conway 99-graph has at most three pairwise orthogonal signed Fano eigenvectors up to sign. In particular, every integral marked extension in the determinant-49 reduction has at most three antipodal root pairs, simultaneously for Seidel ranks 36, 38, 40 and 42. At rank 42 the graph has at most six oriented norm-14 vectors.

We use the [marked-coset intersection theorem](../marked-coset-shells/README.md). Its orthogonal-pair argument applies to signed Fano vectors whenever their ordinary dot product vanishes. Each Fano configuration has two sign sides of seven points and an independent set $Y_i$ of fifteen points seeing neither side. Its two independent 22-sets are obtained by adding either side to $Y_i$. Across two orthogonal configurations all four endpoint intersections have size one. More precisely, either endpoint of the second configuration contains one site from each sign side of the first and none from $Y_i$, by the intersection formula in that theorem. Applying this in both directions shows that the two fifteen-sets are disjoint and each is disjoint from the other configuration's sign sides. Each of the four signed side intersections is a single site.

For one configuration, every site outside $Y_i$ and its two sides sees one site of each sign and three sites of $Y_i$. The last count follows by applying the 22-set neighbor equation to an endpoint. Sites on a sign side see four sites on the opposite side and none of $Y_i$. Each point of $Y_i$ sees no sign sites in its own configuration.

## The remaining 39 sites

Suppose there are four configurations. Remove their disjoint fifteen-sets, leaving a set $W$ of 39 sites. A site of $Y_i$ lies outside the other three configurations and their fifteen-sets. It therefore sees three vertices in each of the other fifteen-sets and has five neighbors in $W$. Those five neighbors carry six sign memberships in total, one of each sign in each of the three other configurations.

For $x\in W$, let $s(x)$ be the number of sign sides containing it. It has $2+3s(x)$ neighbors in $W$, by counting its neighbors in the four fifteen-sets. Write $m_j=|\{x:s(x)=j\}|$. Counting sites, side incidences, and pairwise signed-side intersections gives
$$\sum m_j=39,\qquad\sum j m_j=56,\qquad\sum \binom j2 m_j=24.$$
In particular $m_0+m_3+3m_4=7$. If $m_0=0$, the five neighbors in $W$ of each site in a fifteen-set carry six memberships, so none of them can have three memberships. Every site carrying three would see three vertices of the omitted fifteen-set. Thus $m_3=0$, contradicting $3m_4=7$.

A site $o$ with zero memberships sees two neighbors in $W$ and one vertex of every signed side. Those two neighbors $a,b$ must belong to all four configurations with opposite signs. Orient all signs so $a$ is positive. No third fourfold site exists, since sharing two signs with $a$ or with $b$ would repeat a signed-side intersection. Thus $m_4=2,m_0=1,m_3=0$. The twelve twofold sites are exactly $d_{ij}$ for $i\ne j$, with signs $+i,-j$. Each signed side has three further sites, all singletons. The fourteen possible neighbors of $a$ in $W$ are precisely $o,b$ and the twelve negative singletons, so it sees them all. The analogous statement holds at $b$.

## Labeling the singletons

The neighborhood of $a$ induces a perfect matching. The sites $o,b$ are paired, so each negative singleton of group $i$ is paired to another negative singleton of a different group $j$. A negative singleton has five neighbors in $W$. Four must carry $+i$, including $a$. Its paired negative singleton supplies the fifth. In every group other than $i$, the positive-sign requirement is already met at $a$. The negative requirement in group $j$ is met by its mate. It follows that the remaining three neighbors are one positive singleton of group $i$ and the two doubles $d_{ik}$ with $k\notin\{i,j\}$.

For each $j\ne i$ exactly one negative singleton in group $i$ has its mate in group $j$. Indeed $a$ and $d_{ij}$ are both positive in group $i$, so they have exactly two common neighbors on its negative side. The site $d_{ij}$ does not see $b$, because it shares the negative sign $j$ with $b$. Its two common neighbors with $a$ on the negative side of $i$ are therefore exactly two of the three negative singletons of $i$. By the preceding paragraph it misses precisely those with mate in group $j$. This gives the labels $n_{ij}$ with mate $n_{ji}$. Interchanging signs gives $p_{ij}$ with mate $p_{ji}$. The remaining edges between opposite singletons in each group form a perfect matching, written $p_{ij}\sim n_{i,\pi_i(j)}$. There are $(3!)^4=1296$ choices for the four permutations.

## Finite completion

For each choice, the only unspecified edges in $W$ are between doubles. Every double already has four singleton neighbors and needs four double neighbors. For each double the checker tries every four-subset of the other doubles sharing no sign with it. It imposes the sign-side neighbor counts and the two common neighbors with each same-side singleton. Both common neighbors of such a pair lie in the opposite sign side, inside $W$. Retaining symmetric choices produces four graphs. Testing the graph-wide common-neighbor upper bounds on all pairs inside $W$ leaves exactly one, with all four permutations equal to the identity.

Fix $v=d_{01}$ in this last graph. It has three neighbors in each of $Y_2,Y_3$ and none in $Y_0,Y_1$. A neighbor in $Y_i$ has a five-subset $B$ of neighbors in $W$, containing $v$. Enumerate these subsets with their label $i$. They avoid both signs of $i$ and cover all six other signed sides exactly once. Every pair $x,y\in B$ needs room for one more common neighbor beyond those already in $W$. Also the vertex in $Y_i$ and each $x\in W$ have at most $2-\mathbf1_{x\in B}$ common neighbors already in $W$. These conditions leave 70 candidate labeled blocks.

For every $x\in W\setminus\{v\}$ the required number of selected blocks containing $x$ is exactly
$$2-\mathbf1_{x\sim v}-|N_W(x)\cap N_W(v)|.$$
Repeated blocks are impossible since two vertices have at most two common neighbors. Selecting six distinct candidates with the prescribed counts and group sizes gives 3,841 choices. In every choice two of the blocks intersect in at least three sites, which violates that same common-neighbor bound. Thus $v$ has no completion.

Run `python3 verify.py` in this directory to reproduce both exhaustive enumerations with integer arithmetic. The final search branches on a positive outstanding count, tries each still eligible block covering it in order, and removes earlier choices from subsequent branches to count each unordered selection once. This excludes the four-pair case. Configurations with fewer root pairs, including zero, still require an existence or nonexistence argument.
