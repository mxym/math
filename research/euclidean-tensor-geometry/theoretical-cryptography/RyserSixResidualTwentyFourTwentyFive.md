# Two-vertex residual bound and degree caps at 24–25 edges for rank-six Ryser candidates

Let $H$ be a finite intersecting six-partite six-uniform hypergraph with covering number six, with distinct edges. If $H$ has at most 25 edges, then **every two vertices leave at least nine edges uncovered**. If $H$ has exactly 24 edges its maximum degree is at most **nine**; if it has exactly 25 edges its maximum degree is at most **eleven**.

This is a follow-up to the [24-edge lower bound, DOI 10.5281/zenodo.24615440](https://doi.org/10.5281/zenodo.24615440) ([fixed proof](RyserSixTwentyFourEdges.md)). It restricts hypothetical 24- and 25-edge candidates, without ruling out either order. The new residual and repeated-star arguments came from the research Dreamer; the degree profiles and the last obstruction were independently reproduced here.

## 1. The two-vertex bound

Each original part has at least six active vertices, since a part is a cover. Each active vertex has degree at least two: if a vertex belonged only to one edge, deleting it from that edge would leave a five-element cover.

Let $J$ be the residual family after deleting all edges through the two selected vertices. Its cover number is at least four. At most six intersecting edges can be covered by three vertices by pairing edges (with a single vertex for any leftover edge). For seven edges, a degree-three vertex leaves at most four edges, also giving a three-cover. If every degree is at most two, the six parts together can supply at most $6\lfloor7/2\rfloor=18$ intersecting edge pairs, less than $\binom72=21$. Thus seven or fewer residual edges are impossible.

If exactly eight remain, pairing gives cover number exactly four. By [Abu-Khazneh–Pokrovskiy, Lemma 2.8](https://arxiv.org/abs/1409.4938), there is one triple block in every part of this residual family (the blocks group the edge rows by their common vertex in that part), and there are at least eleven double blocks in all. At most two double blocks fit in a part, because eight edge rows include a triple. Hence five parts have block sizes $3,2,2,1$ and the sixth has at least one double block; it has at most five active vertices since a triple and a double use five rows. At least $5\cdot2+1=11$ original active vertices are absent from $J$. Excluding the two selected vertices still leaves at least nine further vertices, each with at least two incidences in the removed edges.

Every removed edge meets every edge of $J$, so its vertices present in $J$ form a cover of $J$ of size at least four. It also contains at least one of the two selected vertices, which are absent from $J$. Thus it contains at most one of the nine further missing vertices. This requires at least 18 removed edges, whereas at most $25-8=17$ could have been removed. This proves the bound.

## 2. The one-star residual profiles

Delete all edges through an active vertex $x$ and write $m=|E(H)|-d(x)$ for the number remaining in $J$. Its cover number is at least five, so $m\ge13$ by [Aharoni–Barát–Wanless, Theorem 2.7](https://arxiv.org/abs/1409.4833). Each removed edge consists of $x$ plus a five-cover of $J$: its other five vertices must meet all residual edges, so all five must be active in $J$. Hence the active vertex set of $J$ contains all active vertices of $H$ except $x$. Its part sizes are at least 5 in the part of $x$ and at least 6 in each other part.

A five-cover of $J$ contains at most one degree-one vertex of $J$: if two such vertices occur, replace them by one vertex at the intersection of their unique edges (or just delete one if their unique edges coincide). This would yield a four-cover. Every singleton of $J$ was present in at least one removed edge, since its original degree was at least two. It follows that $J$ has at most $d(x)$ degree-one vertices across all parts.

By Section 1, the largest degree of a vertex in $J$ is at most $m-9$ (apply the two-vertex bound to $x$ and that vertex). In a part of $J$ the sums of the two, three, or four largest degrees are at most $m-5,m-3,m-1$ respectively. The stars of vertices in a part are disjoint, and violating any bound lets one cover the remaining edges by pairing as needed to give a four-cover. These constraints apply independently of any upper bounds on the original part sizes.

For each residual part enumerate sorted positive integer degree lists of sum $m$ with those size and largest-degree conditions. Record its number of degree-one vertices, its contribution to $S=\sum_v\binom{d_J(v)}2$, and its number of degree-five vertices. Add these records for the six parts, keeping the singleton total at most $|E(H)|-m$. Since $J$ is intersecting, $S\ge\binom m2$. The independent integer verifier gives the following full relevant profile outputs:
\[
\begin{array}{c|c|l}
 |E(H)| & m & \text{profile constraint}\\\hline
 24&13&S\le71<78\\
 25&13&S\le73<78\\
 24&14&(S-91,t)\in\{(0,4),(0,5),(0,6),(1,5),(1,6),(2,6),(3,6)\},
\end{array}
\]
where $t$ is the total number of degree-five vertices. This already yields the cap eleven at order 25. At order 24 it remains only to eliminate $m=14$.

## 3. Repeated degree-five star pairs

Assume $m=14$, and put $E=S-91\ge0$. Any two degree-five stars meet, or their ten covered edges and two intersections of the remaining four would give a four-cover. Any three degree-five vertices must include a pair of codegree at least two: if their pairwise codegrees were all one, their three stars would cover at least $15-3=12$ edges, and the remaining pair could be covered by one vertex. Thus the graph on the $t$ degree-five vertices joining pairs of codegree one is triangle-free. By Mantel's bound there are at least $\binom t2-\lfloor t^2/4\rfloor$ repeated pairs, namely $2,4,6$ at $t=4,5,6$.

For each pair of residual edges write $s$ for their intersection size. Then $E=\sum_{\text{edge pairs}}(s-1)$. Counting common pairs of vertices and applying the convex inequality for the nonnegative $s-1$ gives
\[
 \#\{\text{repeated vertex pairs}\}
 \ \le\ \sum_{\text{edge pairs}}\binom{s}{2}
 \ \le\ \binom{E+1}{2}.
\]
The first inequality follows because a repeated pair lies in at least one pair of residual edges. For the second use $\binom{a+1}{2}+\binom{b+1}{2}\le\binom{a+b+1}{2}$, strictly if $a,b>0$.

Of the seven possible profiles the only one surviving these two bounds is $E=3,t=6$. Equality would force a single pair of residual edges meeting in four vertices, so all six repeated pairs could use only those four vertices. Among the six degree-five vertices, at least two are outside that four-vertex set. Those two and any third degree-five vertex form a triple with no repeated pair, contradicting the necessary condition. Thus $m\ge15$ at order 24, and $d(x)\le9$ for every $x$.

**Replay.** `python3 -O verify_ryser_six_residual_twenty_four.py` independently enumerates all degree-profile totals and verifies the small repeated-pair obstruction by exact integer pair and triple enumeration.
