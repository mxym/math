# No fully nice pure-rich triangle; the 1,602 endpoint is impossible

In a strongly regular graph with parameters (99,14,1,2), write n₃ for the number of unordered pairs of disjoint triangles joined by exactly two edges. Then **n₃ ≥ 1605**. Equivalently using Reimbayev's [induced-hexagon identity](https://ejaam.org/articles/2024/10.62780-ejaam-2024-001.pdf), there are at least **210,891 induced hexagons**. Existence or nonexistence of the graph remains unresolved. The proof uses no global symmetry assumption.

The stronger structural assertion is that no triangle T can have all three points nice, three or four incident rook grids (b_T=3,4), and exactly 2b_T prism partners. Here a point is *nice* when every square at the point lies in a triangular prism and no induced three-center motif H is centered at that point. The nine vertices of H consist of three independent centers, with two private independent common neighbors for each center pair and no other edges. Write g for the total number of rook grids (induced 3-by-3 rook graphs). In particular there are at most 9g/10 nice points: each nice point is on at least four pure-rich lines and at least two other full lines (with at least one grid). At most two nice points lie on a pure-rich line and at most three on a full line; hence 6g≥3·4s/2+2s/3 for s nice points.

## Prerequisites and normalization

The previously checked [five-diagram and line reduction](../nice-triangle/Theorem.md) forces such a triangle T if n₃=1602. Its local diagram classification and construction of T's 39-vertex shell given an all-nice pure-rich T are not themselves restricted to that endpoint. The [next exclusion](../four-grid-shell/Theorem.md) rules out b=4 and the eight- and eleven-arc local diagrams at any nice point. We only need b=3. The [covered-point flow lemma](../covered-root/Theorem.md) describes the necessary ternary rows used below. Finally the [positive identity](../../order-nine-flags/README.md) gives n₃ ≥ 1602 and 3 ∣ n₃; excluding equality yields the numerical statement above.

The shell is T=(0,1,2) together with T_i's twelve other neighbors, the points of wing i. In each wing label matched pairs 0,...,5, with local signed site 2a+s. Pairs 3,4,5 are the three fixed grids. The transfer matching from wing 0 to 1 and from 1 to 2 preserves labels. From 2 to 0 it preserves fixed labels; it sends defect pair a to a+1 mod 3, preserving its sign except for the step 2→0 of the defect-pair labels, where either sign choice is possible. These two twists exhaust the shell by the line reduction.

At each root o=T_i the triangle T is axis 6; its six wing pairs are axes 0,...,5. It is a pure source of outdegree 3 (indeed p_T=6, b_T=3). The ten-arc diagram has its pure sources of outdegree 2 and its sinks of outdegree 0, so is impossible here. The twelve- and fourteen-arc diagrams each have every source from {6,3,4,5} pointing to the defect set {0,1,2}. In the fourteen-arc diagram one distinguished defect j also points to the other two defects. The local assignment sp_i is 0 in the former case or 1+j in the latter.

Thus per twist there are 4³=64 labeled assignments. Index the nine defect-pair sites by position 3a+i. Their transfer edges form C9. Its rotations/reflections x↦±x+c, c=0,...,8, lift to actual relabelings of the shell. Explicitly in the untwisted case apply the map mod 9 separately to either sign cycle; in the twisted case use the same map mod 18 on the one cycle, whose opposite sites are mates. Permute the three T-points accordingly and transport the fixed pairs by the wing permutation. The checker explicitly validates all 18 permutations on all 39 neighborhoods in each twist. The eight orbits have representatives 000,001,011,012,013,111,112,121; the first has size one and the rest size nine. A separate 48-element group permutes the three fixed-pair names and flips their signs simultaneously in all three wings. Nothing here presumes that a labeling symmetry extends to the 99-vertex graph.

## The 60 physical words

Each of the 60 points y outside the shell has exactly two contacts in each wing, as y is nonadjacent to its T-point, with no T-contact. Those contacts cannot be mates, whose unique common neighbor is their T-point. Conversely each of the 60 choices of a nonmated signed pair in one wing has exactly one far common neighbor: it has exactly one shell common neighbor (the T-point), as is also verified in the displayed shell. Accordingly a candidate word is a sextuple of signed shell sites, grouped as three sorted nonmate pairs. Every chosen word occurs once or not at all (variable $0\le x_f\le1$); each prescribed pair in any one wing occurs exactly once. For sites p,q in different wings let
$r_{pq}=2-D_{pq}-(D^2)_{pq}$, with D the 39-shell adjacency. Exactly r of the chosen words contain both sites.

The independent generator starts with all 60³ words and rejects only these violations:
1. Two distinct selected sites have already exhausted their common-neighbor budget in the shell (r≤0).
2. A selected site is adjacent to at least two other selected sites. The edge between it and y would have at least two common neighbors.
3. A fixed grid pair has not been hit exactly once across the three wings. A rook grid is one-dominating off itself (its indicator satisfies (A−3I)χ=1), and y does not touch T.

Exactly 12,096 words survive in either twist at this stage. The following state filters remove additional impossible words independently at each of the three roots.

## Root states tied to physical points

Relative to o=T_i the exterior is 24 **known** shell points (the other two wings) and the 60 **unknown** far points. Each exterior p lies in a four-cell C_h indexed by its pair h of parent axes. Its two signed parents are known from shell adjacency or its word. If h contains axis 6, its four members are known shell vertices. Otherwise p is far and the local word pair in wing i identifies its two signed parents and its cell.

For each exterior p the covered-point flow lemma supplies a row w on the 21 unordered axis pairs (zero on clean pairs, ternary on dirty arcs). At each source/target copy of an axis the sum of its incident w is zero. In its own dirty cell h, w_h=−1. On any other incident dirty arc a value ≥0 is allowed if h is dirty and shares a same-role endpoint; otherwise it is zero. For completeness the replay generates *all* solutions of these restrictions by iterating independent ternary choices of zero sum at each source, then checking the target sums. Columns at pairs disjoint from h are restricted only by these rules.

The exterior degree of p into C_f and the number of its two signed-parent triangle partners in C_f are, respectively,
[
 k_f(p)=2[h=f]+[h\cap f=\varnothing]+w_f(p),
]
and $j_f(p)=2$ or 1 for f=h in a clean or dirty cell, respectively. For f≠h it is $w_f(p)$ if f and h are dirty with the same head, and zero otherwise. These are the previously proved pointwise formulas, not sufficiency assumptions. At each physical point retain only rows whose six degrees into C_{6,a} agree exactly with the known physical contacts. If p is far, its signed parent on each tail of its own dirty h, or on either axis if h is clean, has its unique triangle partner with p **in the same far cell** (the prescribed internal flip). Thus reject this word if any selected shell neighbor of p is itself adjacent to that signed parent. This is the only further local word rejection; a word having an empty state fiber at any root can of course be discarded.

Write $y_{i,p,w}\in[0,1]$ for the physical point occurrence in state w at root i. The total over w is 1 for a known shell point p and is $x_p$ for a possible far word. Actual graphs give 0/1 solutions; the proof uses only these real bounded relaxation constraints.

## Pointwise degree and motif coverage

For a known shell exterior point p its adjacency to every exterior candidate q at its root is known: shell-shell adjacency D in the first case, membership of p in the word q in the second. For each far cell f require (all quantities weighted by their corresponding physical state variables):
[
 \sum_{q\sim p}[q\in C_f] = k_f(p).
]
On the left each state of q weighs the indicator; on the right sum over the states of p. This is just the definition of its degree into f.

Further, if f is disjoint from p's own axis pair, the four points of C_f must all be accounted for, giving
[
 4\;\le\;\sum_{q\sim p}\left([q\in C_f]+j_f(q)+
 [p,q\text{ share a signed parent}]\,k_f(q)\right).
]
Indeed count a candidate z∈C_f. If z is adjacent to p, q=z gives the first term. Otherwise o,p,z have private, disjoint pairs of common neighbors: the two pairs of signed parents and the two common neighbors of p,z, both exterior. No edges among them apart from those to the centers can occur unless one of the latter two meets one of the four signed parents (the two common neighbors are independent by λ=1; the four parents are independent since the axes are disjoint). As o is nice the induced H is forbidden, hence some such contact exists. If its witness q is adjacent to a signed parent of z then z is one of the $j_f(q)$ triangle partners in C_f; if adjacent to a signed parent of p, q and p share a signed parent and z is one of the $k_f(q)$ neighbors of q in C_f. This covers all four z. Witnesses may be counted more than once, as only an upper estimate for the number covered is used.

No global flow moments, eigenspace equations, aggregate motif quotas, matching nonisometry restrictions or far-far adjacency variables are needed in this final system. Its feasibility would not be sufficient for a graph.

## Integer replay

The preceding constraints are closed under the 48 signed relabelings of the fixed pairs. A graph solution would give, on averaging the relabeled solutions, a solution constant on the orbits of words and pairs (physical point, row-state), with variables still in [0,1]. This permits summing the integer coefficients of each linear row within each **variable** orbit, retaining that row's original right-hand side. On far-word normalization rows one representative per orbit suffices; all pointwise constraints are generated, then identical rows deduplicated.

The result has form $Az=b, Uz\le q, 0\le z\le1$. For signed integral u and nonpositive integral v an infeasibility proof is
[
 u b+v q-\sum_j\max(0,(uA+vU)_j)>0.
]
Indeed any feasible z gives $ub+vq\le (uA+vU)z\le\sum_j\max(0,(uA+vU)_j)$. The small certificate files name the exact individual constraints and give their integer multipliers. The checker builds the actual shell, states and incidence relations independently from their definitions, using integer arrays and Python arbitrary-precision accumulation for the final separator. No search solver or floating-point comparisons are used by the replay. Run `python3 verify.py` with NumPy and SciPy (sparse integer matrices). All 16 displayed lower bounds must be strictly positive.

[Clean integer replay transcript](replay.txt). The proof data are in [`certs/`](certs/); all 16 files and both Python sources are required for a replay.
