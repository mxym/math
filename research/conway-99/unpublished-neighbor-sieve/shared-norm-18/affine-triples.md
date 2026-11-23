# A rank-36 three-type alternative is impossible

This note considers **exactly three** of the twelve unit types in the [rank-36 population sieve](rank36_three_types.py), not a graph with arbitrary additional types. Write $U_{a,t}$ for unit populations and $N_t$ for the neutral unit populations at the norms discussed below; the twelve-type coordinate $(0,26)$ is the *unit* part, even when the full norm-26 shell has nonunit entries. The folded nonnegative coordinates $W_{a,t}$ have the four subtractions used in [the moment equations](higher_moments.py). At rank 36, for the twelve unit types, the actual graph count is $2402W_{a,t}$. Also $W_{0,0}=1$ and $W_{1,23}\ge99$.

**The alternative $\{N_{24},U_{1,21},U_{3,37}\}$ is impossible.** When all other unit types in the twelve are absent, the nine short homogeneous moment equations give
$$
56W_{1,21}=1312W_{0,0}+29W_{0,14}+12W_{1,23}
              +16W_{3,33}+8W_{3,35}+3W_{4,46}.
$$
Consequently $U_{1,21}\ge\lceil2402(1312+12\cdot99)/56\rceil=107233$. The graph-theoretic upper bound $U_{1,21}\le44352$ below contradicts this. Together with the 210 prior exclusions, at most nine of the 220 exactly-three-type choices remain at rank 36; this is not an exclusion of rank 36.

## A self-contained upper bound

A $(1,21)$ field is a unit labeling $b$ with $Ab=-4b-2{\bf1}$, $\sum b=-11$, so it has five positives and sixteen negatives. Let $e,f$ count edges within the two respective signs. A positive sees $6+d_P$ negatives and a negative sees $2+d_N$ positives. Counting cross edges gives $f=e-1$. The capacity of pairs of positives for common neighbors is $20-e$, while the negatives already require at least $16+4f$ slots by $\binom{2+d}{2}=1+2d+\binom d2$. Hence $e=1,f=0$, so there is a unique positive edge $pq$ and the negatives are independent. Every negative sees exactly two positives. Since $p$ sees seven negatives, they consume all seven common-neighbor slots with the other four positives ($1+2+2+2$). The same holds for $q$. In particular the unique common neighbor $h$ of $p,q$ is negative.

Set $X=N(p)\setminus\{q,h\}$ and $Y=N(q)\setminus\{p,h\}$, disjoint 12-sets. The negatives include six in $X$, six in $Y$, and $h$. Each wing induces six matching edges by $\lambda=1$. There is also a perfect matching from $X$ to $Y$: each $x\in X$ shares $p$ and exactly one other neighbor with $q$, and that second neighbor is in $Y$ because $h$ has its unique mate $q$ in $N(p)$. The reverse direction gives uniqueness on $Y$. The six negatives in $X$ choose one endpoint of each mate edge, hence at most $2^6$ possibilities. Those in $Y$ must be exactly the cross-matched images of the six *nonnegative* sites of $X$, because the negatives are independent.

It remains to show a chosen wing coloring specifies at most one full field. With $d_i=3e_i-Ae_i$ put $D=d_p+d_q$. Then $D$ is 2 on $p,q$, −2 on $h$, −1 on the two wings, zero elsewhere. The defining adjacency identity gives $A d_i=-4d_i-2{\bf1}$, $\|D\|^2=36$, $b\cdot D=18$. Hence $D-b$ is another unit $(1,21)$ labeling; it fixes $p,q,h$, interchanges the colors on both wings and exchanges the remaining three positives $R$ with the remaining three negatives $R'$. Any $r\in R$ misses $p,q,h$ (the unique positive edge is $pq$, and $h$ already sees two positives). Both its common neighbors with $p$ lie in $X$ and are negative, by the endpoint-slot saturation above. Applying the same fact to the switched labeling shows that every $r'\in R'$ sees two *oppositely* colored sites in $X$ and cannot be an $R$-site of any field with the original coloring. Consequently two such fields differ off the wings in at most twelve signed units, with no opposite-sign conflicts producing nonunits. Their difference has eigenvalue −4, and cannot be nonzero: its positive and negative supports would have equal size $n\le6$, each positive needs at least four negatives, and the common-neighbor cap gives $6n\le2\binom n2$, impossible. This proves the desired uniqueness. There are $99\cdot14/2=693$ possible positive edges, so $U_{1,21}\le693\cdot64=44352$ unconditionally.

## The other charge-three alternative

On $\{N_{24},U_{1,27},U_{3,37}\}$ the same rows instead give
$$
\begin{aligned}
W_{3,37}&=321W_{0,0}+7W_{0,14}+4W_{0,22}+W_{1,23}+2W_{3,35},\\
12W_{1,27}&=5568W_{0,0}+123W_{0,14}+48W_{0,22}
                +36W_{1,23}+24W_{3,35}+5W_{4,46}.
\end{aligned}
$$
At rank 36 this yields $U_{3,37}\ge1008840$ and $U_{1,27}\ge1827922$. Each $(3,37)$ field has two nonadjacent positives: if they were adjacent, $b-d_p-d_q$ would be a $(1,21)$ field with two adjacent negatives, contrary to the independence just proved. Thus, among the 4,158 unordered nonedges, at least one positive pair is shared by at least 243 such fields. This second alternative is not refuted here.

**Exact replay.** Place [rank36_affine_triples.py](rank36_affine_triples.py) beside [rank36_three_types.py](rank36_three_types.py) and run it with Python and python-flint. For each hypothesis it projects the previously established nine short rows onto the retained columns and checks that adjoining each stated small integer identity does not raise their exact rational rank. No linear-programming tolerance, graph symmetry or newly assumed bounds enter the identity check.
