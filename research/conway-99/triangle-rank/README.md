# A triangle obstruction to small Seidel rank for the Conway 99-graph

**Theorem.** Let $A$ be the adjacency matrix of a strongly regular graph with parameters $(99,14,1,2)$. Then $S=2A-J+I$ has rank greater than 30 over $\mathbb F_7$. Together with the known evenness and upper bound this leaves $32,34,36,38,40,42$. The proof uses a finite exhaustive computation and applies to a graph with any automorphism group. The [subsequent rank-32 census](../triangle-rank-32/README.md) reduces the list to five values. Existence is still open.

Previously the eight even values from 28 to 42 survived the lattice argument. The triangle calculation below excludes the first two. The convention for the sign of the Seidel matrix does not affect its rank. [Wave 66 and related bounds](https://github.com/YesterdaysLemon/conway-99-research#readme) · [Rational eigenspaces and rank parity](../../conway-99-involution/rational-eigenspaces/Theorem.md).

## The 39 vertices about a triangle

Fix a triangle and call its vertices $0,1,2$. Every edge is in one triangle. The other 12 neighbors of each triangle vertex form a wing. The wings are disjoint. Inside a wing each site has precisely one mate, the unique common neighbor of the site and its parent. Between two wings there is a perfect matching. Indeed, a site in wing $i$ and parent $j$ have two common neighbors, one of which is parent $i$. The other must lie in wing $j$. Applying this in both directions gives the matching.

Label the twelve sites in each wing by transporting labels along the first two matchings, from wing 0 to 1 to 2. Let $P,Q,R$ be the three mate permutations and let $\pi$ map labels in wing 2 back to wing 0 along the last matching. These data specify the entire induced adjacency matrix $A_C$ of the 39 vertices. Simultaneous relabeling lets us fix $P=(0,1)(2,3)\cdots(10,11)$. The union of $P,Q$ is a union of alternating even cycles, counting doubled edges as cycles of length two. Their half-lengths partition six. On each such representative we reduce the 10,395 choices of $R$ by rotations by two, color-preserving reflections and swaps of equal-length cycles. This gives 3,580 representatives $(P,Q,R)$. One must still consider every permutation $\pi$ for each representative. No relabeling is required to extend to an automorphism of the graph.

## Enumerating low-rank shells

Write $D$ for the adjacency on the 36 wing sites. Over $\mathbb F_7$ the rank of $S_C=2A_C-J+I$ is $1+\operatorname{rank}(3I-D)$. To see this, split the coordinates on each wing into constants and vectors of sum zero, possible since $12$ is invertible. On the three zero-sum spaces together the operators $S_C$ and $-2(3I-D)$ coincide. On the wing constants $3I-D$ acts by $3I_3-J_3$, of rank two. On the three parent coordinates and three wing constants $S_C$ acts by the matrix below, with $I=I_3,J=J_3$.

$$
\begin{pmatrix}J-I&12(2I-J)\\2I-J&I-10J\end{pmatrix}.
$$

This matrix has rank three. On constants across the three wings and on each of the two contrasts it gives a two-by-two block of rank one modulo seven. In $3I-D$ eliminate the middle wing by $(3I-Q)^{-1}=3I+Q$. Writing $\Pi_{ij}=1$ when $i=\pi(j)$, the shell rank becomes

$$
13+\operatorname{rank}\begin{pmatrix}
P+Q & 3I+Q+\Pi \\
3I+Q+\Pi^t & Q+R
\end{pmatrix}.
$$

Here permutations in matrices stand for their permutation matrices. The checker eliminates a nonsingular principal submatrix spanning the rank of $P+Q$. After this elimination it chooses the images $\pi(j)$ without replacement. At each step the residual principal matrix of the assigned sites is fully known. Its rank is a lower bound for the final residual rank, so pruning above the cap cannot suppress a solution.

| Rank of the 39-vertex shell | Permutations at that rank, summed over the 3,580 representatives |
| --- | ---: |
| At most 27 | 0 |
| 28 | 8 |
| 29 | 165 |
| 30 | 5,239 |

Before checking exterior vertices, identify simultaneously conjugate quadruples within each representative. For the directed edge-colored graph of the four named permutations, traverse each component from each possible start in a fixed color order, keep its lexicographically least encoding and sort the component encodings. This leaves 571 shells. All shell ranks are recomputed directly from the 39-by-39 matrix at this stage.

## The other 60 vertices

Each outside vertex sees exactly two sites of each wing, since it and the corresponding parent have exactly two common neighbors. The two sites cannot be mates. Conversely each nonmate pair in one wing has just its parent as a common neighbor inside the shell, by the matching property. Its second common neighbor must lie outside. Thus each of the 60 nonmate pairs in each of the three wings must occur. A choice of three such pairs determines a proposed exterior column $v$ of $S$, with six entries $+1$ and all others $-1$. Discard a choice if two of the six sites already have their full quota of common neighbors in $C$.

Let $Z$ have as rows a basis of the kernel of $S_C$, and let $V$ collect all exterior columns restricted to the shell. If $s=\operatorname{rank} S_C$, then

$$
\operatorname{rank} S \ge s+2\operatorname{rank}(ZV).
$$

Indeed, split off the nonsingular part of $S_C$ by congruence. In the remaining matrix the shell radical has zero diagonal block and off-diagonal block $ZV$. Taking a nonsingular $t$-by-$t$ minor of $ZV$ gives a nonsingular principal block of size $2t$, whatever the exterior diagonal block.

* At shell rank 30 every possible column must leave the rank of its bordered 40-by-40 matrix equal to 30.
* At shell rank 29 every possible column satisfies $Zv=0$.
* At shell rank 28 all the vectors $Zv$ must lie on one common line, including the possibility that all are zero. For each required wing pair try every combination of pairs in the other wings. If a zero vector is possible, this requirement imposes no line restriction. Otherwise retain its set of attainable lines and intersect these sets over all required pairs.

Every one of the 571 shells fails the corresponding necessary test. This proves the theorem.

As a cross-check I also enumerated directly from the Seidel matrix on the parents and the first two wings. That computation inserted sites of the third wing with incremental symmetric elimination. Across 3,580 matching representatives it gave exactly the same 5,412 labeled results, including each permutation and its rank, as the wing-Laplacian enumeration supplied here. An additional implementation of the exterior test checked all 5,412 cases before taking conjugacy representatives.

## Reproduction

From this directory run the following with Python 3, NumPy and a C++17 compiler. The optional job count distributes whole matching representatives across processes. Both the enumeration and the extension checks use exact finite-field arithmetic.

```sh
c++ -O3 -std=c++17 enumerate.cpp -o /tmp/conway-triangle-rank
python3 check.py /tmp/conway-triangle-rank --jobs 3
```

Expected counts are `{28: 8, 29: 165, 30: 5239}` and `571 representative shells; all obstructed at global rank <= 30`. The checker imports the existing matching generator and ordinary elimination routine from [check_rank.py](../../conway-99-involution/seven/check_rank.py). The finite search covers necessary local conditions. The six larger rank values require further arguments.
