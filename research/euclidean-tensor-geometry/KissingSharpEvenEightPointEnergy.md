# Sharp optimized quartic energy of eight kissing points

Put $f(t)=t^4-t^2/4$. If $X$ consists of $2m$ unit vectors whose distinct pairs have inner product at most $1/2$, let $h(X)$ be the minimum of $\sum p_xp_y f(x\cdot y)$ over probability weights. For **$m=1,2,3,4$**, in unrestricted ambient dimension,
\[
                         \max_X h(X)=\frac{3}{4m}.
\]
In particular the eight-point maximum is **$3/16$**, with no transitivity, span or sign-pattern assumption. The eight-point value is attained already in dimension three, for example on four antipodal root lines of $D_3$ (take the lines of $(1,\pm1,0)$ and $(1,0,\pm1)$, normalized). This is a weighted quartic maximum, not the usual best angle for eight points or a change in a kissing number.

At orders two, four and six the **entire equality family** consists precisely of $m$ antipodal pairs with all inner products between different lines in $\{0,\pm1/2\}$. This is also the full eight-point equality family whenever the strict graph has at least two maximum independent sets. We give a necessary-and-sufficient geometric test for the remaining eight graph types below; we do **not** claim that each such graph can attain equality.

## A local estimate for nearly antipodal pairs

The strict graph joins points with inner product below $-1/2$. It has no triangle, by applying the squared norm to the sum of three points. A pair block $P_i=\{x_i^+,x_i^-\}$ has center $m_i=(x_i^++x_i^-)/2$ and $b_i=\|m_i\|^2$. Suppose several blocks have $-x_i^+\cdot x_i^-\ge9/10$, so $b_i\le1/20$. Suppose also that between any two blocks there are either no strict edges or exactly two strict edges with disjoint endpoints, and each block meets at most two others by such double edges. Then the uniform distribution on the union of $m$ blocks has energy at most $3/(4m)$, strictly less if some $b_i>0$.

Indeed, for a double edge write the two strong inner products as $-1/2-\delta_1,-1/2-\delta_2$. The two other products are at most $1/2$. The sum of all four products equals $4m_i\cdot m_j$, hence
\[
 0\le\delta_1+\delta_2\le-4m_i\cdot m_j
 \le4\sqrt{b_ib_j}\le2(b_i+b_j)\le1/5 .
\]
The two weak costs are nonpositive. As $f$ is convex and increasing on $[1/2,1]$, the total cost over these four pairs is at most $2f'(7/10)(b_i+b_j)$. Summing over adjacent blocks yields at most $4f'(7/10)\sum_i b_i$. The within-block off-diagonal costs, on the other hand, have total at most $3m/4-2f'(9/10)\sum_i b_i$, by integrating $f'$ on $[1-2b_i,1]$. Since $4f'(7/10)=4.088<4.932=2f'(9/10)$, adding the diagonals proves the claim. This argument also works with non-strict limiting double edges exactly at $-1/2$.

## Why eight is sharp

An independent $m$-set has all pair products in $[-1/2,1/2]$, where $f\le0$. Uniform weight on it gives $h\le 3/(4m)$. At two, four and six vertices, a triangle-free graph always has an independent set of at least half its vertices. For six this is the elementary $R(3,3)=6$ argument: for any vertex of degree at least three use three neighbors; if all degrees are at most two the components are paths and cycles, with the only possible odd cycle on five vertices accompanied by a singleton. The four-point assertion follows from triangle-freeness directly.

At eight vertices, absence of an independent four-set leaves precisely three abstract Ramsey graphs. Their number is classical, not a new enumeration: compare [McKay's catalogue of Ramsey graphs](https://users.cecs.anu.edu.au/~bdm/data/ramsey.html). Our verifier regenerates all three by hereditary augmentation and canonical refinement. For the two noncubic graphs, continuous Gram bounds give $h\le .187470<3/16$ in 31 and 65 cells.

The remaining graph is the eight-vertex Möbius ladder, consisting of an eight-cycle and four opposite rungs. Contracting the four rungs leaves a four-cycle of double edges. If all four rung strengths $-x_i^+\cdot x_i^-$ are at least $9/10$, apply the block lemma. They cannot all be exact antipodes in an actual cubic strict graph: an antipodal pair has no strict neighbor outside the pair. The bound is therefore strict. Otherwise a weakest rung has strength at most $9/10$. The four rungs are equivalent under graph automorphisms, so choose it as the largest rung Gram coordinate. Its lower endpoint is rounded **down** to the $1/4096$ grid. The remaining continuous chart gives $h\le .187470$ in 99 cells. Thus equality at eight requires an independent four-set.

Conversely on any union of $m$ signed lines as in the equality family, the energy equals $\tfrac34\sum_i(p_i^++p_i^-)^2$. Its minimum is $3/(4m)$. This proves sharpness.

## Exchanges of maximizing independent sets

For a signed mass difference $c$ with $\sum c_i=0$, set $T=\sum c_i x_i^{\otimes4}$ and $B=\sum c_i x_ix_i^T$. The trace of $B$ is zero, and $B$ is the two-index contraction of $T$. In span dimension $d\le8$,
\[
 \|T\|^2\ge\frac{6}{d+4}\|B\|^2,\qquad
 c^TFc=\|T\|^2-\tfrac14\|B\|^2\ge0,\quad F_{ij}=f(x_i\cdot x_j).
\]
For the first inequality, pair $T$ with the symmetrization of $B_{ij}\delta_{kl}$ over the six placements. Its contraction is $(d+4)B/6$, so its squared norm is $(d+4)\|B\|^2/6$. Equality $c^TFc=0$ therefore forces $T=0$. In particular probability energy is convex on the simplex.

In an equality code every independent $m$-set is a minimizing uniform support: its distinct costs must all vanish, so its line inner products are $0$ or $\pm1/2$. An independent set larger than $m$ is impossible. If $S,S'$ are two different independent $m$-sets, their probability midpoint is admissible. Applying the preceding inequality to the difference of their minimizing weights shows that the two fourth moment tensors are identical. Cancel the common points; put $r=|S\setminus S'|\le4$. Viewed as operators on symmetric matrices, the tensors give identical ranges, namely the span of the squares $s s^T$ on each side. We claim this forces an antipodal pair in the code.

* For linearly independent $s$ on one side, change coordinates to send them to coordinate vectors. The only rank-one squares in the resulting diagonal span come from the same lines. Since the two difference sets are disjoint, matching a line gives an antipodal pair.
* A dependent triple has rank two: a line cannot contain two members of an independent set. Its three lines occupy an entire maximum projective $60^\circ$ configuration in that plane (directions modulo $\pi$ are separated by at least $\pi/3$). The other triple lies in that same plane by equality of the square spans. Six distinct kissing vectors in a plane must form a regular hexagon, hence yield antipodal pairs.
* Four such independent-set lines cannot all fit in a plane. In rank three, if three lie in a plane, change coordinates to place the plane in the first two coordinates and the fourth line on the third axis. The square span is block diagonal. The second set must use that axis, since otherwise its span of squares has zero third block. If no triple is dependent, normalize a basis of the first three lines so the fourth has coordinates $(1,1,1)$. A rank-one matrix in the span of the three diagonal squares and $\mathbf1\mathbf1^T$ either is diagonal or has all three off-diagonal products equal and nonzero; its generating vector is then proportional to $\mathbf1$. Again the same lines must be used. Congruence changes here preserve ranks and spans; they are not asserted to preserve angles.

An antipodal pair has only nonpositive cross costs to the remaining code. If those remaining $2m-2$ points had $h<3/[4(m-1)]$, mixing minimizing probabilities of the two parts with masses proportional to their reciprocal energies would contradict equality for $2m$ (if a part has nonpositive minimum, use that part alone). Thus the remaining code attains its own bound. Once induction identifies those remaining points as a paired code, their uniform measure minimizes energy and has full support. A negative cross cost to the removed pair would then strictly lower the energy of the mixed measure, so all cross costs vanish as well. For $m\le3$, two different maximum independent sets always exist: if $S$ were unique, each outside vertex would have at least two neighbors in $S$ (otherwise enlarge $S$ or swap). The outside $m$-set is not independent, yet the two endpoints of an outside edge need disjoint two-element neighbor sets in $S$, impossible for $m\le3$. Starting from the antipodal pair at order two, the exchange-and-removal argument proves the asserted equality classifications. At eight it proves the paired conclusion whenever two maximizing independent sets exist.

## The single-maximum-set test at eight

Among triangle-free eight-vertex graphs of independence number four, exactly eight isomorphism classes have a unique maximum independent set; the checker gives their indices in its own canonical list. For any such graph with unique four-set $S$, equality holds for a geometric realization **if and only if**
\[
 f(s\cdot s')=0\quad(s\ne s'\in S),\qquad
              \sum_{s\in S} f(y\cdot s)\ge3/4\quad(y\notin S).
\]
Necessity follows by perturbing uniform mass on $S$ toward each $y$; sufficiency follows from convexity and the simplex first-order condition at that uniform mass. This is an exact test of a given configuration, not an isometry enumeration of its possible realizations.

The [standalone replay](verify_kissing_even_eight.py) checks rational block constants, the graph census, the 195 continuous Gram cells, and the unique-independent-set count. Run `python3 verify_kissing_even_eight.py` with NumPy, SciPy and threadpoolctl. Numerical LP and eigenvector output only proposes leaves; every accepted terminal uses integer sign checks covering the closed Gram box.
