# One short field per doubly prism-covered square outside grids

Assume a hypothetical SRG(99,14,1,2) has no neutral integral minus-four field of squared norm 14 (the Fano-free case). Write S for the number of graph fields of **positive charge one, squared evaluation cost 23** whose entries are all 0,+1,−1. This counts the positive-charge labeling once, not the charge-minus-one negation; it is the unscaled unit G(1,23) population. We use the [norm-28 marked-coset / positive-charge dictionary](../marked-coset-shells/README.md): an integer evaluation b of charge a obeys Ab=−4b−2a·1, Σb=−11a, and its cost t is Σb_i².

Let Q₂ be the number of induced squares with prisms in both directions, and G the number of rook grids. Each grid has nine squares, which are doubly covered, and no two distinct grids share one (two intersecting grid lines reconstruct their grid by the common-neighbor rule). See the [two-direction dictionary](../../conway-99-involution/uncovered-squares/README.md).

**Theorem.** Each doubly covered square outside all grids gives a different unit (1,23) field. Thus
```
Q₂−9G ≤ S.
```
More precisely, all four roots of one such square give the same field and four distinct exceptional anchors. The theorem does not assume the rank or the absence of any other shell.

## Literal eight-site set and its single mark

The two prisms in the two directions of a square are unique, since every edge has a unique triangle cap. Their union H consists of the eight sites of a rook grid minus a corner: denote the square vertices by p_ij, i,j∈{0,1}; the two row extensions by R_i and the two column extensions by C_j. The row and column extensions in their own pair are adjacent, their edges to the four square corners are those of their corresponding prism, and R_i and C_j cannot be adjacent: they are neighbors on different signed axes at p_ij, each already paired to another neighbor there. These facts determine all edges of H. Inside H a square corner has degree four and an extension vertex has degree three.

At root p_ij use its two local axes visible in H, consisting of its two same-row and two same-column neighbors. Three of their four exterior cell labels are in H: the square-opposite corner sees the two flip neighbors, namely one row extension and one column extension. The fourth label q_ij is the other common neighbor of R_i and C_j besides p_ij. It is outside H. In the four-cell graph the three known H vertices form a two-edge path, with both edges flips. The known degree-two vertex cannot take a further edge. The fourth label cannot add just one edge (three-edge cells are impossible by [the real-defect argument](big-triangle-wing.md)). Adding both remaining flips would turn the cell into a grid containing the square, contrary to the assumption. Thus q_ij is isolated in that cell.

The nine-site set S_e of this axis pair is therefore H together with q_ij, and its cell defect is v_e=(A−3I)1_(S_e)−1, neutral and of squared norm 28. The site translation d_q=(3I−A)e_q has charge one, cost 23, and v_e·d_q=7v_e(q)=−14, since q is isolated in its cell. Consequently the charge-one field
```
u = v_e+d_q = (A−3I)1_H−1
```
has cost 28+23−28=23. It is the same exact integer labeling for all four roots. It is not an ordinary d_i: otherwise v_e=d_i−d_q, whose squared norm for i≠q is 42 or 56, and it is zero at i=q.

For completeness, Fano-freeness makes every nonordinary (1,23) labeling unit. If b_i≥2, subtracting d_i gives a neutral field of norm 42−14b_i. At b_i=2 this is the absent norm 14, at b_i=3 it forces b=d_i, and larger entries are impossible. If b_i≤−2, adding d_i gives charge two and cost 50+14b_i≤22. Strictly less than 22 violates the absolute coordinate sum, and equality forces every value nonpositive, whereas the translated coordinate at i is +1. This checks the relevant positive-charge convention directly.

## Recovering the square from the same field

For any unit (1,23) field, write P,N for its six positive and seventeen negative vertices. The field equation makes the cross degrees 6+d_P at a positive vertex and 2+d_N at a negative vertex, where d_P,d_N are respective same-sign degrees. Thus e(N)=e(P)+1. There are at most 30−e(P) common-neighbor allowances for P-pairs, but the negative vertices alone witness at least
```
Σ_(x∈N) choose(2+d_N(x),2) ≥17+4e(N).
```
Hence 5e(P)≤9, so e(P)≤1 and e(N)≤2.

For the constructed u, its four square corners are zero and its four extension vertices are negative, by their degrees in H. The two extension edges are therefore exactly the two negative edges of u, with no others. For each unordered pair consisting of one endpoint from each of these two edges, the two common neighbors are its square corner (u=0) and its missing-corner label q_ij (u=+1). The latter value follows equally from u=v_e+d_q and v_e(q)=−2.

These four q_ij are distinct. A repeated candidate from two pairs sharing an endpoint would be adjacent to at least three distinct extension vertices; for two disjoint pairs it would be adjacent to all four. Any such outside site has u=(number of its H-neighbors)−1 ≥2, contrary to the unit profile. Given u, the four cross pairs between the endpoints of its negative edges therefore recover the square as their four unique zero common neighbors. Given u and one of its four anchors, its two extension neighbors are the only endpoints of those negative edges adjacent to it; their other common neighbor is the precise rooted corner p_ij. This proves the desired injection and also fixes the root when needed.

The two unique triangle caps of the two negative edges are outside H, each with at least two neighbors in H. They are distinct from the four anchors and each other, since otherwise an outside site would have at least three H-neighbors and u≥2. Thus the six positives of u are exactly the exterior pair witnesses of the four extension vertices. No assertion is made that every unit (1,23) label arises this way.

Every rooted two-edge path-plus-isolate four-cell supplies one square outside grids of the above kind (the degree-two label is the opposite corner and its two flips specify the two prism directions), and conversely each such square supplies exactly four such rooted cells. The total number of those rooted cells is therefore 4(Q₂−9G)≤4S.

## Consequences and current scope

In the Fano-free case S=0, every doubly covered square belongs to a grid and no rooted four-cell is a two-edge path plus isolate; a nonclean two-edge cell must be a matching. The fields constructed from H are eligible in every marked extension, even though the theorem uses the full graph population S. Indeed for the base marks $u_i$ with Gram $3I-A+J/9$, set $y=-\sum_{i\in H}u_i$. Its evaluations are $u+\mathbf{1}/9$ by the displayed definition of $u$. Also $y-u_0=-\sum_{i\in H}(u_i-u_0)-9u_0$ is in the original graph lattice, which contains every $u_i-u_0$ and $3u_0$. Thus $3y$ is in the original marked coset. Its zero discriminant class contributes without division by eight to the extension population.

On the rank-42 two-type branch the [four remaining short tuples](shared-norm-18/two-type-true-hoffman.md) give Q₂−9G≤2,5,8 or 11 respectively. The equivalent linear relation is
```
2079−n₃+U₀−9G ≤ S,
```
where U₀ counts uncovered squares and n₃ counts disjoint triangle pairs with exactly two joining edges. The known unconditional grid and uncovered-square inequalities do not by themselves force this left side above 2,5,8 or 11. This gives an actual common-field restriction, not an exclusion of any of the four tuples or of a whole rank.

## An eligible coclique charges some squares twice

Fix an actual Hoffman coclique C and a marked extension in which it is eligible. Let $S_C$ count the eligible unit $(1,23)$ labels in this extension, and let $D_k$ count the nongrid doubly covered squares with $|C\cap H|=k$ for their eight-site set H. Then
$$D_0=0,\qquad D_1+D_2+2D_3\le S_C.$$
For a square counted in $D_1$, its single point in C is a square corner, not an extension vertex. The eight-site diagram is part of a three-by-three grid, so its independent sets have order at most three.

Put $c=-\mathbf1_C$. The marking of H has actual angle
$$\delta=u\cdot c=7k-10,$$
since $A\mathbf1_C=4(\mathbf1-\mathbf1_C)$. If $k=0$, the field $u+c$ would have charge three and cost $23+22-20=25$, below the minimum absolute coordinate sum 33. If $k=1$, then $\delta=-3$, meaning that C contains three more positive than negative sites of u. Every extension vertex is negative in u and is adjacent to three of the six positive pair witnesses. If that extension vertex belonged to C, at most three positive sites would remain available, whereas at least four would be required.

When $k=3$, its three sites occupy distinct rows and columns in the eight-site grid diagram. They include one endpoint of each of the two negative extension edges: the truncated row and the truncated column have to be used. Now $\delta=11$. The eligible translate $u'=c-u$ has charge one and cost $22+23-2\cdot11=23$. Its entries are at most one, so it cannot be an ordinary mark; by Fano-freeness it is therefore unit. Its positives are exactly the negative sites of u outside C, an independent set because both negative edges meet C. The degree balance above gives only one negative edge for $u'$. It is therefore not any square label. The transformation is injective, so each $D_3$ square spends an extra label from the same shell, in addition to its original square label. Here this translate retains zero terminal discriminant class because c is eligible and u came from the original marked lattice.

On the rank-42 two-type face, $S_C=S$ in the [actual coclique identity](shared-norm-18/two-type-true-hoffman.md#a-universal-marked-identity-on-this-face), and independently
$$3D_2+16D_3\le V_C=(853-62S)/3.$$
Each $D_2$ square has angle four and contributes a nonordinary mark to the angle-four bracket of $V_C$. Both labels of a $D_3$ square have angle eleven, with coefficient eight each. These are constraints on literal square counts; they do not provide a lower bound contradicting a tuple.
