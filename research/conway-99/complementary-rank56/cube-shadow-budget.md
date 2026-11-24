# Cube shadows add actual primal norm-eight vectors

Use the [complementary rank-56 lattice](README.md), and let y4 count its vectors of squared norm eight. Write N16,d for the actual oriented neutral −4 norm-sixteen count of deficiency deck d, where the decks are ordered as 8, 6+2, 4+4, 4+2+2, and four double edges. Put
```
W = N16,1 + N16,2 + 2N16,3 + 2N16,4 + 4N16,5.
```
At any rank, **y4 ≥ 40,592 + ceil(W/10)**. At rank 42 the stronger bound is **y4 ≥ 40,592 + W**. These compare actual graph populations in opposite eigenspaces; no complete rank is ruled out.

## A new, disjoint class of lattice vectors

Let z be a signed parity indicator of an actual induced three-cube Q. Its shadow h=(A+4I)z has squared norm 56 by the [cube shadow calculation](../unpublished-neighbor-sieve/shared-norm-18/n16-matched-partitions.md#genuine-cube-shadows). The vector h/√7 is exactly the sum of the complementary centered marks a_i with coefficients z_i. It lies in the primal lattice's M summand and has squared norm eight, so every distinct oriented shadow yields one y4 vector.

None is in the [40,592 mandatory-mark census](README.md#3-mandatory-primal-marks). A coincident mandatory mark would have signed-unit coefficients c of support at most six, with coefficient sum s of absolute value at most five, plus an integral shift in the binary glue plane. Its binary projection must vanish. Since the glue class has order eleven this forces s=0 and the binary shift is zero. Equality of the M projections then gives d=z−c in the kernel of A+4I, with sum zero, and d is nonzero since z has eight sites. Each sign's coefficient mass in d is at most 4+3=7. An entry of magnitude at least two would require opposite neighbor mass at least eight by the eigen-equation, so d is unit. It has support at most fourteen, and the [neutral minimum and Fano classification](../short-support-packing/README.md) make it a norm-fourteen Fano field. In particular c and z must be disjoint, so the signed support of d contains Q.

A Fano field cannot contain such a signed cube. In the standard model its two shores are nonzero vectors and nonzero covectors on the three-dimensional binary space, with edge evaluation one. If four chosen covectors have degree three on four chosen vectors, they all evaluate to one on the sum v of the four vectors, so v is nonzero and the four covectors are exactly those evaluating to one at v. Any chosen vector equal to v then has degree four; every other chosen nonzero vector has degree two, since its defining binary condition and the one for v are independent. Neither yields the desired degree three of a cube. This proves disjointness from the mandatory census.

## Exact census identity and discriminant refinement

Let k_h count the oriented cubes with shadow h. Two distinct cubes with a common shadow are disjoint and mutually matched, preserving their shadow signs. Conversely a matched partition of a norm-sixteen support supplies an ordered equal-shadow pair with difference the given oriented field: orient one cube as the field and the other as the negative of the field. Reversing the roles and both cube signs produces a second ordered pair (at the opposite shadow) with the same difference. These are exactly the two ordered pairs for that partition. By the [five partition counts](../unpublished-neighbor-sieve/shared-norm-18/n16-matched-partitions.md) it follows that
```
sum_h k_h(k_h−1) = 2W.
```
The [six-cube exclusion](../unpublished-neighbor-sieve/shared-norm-18/norm16-no-six-cubes.md) gives k_h≤5 everywhere; hence each shadow contributes at most twenty to the sum and at least ceil(W/10) new lattice points are needed.

At rank 42 there cannot be even three such cubes with one shadow. Their differences from a common base cube have ordinary Gram with diagonal sixteen and off-diagonal eight, so modulo seven their two-dimensional Gram has diagonal two and off-diagonal one, determinant three, a nonsquare. The pairing on the original seven-discriminant is this dot product modulo seven, up to a common nonzero scalar. Its anisotropic plane has square determinant over F7 (equivalently, the split plane has determinant −1, a nonsquare), and a common scale does not change its square class. The nonsingular two-dimensional Gram could not span that plane. Thus k_h≤2, so each shadow contributes at most two to the sum and at least W new primal points occur. The ceiling and orientation conventions are literal, not averaged over extensions.

## Disjoint contributions through norm eighteen

In the complementary lattice of [the six-site census](README.md#3-mandatory-primal-marks), put \(g=h/\sqrt 7\) for an oriented shadow as above. For each such \(g\), take the following two families, where \(z_i^{\rm site}=(a_i,k)\) is the lattice site mark, \(\epsilon\in\{-1,1\}\), and \(v,w\) are integers:
\[
 g+ve+wf,\qquad
 g+\epsilon z_i^{\rm site}+ve+wf\quad(1\le i\le99).
\]
The first family has charge \(s=0\) in the binary glue plane and the second has \(s=\epsilon\). The glue class of \(k\) has order eleven, so equality within or between these families forces the same charge, then the same binary translate. At a nonzero charge, a putative collision with different sites \(i,j\) would imply
\[
 h-h'=\epsilon(A+4I)(e_j-e_i).
\]
The right side at \(i\) has magnitude at least three, whereas both shadows have entries in \(\{0,\pm1\}\). Thus the site and shadow are recovered. At zero charge the shadow is immediately recovered.

The zero-charge family is disjoint from the mandatory census by the norm-eight argument above, after cancelling the common binary translate. For charge one (the other sign follows by negation), a putative mandatory mark of coefficient vector \(c\) must have signed sum one and the same binary translate, by the order-eleven glue and \(|\sum c_i|\le5\). In particular \(c\) has support at most five, with at most three positives and two negatives. The equality of graph projections would make
\[
 d=z_Q+e_i-c
\]
a centered \(-4\) eigenvector, where \(z_Q\) is the signed cube indicator. It is nonzero because \(z_Q+e_i\) has at least seven nonzero entries. It has at most seven positive and seven negative mass. A coefficient of magnitude two or more would demand at least eight opposite-sign neighbour mass, so \(d\) is a signed-unit vector. Its support is at most \(8+1+5=14\). The minimum forces equality, hence \(Q,\{i\},\operatorname{supp}(c)\) are disjoint and \(d\) is a signed Fano field containing a cube. The binary incidence argument above excludes this.

An oriented shadow has squared norm eight, and 28 entries of each sign and 43 zeros. Since \(\langle g,a_i\rangle=h_i\) and each site mark has squared norm four, the \(198\) vectors before translation in the second family have half-norm \(6+\epsilon h_i\), with multiplicities \(56,86,56\) at indices \(5,6,7\). Adding the binary translate increases half-norm by
\[
 v^2+vw+3w^2+sw=(v+w/2)^2+11w^2/4+sw.
\]
For half-norm increment at most five, this forces \(|w|\le1\) and \(|v|\le3\). The [integer replay](cube_shadow_translates.py) counts the translates and convolves their coefficients. The resulting additions beyond the mandatory census, **per distinct oriented shadow**, are
\[
\begin{array}{c|rrrrrr}
j&4&5&6&7&8&9\\\hline
\Delta y_j&1&58&198&344&286&452 .
\end{array}
\]
Multiply each entry by \(\lceil W/10\rceil\) in any admissible rank, or by \(W\) at rank 42. For instance, at rank 42 this gives \(y_5\ge773392+6P+58W\). These are graph-realized lower bounds for six actual primal shells; feasibility of the resulting larger modular system is not asserted.
