# The complementary rank-56 lattice of a Conway graph

Assume an SRG(99,14,1,2) with adjacency matrix $A$ and mod-seven Seidel rank $r$. We work in its **+3** eigenspace, not the −4 eigenspace of the [rank-44 construction](../maximal-marked-lattice/README.md). The necessary conditions below apply to all four ranks $r=36,38,40,42$ and do not exclude any rank.

Write $P$ for the number of induced triangular prisms, $D$ for the number of unordered vertex-disjoint anticomplete pairs of prisms, $G$ for the number of induced nine-site rook grids, and $N^+_{14}$ for the number of oriented integral +3 eigenvectors of ordinary squared norm 14. There is an even rank-56 lattice $\Lambda$ of level 7 and determinant $7^{54-r}$. Here $y_j$ counts vectors of squared norm $2j$ in $\Lambda$; $x_j$ counts them in $\sqrt7\,\Lambda^*$. These coefficients are **not** those of the old −4-side lattice. We prove

$$
x_1=\cdots=x_5=0,\qquad x_6=4G+2D,\qquad x_7=2+N^+_{14}.
$$

## 1. Projection, determinant and glue

We have $A^2=12I-A+2J$, with eigenvalues $14,3,-4$ of multiplicities $1,54,44$. Set $E=(4I+A-2J/11)/7$, the orthogonal +3 projector, and $a_i=\sqrt7\,Ee_i$. Then $(a_i,a_j)=(4I+A-2J/11)_{ij}$. The even integral lattice $M=\sum_{i,j}\mathbb Z(a_i-a_j)$ is the quotient of the sum-zero coefficient lattice $C$ by the radical of its pulled-back Gram form, which on $C$ is the standard dot product followed by $A+4I$.

* At 7 the dot product on $C$ is unimodular (determinant 99). The operator $A+4I$ acts as 7 on its rational image, hence 7 times its saturated image lies in its integral image. Thus every nonzero local Smith entry is 1 or 7 up to units. The number of units is precisely $r$: on the sum-zero part $S=J-I-2A$ reduces to $-2(A+4I)$ and the separate constant line is killed by $S\bmod7$. Removing the primitive radical leaves the same nonzero Smith entries. Thus the discriminant group at 7 is elementary of rank $54-r$.
* At 11 the eigenvalue difference 7 is a unit, so $C$ splits orthogonally into the two restricted eigenspaces. The ordinary dot product on $C$ has a single factor of 11 in its determinant, and its mod-11 radical is the constant line, lying in the +3 summand since $14\equiv3\bmod11$. The rescaling by 7 on this summand is a unit, hence the determinant of $M$ has 11-adic valuation one.
* At every other prime the projector $E$ is integral on the full unimodular ambient module. Its image is therefore an orthogonal unimodular direct summand and rescaling its form by 7 leaves it unimodular. All the projected generators are locally in the difference lattice since $11a_i=\sum_{j\sim i}(a_i-a_j)$. In particular this works also at 3, where the sum-zero coefficient lattice is not unimodular.

Thus $\det M=11\cdot7^{54-r}$, consistent with the [rational determinant calculation](../../conway-99-involution/rational-eigenspaces/Theorem.md). Each $a_i$ pairs integrally with $M$. Its class has order 11 and half-norm $21/11\equiv-1/11\bmod1$.

Use a binary even lattice $K$ with basis $e,f$ and Gram matrix $[[2,1],[1,6]]$. The dual vector $k=(-e+2f)/11$ has norm $2/11$ and evaluations 0 and 1 on $e,f$. Adjoin $(a_0,k)$ to $M\perp K$; its discriminant quadratic value is zero, giving an even index-11 overlattice $\Lambda$ with exactly the claimed elementary 7-discriminant. The level is 7: on the dual $7(v,v)$ is integral and $49(v,v)$ even forces $7(v,v)$ even. The determinant exponent is positive and even in the four ranks, so the level is not 1 and the scalar theta character is trivial. The actual marks $z_i=(a_i,k)$ have Gram matrix $4I+A$.

## 2. Dual-label dictionary

For $u\in M^*$ its evaluations on the $a_i$ have integral differences, lie in $\frac1{11}\mathbb Z$, and sum to zero. Write them uniquely $b_i-a/11$, $b_i\in\mathbb Z$, $-5\le a\le5$. They form a +3 eigenfunction, hence $Ab=3b+a{\bf1}$ and $\sum b_i=9a$. Conversely the centered evaluations of any such labeling are in the projector image; the tight-frame bound 7 gives $u=\frac17\sum_i(b_i-a/11)a_i$. Its squared norm is $(t-9a^2/11)/7$ for $t=\sum b_i^2$.

A vector of $K^*$ with evaluations $p,q$ on $e,f$ has squared norm $(6p^2-2pq+2q^2)/11$. It pairs with the glue class integrally after combining with $u$ exactly when $a\equiv-p+2q\bmod11$. Its squared norm after scaling the pair by $\sqrt7$ is

$$
  2j=t+[7(6p^2-2pq+2q^2)-9a^2]/11.
$$

For $j\le7$, use $t\ge9|a|$, $t\equiv a\bmod2$ and $6p^2-2pq+2q^2\ge5p^2+q^2$. The following list is exhaustive; for nonzero charge the multiplicity includes both signs, and multiplies the number of labels at positive charge.

* $0\le j\le5$: neutral $t=2j$ once.
* $j=6$: neutral $t=12$ once; charge magnitude 1 with $t=9$ four times.
* $j=7$: neutral $t=14$ once and $t=0$ twice; charge magnitude 1 with $t=11$ four times.

For neutral $t\le14$, if $b_i\ge2$ subtract $d_i=(4I+A)e_i$. This vector has charge 2, norm 30 and $b\cdot d_i=7b_i$. The resulting charge −2 vector has squared norm at most $14+30-28=16$, less than its absolute coordinate sum 18. Reversing signs rules out all nonunits. Both signs have $n=t/2$ sites and minimum internal degree three.

On at most six sites the only possible nonempty induced graph of minimum degree three is a prism. Every vertex neighborhood induces a matching. Center degree at least five leaves no site outside that closed neighborhood and its leaves can only see the center and one mate. With degree four, every leaf needs the sole possible site outside the closed neighborhood, contrary to the common-neighbor cap of two. Thus the graph is cubic. On four sites it would be a forbidden $K_4$; five sites are impossible by parity. On six sites its complement is a six-cycle or two triangles, giving respectively a prism or the impossible $K_{3,3}$. This excludes $0<t<12$. At $t=12$ the two prisms are anticomplete by the eigen-equation. Conversely their signed difference has sum zero and Rayleigh quotient 3 on the sum-zero subspace, hence is a +3 eigenvector. The contribution is $2D$.

At charge 1 and $t=9$ the equation $\sum b_i^2=\sum b_i$ makes $b$ a nine-set indicator. Internal degree is four and exterior degree one, so all pair quotas are attained inside. For clarity, the resulting (9,4,1,2) graph is a rook grid: at a root its four neighbors form two mate pairs; each of the four remaining sites sees one neighbor from each pair, and each choice occurs exactly once. For either neighbor from either mate pair, its two contacts among the remaining four must be adjacent by the neighborhood matching, determining the rest by degree four. Conversely every induced grid exhausts all its internal pair quotas, and its $9(14-4)=90$ external incidences give each outsider exactly one contact. This contribution is $4G$.

At charge 1 and $t=11$, the equation $\sum b_i(b_i-1)=2$ gives either one −1 or one +2, all other entries 0 or 1. The −1 site would require neighbor sum −2. In the +2 case every one of its 14 neighbors would have to be nonzero (a zero site has neighbor sum 1), but there are only seven singletons. This completes the displayed dual coefficient identities.

## 3. Mandatory primal marks

Choose a coefficient vector $c$ with entries $0,\pm1$, support size $m\le6$ and $|s|=|\sum c_i|\le5$. For integers $v,w$ the marked vector $\sum c_i z_i+ve+wf$ has squared norm

$$
 4m+2\sum_{i<j,\ i\sim j}c_ic_j+2ws+2v^2+2vw+6w^2.
$$

These descriptions never collide. Equality of binary projections forces $s-s'\equiv0\bmod11$, hence $s=s'$ and the same translate. If the other projections agree, $d=c-c'$ has equal positive and negative masses each at most six, and $Ad=-4d$. A nonunit requires opposite neighbor mass at least eight. With unit entries and $n$ sites of each sign, every positive site needs at least four negative neighbors; counting pairs gives $6n\le2\binom n2$, excluding $1\le n\le6$.

Keeping just $-6\le v\le6$ and $-4\le w\le4$ gives these lower bounds (not assertions that the marks fill the entire shells):

| $j$ | $y_j$ at least |
|---:|---:|
|0|1|
|1|2|
|2|198|
|3|1,786|
|4|40,592|
|5|$773392+6P$|
|6|$14385096-54P$|
|7|$164667888+180P$|
|8|$1254825198-126P$|
|9|$6155557260-1096P$|

**Replay:** python3 verify.py (standard library only, Python 3.9+). This standalone verifier reuses the [six-site recurrence](../rank-34-short-support/count_marks.py) and checks the binary lift table as well. Remove a degree-0,1,2 vertex of a test graph; the extension factors are respectively 99, 14, and $2-A_{ij}+12[i=j]$. At minimum degree three the only injective images through six sites are prisms, with $12P$ labeled embeddings by the above classification. Partition by equal images to recover noninjective homomorphisms, then invert over missing edges to count induced images. Divide by the permutations of each sign class. Every recursive expression is affine-linear in $P$; evaluating formally at 0 and 1 gives the exact constant term and slope, not two graph-realizability assumptions.

See [Cross-eigenspace tail and grid bounds](tail-budget.md) for comparisons with actual charge-one populations in the −4 sector and whole-grid intersection constraints.

See [the cube-shadow budget](cube-shadow-budget.md) for a disjoint family of primal norm-eight vectors counted by the actual neutral norm-sixteen support census.
