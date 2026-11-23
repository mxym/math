# Reconstructing the sixty exterior vertices from at most ten adjacency rows

In any hypothetical graph there is a triangle whose 39 known neighborhood marks span at least 33 of the 44 real dimensions. After specifying the 60 exterior contact words and at most ten exterior adjacency rows at this triangle, the whole graph is uniquely determined. The last dimension can be recovered by parity constraints.

## Choosing the triangle

Let $T$ have three wings of twelve sites. Their induced graph $D$ is cubic, with one mate in a site's own wing and one matched site in each of the other two. Its connected components have sizes $6k_i$: a component meets each wing equally often, and within each wing the mates pair its sites. Thus $\sum k_i=6$. Write $c$ for the number of components and $L=3I-D$ for the wing Laplacian.

A component of size six has two sites in each wing. It is either a triangular prism or $K_{3,3}$, as is seen by following the three cross matchings on the three pairs. The second option has two sites with three common neighbors. The prism option together with $T$ induces a three-by-three rook grid. Conversely a grid on $T$ gives such a component because each of its six wing sites uses all three wing edges in the grid.

If $c\ge5$ then at least four of the $k_i$ are one, giving four grids containing $T$. Any one grid contains six triangles and six induced prisms. Distinct grids cannot share a prism because they cannot share even one induced square. Indeed the two common neighbors of each opposite pair prescribe the square, edge third vertices prescribe its four caps, and the common-neighbor condition fixes the last point of its grid (it is the other common neighbor of two caps on intersecting extended lines). See the [square and grid count](../../conway-99-involution/uncovered-squares/README.md). With $g$ grids and $P$ prisms we have $6g\le P\le851$. At most $\lfloor851/4\rfloor=212$ of the 231 triangles can have $c\ge5$. In particular at least 19 have $c\le4$.

The wing Gram is $L+J/9$. Its kernel consists of the component constants of total sum zero, so its rank is $37-c$. The three triangle marks are in the wing span by their three neighbor equations. The parent coefficient matrix in these equations is $3I_3+J_3$, which is invertible. The complement of the whole 39-site span in the graph's real space has dimension $44-(37-c)=7+c$. It is at most eleven at the selected triangle.

## Contacts, pivots and rational reconstruction

Every exterior vertex has exactly two neighbors in each wing, and each nonmate pair of a wing occurs exactly once among the 60 contact words. Let $w_y$ be the column of 36 contact indicators. Each component of size $6k_i$ must receive exactly $k_i$ contacts, by orthogonality to the kernel of the wing Gram and the total of six. This is also the [component balance used in the earlier rank-32 checker](../triangle-rank-32/verify.py).

Let $L^+$ be the inverse on the orthogonal complement of the component constants, extended by zero on those constants. Put $v_y=w_y-\mathbf1/6$ and let $h_y$ be the projection of $u_y$ orthogonal to the wing span. The projection of $u_y$ onto the wing span has Gram entries
$$P_{yz}=1/36+v_y^tL^+v_z.$$
Indeed its pairings with the wing marks are $\mathbf1/9-w_y=-\mathbf1/18-v_y$. The wing Gram acts by four on the global constants, and by $L$ on the orthogonal complement of the component constants. Consequently the residual Gram $H$ has entries
$$H_{yy}=37/12-v_y^tL^+v_y,\qquad
H_{yz}=1/12-A_{yz}-v_y^tL^+v_z \quad(y\ne z).$$
One can use the inverse of $L+\bigoplus_i J_{6k_i}$ on the balanced vectors for exact rational arithmetic.

The 60 residual vectors span the complement because the full frame spans all 44 dimensions. Choose $6+c$ independent residuals, with index set $I$, one short of a basis. Enumerate their adjacency to the other exterior vertices and to each other. Every exterior row has exactly eight ones. The displayed formulas give $H_{II}$ and $H_{I,*}$. Require $H_{II}$ positive definite and set $H_0=H_{*,I}H_{II}^{-1}H_{I,*}$. The diagonal of the remaining rank-one Gram is known, say $q_y=H_{yy}-(H_0)_{yy}$. Reject negative entries. For $q_y>0$, the last coordinate is $s_y\sqrt{q_y}$ with $s_y\in\{-1,1\}$. For every pair test the two possible sign products against the two allowed rational Gram entries. A zero product is tested directly. A singleton allowable sign product gives a parity equation, and no allowable product rejects the configuration. Every comparison can be done with signs and squares of rational numbers.

The resulting parity equations can be solved by graph traversal. Any solution yields all required mutual products in dimension 44 and hence a full graph by the [99-point equality case](../maximal-marked-lattice/README.md). An implementation should also check $A^2=12I-A+2J$ on the recovered adjacency. Two different sign solutions giving distinct Gram matrices would produce two graphs whose adjacency difference has rank at most two, because only the last rank-one Gram changes. The trade argument below excludes this. Finding the contact words and the selected rows remains open.

## A rank-two difference is a transposition

Let $A,A'$ be adjacency matrices of two labeled graphs with the required parameters, and suppose $E=A'-A$ has rank two over the reals. A nonzero off-diagonal entry $E_{ij}$ gives an invertible principal two-by-two block. Reconstruction from that block shows
$$E_{ab}=(E_{ai}E_{jb}+E_{aj}E_{ib})/E_{ij}.$$
The zero diagonal implies $E_{ai}E_{aj}=0$ for every $a$. Hence $E=uv^t+vu^t$ with disjointly supported signed-unit vectors $u,v$. Both sum to zero since $E$ has zero row sums. Write $m,n$ for their support sizes. On the cross pairs the original graph is a union of two complete bipartite graphs between opposite signs, each with sides $m/2,n/2$. If both sizes are at least four, the common-neighbor bound forces $m=n=4$.

Subtracting the two graph equations gives $AE+EA+E^2=-E$. At sites outside both supports this forces $Au=Av=0$ coordinatewise. On cross pairs it gives $(Au)_i/u_i+(Av)_j/v_j=-1$ for $i$ in the first support and $j$ in the second. Thus the two ratios are fixed integers $a,b$ with $a+b=-1$. Using the cross adjacencies, $A$ on the span of $u,v$ has matrix
$$\begin{pmatrix}a&-n/2\\-m/2&b\end{pmatrix}.$$
Its eigenvalues are three and minus four because the subspace is centered, $A$ is diagonalizable and this action is nonscalar. Hence $(a-b)^2+mn=49$. The value $m=n=4$ would require an integer square of 33. One support therefore has size two. If it is the support of $u=e_i-e_j$, the vanishing of $Au$ outside the supports shows that $i,j$ have the same neighbors there. On the other support their adjacency is exchanged. The entire change is exactly transposition of $i,j$. Each of these two vertices changes twelve old neighbors and twelve new neighbors, since its degree is 14 and the number of common neighbors of $i,j$ equals $2-A_{ij}$.

In the reconstruction any change is confined to pairs of exterior vertices. Each such vertex has only eight old exterior neighbors, too few for this transposition. A nonzero symmetric matrix with zero diagonal cannot have rank one. This proves uniqueness for each set of contacts and $6+c$ specified pivot rows.

The [reconstructor](triangle_completion.py) takes one labeled shell and its contact words as JSON. Pivot rows are optional. It searches for the missing rows using the exact shell-neighbor equation $B f_y=2\mathbf1-(I+D)w_y$ on the wings, where $f_y$ is the proposed exterior adjacency row. Cauchy's inequality forces or forbids individual neighbors before enumeration. At each step the program selects a wing site and tries all ways to meet its remaining quota, removing other candidates incident to that site. Each feasible row occurs exactly once under this branching rule. Orthogonal projection along the pivot is a single rational rank-one update. The program emits an adjacency only after checking the graph equation entry by entry.

Without input it builds a separate 243-vertex example with parameters $(243,22,1,2)$ and verifies its graph equation. It recovers the complete 180-vertex exterior in each of two tests: from all but the last residual dimension by parity, and with two dimensions withheld by also searching a missing adjacency row. It rejects a corrupted diagonal. The controls exercise the algorithm without supplying a 99-vertex example.

## Spectrum and triangle count on the exterior

For an additional test let $F$ be the induced adjacency on the 60 vertices and let $B$ be the $36\times60$ wing-contact matrix. On the subspace of 36-vectors summing to zero in each wing, of dimension 33, the wing block of the SRG identity gives $BB^t=12I-D-D^2$. The wing/exterior block gives $F B^t v=B^t(-I-D)v$ there. The excluded three-dimensional wing-constant space has $D$-eigenvalues $3,0,0$, and its image under $B^t$ consists of global constants. Of the remaining eigenvectors, $c-1$ have $D$-eigenvalue three and vanish under $B^t$. Every other one has nonzero image, since $D$ is cubic and $(3-\theta)(4+\theta)>0$ for $-3\le\theta<3$.

Thus $F$ has eigenvalue eight once and eigenvalue $-1-\theta$ for each of the $34-c$ remaining wing eigenvalues, with multiplicities. On $\ker B$ the exterior block of the SRG equation is $F^2+F-12I=0$, since $B$ has constant column sum six. Its eigenvalues are three and minus four. The zero trace of $F$, or the dimension of the residual frame, gives multiplicities 18 and $7+c$ there. In particular $F$ is connected, its second-largest eigenvalue is three with multiplicity exactly 18, and the other nonprincipal eigenvalues are at most two. Taking cubic traces shows that $F$ contains exactly $32-t$ triangles when $D$ contains $t$. These are consequences for a candidate exterior, without an existence assertion.

**Complementary +3 shell counts.** The [12-site correspondence](plus22-twelve-wing-unions.md) and [18-site correspondence](plus27-eighteen-wing-unions.md) connect literal unions of wing components to the +3 eigenfields and the complementary rank-56 coefficients. These are distinct from the −4 norm-22 fields and do not exclude a graph or rank.
