# Rectangles cannot charge every pair of a three-prism class

Let $P$ denote the number of triangular prisms in an $\operatorname{SRG}(99,14,1,2)$, $G$ its nine-site rook grids, $B=P-6G$ its bad prisms, and $R$ its unoriented good-prism rectangles. Then
$$
 R\le\lfloor 2B/3\rfloor,\qquad G\le118.
$$
At $P=851$ at least 143 prisms must be bad. The primal lattice shells obey $y_3\ge44{,}804$ and $y_4\ge3{,}748{,}902$. These are unconditional necessary restrictions; neither a graph nor a rank is excluded as a whole.

### The local obstruction

We use the published [equal bad prism and rectangle facts](bad-prisms.md), [cube exclusion](cube-fibers.md#at-most-one-rectangle-per-equal-bad-prism-pair), and [double-cell isolation](pentagon-isolation.md). Distinct prisms of the same bad mark are disjoint and anticomplete, their class size is at most three, and an unordered pair in such a class is charged by at most one rectangle. At a bad prism $X$ with its two triangular faces, double cells are the rectangles charging $X$: each uses a parallel block through each face. Distinct rectangles at $X$ use distinct blocks on each of its two faces, since no two double cells share a row or a column.

Suppose a class contains three prisms, indexed $1,2,3$. Their common mark $s$ is a sum of two norm-four triangle marks with inner product $-2$, so $\|s\|^2=4$. Write their six face marks as $h\pm d_i$, where $h=s/2$, choosing either orientation independently at each prism. Then $\|h\|^2=1$, $\|d_i\|^2=3$, and $h,d_1,d_2,d_3$ are pairwise orthogonal: this follows from the prism products and the fact that every pair of faces from different class members is anticomplete, so has product 1.

A rectangle charging prisms $i,j$ has four original corner triangle marks $c_{ij}^{\sigma\tau}$, one for each $\sigma,\tau\in\{+1,-1\}$. The corner is a good mate of the two indicated faces $h+\sigma d_i$, $h+\tau d_j$, and anticomplete to their opposite faces. Indeed the original rectangle has four edge blocks; the two opposite pairs of third lines in these blocks give its two charged prisms. The two corners using a specified face and differing in the other sign are the other two lines of **one** parallel block through that face. Their marks therefore sum to the negative of that face. It follows, by adding rows and columns of this $2\times2$ array, that
$$
 c_{ij}^{\sigma\tau}
 =-\tfrac12h-\tfrac{\sigma}{2}d_i-\tfrac{\tau}{2}d_j
   +\sigma\tau v_{ij},
 \qquad v_{ij}\perp h,d_i,d_j .
$$
Here $v_{ij}=v_{ji}$, with signs attached to the fixed face orientations. Orthogonality also follows directly from the corner's inner products $-2,1$ with the two faces of each of the two prisms.

Consider rectangles for $ij$ and $ik$, with $i,j,k$ distinct. Fix either $\sigma$. The original corners of the two rectangles mating $h+\sigma d_i$ belong to different parallel blocks through that face by double-cell isolation. Lines from different such blocks are anticomplete: if $C,C'$ are the two off-face marks in the first block and $D$ is an off-face mark of the second, then $D$ is distinct from both (one shared mate determines its grid uniquely). Their products satisfy $(C,D)+(C',D)=-(h+\sigma d_i,D)=2$, and neither distinct-triangle product exceeds 1. Consequently
$$
 (c_{ij}^{\sigma\tau},c_{ik}^{\sigma\upsilon})=1.
$$
Expanding the left side with fixed $\sigma$ gives
$$
 1+\tau\upsilon\left((v_{ij},v_{ik})
 -\tfrac{\sigma}{2}\big((v_{ij},d_k)+(v_{ik},d_j)\big)\right).
$$
Using both $\sigma=+1,-1$ forces $(v_{ij},d_k)=-(v_{ik},d_j)$.

If all three pairs were charged, the three quantities $(v_{12},d_3),(v_{13},d_2),(v_{23},d_1)$ would be pairwise negatives, hence all zero. Yet $(c_{12}^{++},h+d_3)=-1/2+(v_{12},d_3)$ is an integer since it is a product of two graph triangle marks. This contradiction proves that a class of three supplies at most two rectangles. Sizes one and two supply at most zero and one respectively, by the earlier cube result. Summation gives $R\le\lfloor2B/3\rfloor$.

### Integer consequences

The existing [path and parity bound](triangle-grid-parity.md) is
$$
 72G-5544+2E\le3696-P+2R,\qquad E\ge\max(0,726-6G).
$$
Inserting $R\le2(P-6G)/3$ yields $68G\le7788+P/3\le7788+851/3$, so $G\le118$. At $P=851$ we get $B\ge143$ and $y_2\ge462+2\lceil143/3\rceil=558$. For the [published norm-six and norm-eight bounds](triangle-pair-packing.md#consequences-for-the-short-lattice-shells), use $h=B-[3\nmid B]$, $r=\lfloor2B/3\rfloor$ and
$$
 d=h+\min(15G,\lfloor(3696-P+2r)/4\rfloor).
$$
Scanning $0\le P\le851$, $0\le 6G\le P$ with the displayed path and parity inequality leaves 59,261 integer pairs. Both minima of the resulting lower-bound expressions occur at $(P,G,B,h,r,d)=(851,118,143,142,95,900)$: $44{,}804$ for $y_3$ and $3{,}748{,}902$ for $y_4$. The extremal parameter tuple is an arithmetic corner, not an existence claim. Run `python rectangle_class_forest.py` for the exact standard-library scan.
