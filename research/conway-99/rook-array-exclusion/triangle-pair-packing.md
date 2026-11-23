# Packing equal-prism partners at an anticomplete pair of triangles

Let $A,B$ be two disjoint triangles with no edges between them in a strongly regular graph with parameters $(99,14,1,2)$. Count ordered pairs $(E,F)$ of triangles for which $A\cup E$ and $B\cup F$ are distinct triangular prisms with the same mark. The order specifies which of the two root triangles each partner belongs to. **There are at most three such pairs.** In particular $A,B$ have at most three common good prism mates. If $A,B$ are faces of two distinct equal-mark bad prisms, they have at most two common good mates.

Globally, for $P$ induced triangular prisms, $G$ nine-vertex rook grids and $B_0=P-6G$ bad prisms, this gives
$$
13P\le9240+16B_0,\qquad 32G\le3080+P,\qquad G\le122 .
$$
At $P=851$ at least 119 prisms are bad. The [squared-norm-eight count](../primal-norm-eight/README.md) consequently gives at least **3,724,902** vectors at every surviving rank. The existence question remains open.

## The 39 vertices and the 15-subsets

Use the [graph marks and equal-prism lemma](../rank-34-short-support/README.md#equal-images-with-equal-coordinate-sums). Lowercase letters denote triangle marks. Distinct triangle marks have inner product between $-2$ and $1$, with $-2$ characterizing prism mates and $1$ characterizing anticomplete triangles. Indeed for disjoint triangles the product is one minus their number of cross edges, which form a matching. Intersecting distinct triangles have product zero. A triangle has squared norm four, so its mark identifies it uniquely.

Each triangle has 36 distinct outside neighbors. For $A,B$ the nine nonadjacent cross pairs have two common neighbors each. An outside vertex sees at most one point of either triangle, so these witnesses are 18 distinct vertices. The set $Z$ of vertices outside $A,B$ seeing neither has size $99-6-36-36+18=39$.

For a partner pair $(E_i,F_i)$ the equal-prism lemma makes the two prisms disjoint and anticomplete. In particular $E_i,F_i$ have 18 common outside contacts by the same argument. An outside vertex seeing both faces of one prism must see the two ends of a matching edge. Unmatched endpoints already have their two common neighbors in the prism. The unique third vertex on each matching edge gives precisely three double contacts, called its caps. The two equal prisms have the same three caps, since their common vector $(A_\Gamma-3I)1_X$ records two at the double contacts, one at the single contacts, and zero on the prism. Here $A_\Gamma$ is the adjacency matrix. Thus exactly three of the 18 contacts of $E_i,F_i$ also see a root triangle: they see both. The other **15** form a subset $S_i$ of $Z$.

For different partner pairs, $a+e_i=b+f_i$ implies $f_j=a+e_j-b$. Thus
$$
(e_i,f_j)=(e_i,e_j)-3.
$$
The two $E$ faces are different, since the mark identity determines $F$ from $E$. Also $E_i$ cannot equal $F_j$, since only the former is a prism mate of $A$. The inner-product bounds force $(e_i,e_j)=1$ and $(e_i,f_j)=-2$. In particular $E_i,F_j$ form a prism. A vertex of $S_i\cap S_j$ sees both its faces and is outside that prism, as every point of $E_i$ or $F_j$ sees a root. Consequently $|S_i\cap S_j|\le3$. Four partner pairs would occupy at least $4\cdot15-6\cdot3=42$ of the 39 vertices by the first two terms of inclusion-exclusion.

A common good mate $C$ supplies two grids with parallel triples $(A,C,E)$ and $(B,C,F)$. The marks of the three parallel triangles of a grid sum to zero, so $a+e=b+f=-c$. Distinct $C$ give distinct partner pairs. A specified equal-mark bad prism pair gives one further partner pair at its chosen faces. It cannot be among the good ones, since a prism with a third grid line is good. These observations give both common-mate bounds.

## Rectangles and the grid count

Use the [rectangle count](bad-prisms.md#rectangles-of-good-prism-mates). Write $R$ for the number of unoriented four-cycles of good prism mates, $g_T$ for the number of grids containing the triangle $T$, and $H$ for the number of unordered pairs of distinct bad prisms with equal mark. The 27-site forbidden array ensures that each rectangle charges an unordered pair of equal-mark **bad** prisms $X,Y$.

Fix a face $A$ of $X$ and $B$ of $Y$. Of the four original lines of any rectangle charging $X,Y$, exactly one was a common good mate of $A,B$. In the notation of the rectangle count, the two chosen faces are $K_{ij}$ from opposite diagonals and share exactly one index. The original line with this index determines the rectangle: its unique grid with $A$ gives another original line, its grid with $B$ gives a third, and the grid of that third line with the other face of $X$ gives the fourth. Thus the number of rectangles charging this pair is at most two by the local theorem. In particular $R\le2H$.

Let $D_g=\sum_T\binom{g_T}{2}$. The length-two path bound gives $4D_g\le3696-P+2R\le3696-P+4H$. Also $\sum_Tg_T=6G=P-B_0$, there are 231 triangles, and $g(g-1)\ge6g-12$ for integral $g$. Each bad class has size at most three, so $H\le B_0$. Together these inequalities give
$$
12(P-B_0)-5544\le4D_g\le3696-P+4B_0 .
$$
Substituting $B_0=P-6G$ proves the stated bounds because $P\le851$. At $P=851$, $B_0\ge851-6\cdot122=119$, and the [norm-four count](bad-prisms.md) gives at least $462+2\lceil119/3\rceil=542$ vectors.

## Consequences for the short lattice shells

$D_g$ is exactly the number of unordered equal-mark pairs of good prisms. Indeed a good prism's sum is minus the mark of its unique third line. Each of the $g_T$ grids through that line supplies precisely one such prism. The good and bad marks are disjoint. The total number of equal-mark prism pairs is therefore $D=D_g+H$.

Write $b=P-6G$. Partitioning $b$ bad prisms into classes of size at most three gives $H\le h=b-[3\nmid b]$. A class of three attains one pair per prism, and every nonempty smaller class loses one. Since $g_T\le6$ (at a fixed point of $T$ its second grid axis determines the grid), $D_g\le15G$. For $6G=231q+s$ with $0\le s<231$, the least possible $D_g$ among integer grid counts is $231\binom q2+sq$ by balancing. Hence the admissible totals satisfy
$$
231\binom q2+sq\le D_g\le d_g=\min\left(15G,\left\lfloor(3696-P)/4\right\rfloor+h\right),
\qquad D\le d_g+h .
$$

Use the actual grid count $G$ and this upper bound for equal-mark pairs in the [earlier norm-six and norm-eight collision counts](../rank-34-short-support/README.md#combining-the-bounds). Their losses are counted per grid and per equal-mark pair. Include the [additional norm-eight family](../primal-norm-eight/README.md), which has at least $2079-9G$ eligible bowties. With $d=d_g+h$ this gives
$$
\begin{aligned}
 y_3&\ge24948+\max(0,7392-2P-4d)+2(20790-9P-36G),\\
 y_4&\ge1398474+765072+18P-48d+2(831600+36P-2286G)\\
    &\hspace{2em}{}+96(2079-9G)+103(8316-6P).
\end{aligned}
$$
Over the admissible integer pairs $0\le P\le851$, $0\le6G\le P$, the resulting lower bounds are **44,328** and **3,724,902** respectively. Both minima of the bounds occur at $P=851$, $G=122$, $h=118$, $d=947$. One can verify the minima without enumerating the parameters. Dropping floors and using $h\le P-6G$ gives $d\le924+7P/4-12G$. Consequently $y_3\ge70224-27P-24G$ and $y_4\ge4838526-612P-4860G$. At $(851,122)$ these linear expressions are 44,319 and 3,724,794. Lowering either integer parameter by even one raises both past the claimed minima. At the corner the integer bound $d=947$ gives the stated values directly. These parameter values need not be realizable. The [arithmetic checker](triangle_pair_packing.py) verifies the two minima with standard-library Python.

The later [cube exclusion](cube-fibers.md#at-most-one-rectangle-per-equal-bad-prism-pair) sharpens the rectangle multiplicity to one and the grid bound to 120.
