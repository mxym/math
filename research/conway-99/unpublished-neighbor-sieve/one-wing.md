# Reconstruction from the labeled exterior alone

A Conway graph exists if and only if some simple 8-regular graph on the 60 nonmate pairs of twelve labels passes the reconstruction below. The input is one adjacency matrix in that fixed labeling. The test recovers both missing lists of wing contacts and the missing wing matchings. It needs no prescribed 39-site shell, exterior-to-shell contacts, or symmetry. Searching the labeled 8-regular graphs with the required identities remains open.

## The exterior data

Fix an ordered triangle and denote its three twelve-site wings by $P,Q,R$. Transfer the labels of $P$ directly to $Q$ and $R$ along the two cross matchings. Write $n=12$, and put the mate matching $M_0$ of $P$ in the standard form $i\leftrightarrow i\mathbin{\mathrm{xor}}1$, with labels starting at zero. Each exterior vertex is uniquely identified by its two neighbors in $P$, which run through every nonmate pair once. Let $B$ be the $n$-by-60 site/pair incidence matrix in lexicographic order of the pairs. Write $F$ for exterior adjacency and $B_1,B_2$ for the unknown contacts at $Q,R$.

Every exterior point has degree eight within the exterior. The block with rows in $P$ and columns in the exterior of $A^2+A=12I+2J$ gives
$$D=B_1+B_2=2J-(I+M_0)B-BF.$$
In particular the eight neighbors of a fixed exterior label $\{a,b\}$ must form a simple eight-edge graph on twelve labels with maximum degree two. Its degree is at most one on $a,b$ and their mates. Each entry of $D$ is zero, one or two, and every column sums to four. In any fixed row of $D$ at most one entry is two. Indeed $Q_i,R_i$ already have the common neighbor $P_i$. Thus at least 48 of the 60 exterior vertices have four distinct labels in the two missing wings.

The exterior/exterior block now gives the entire rational Gram of $T=B_1-B_2$:
$$K=T^tT=2(12I+2J-F-F^2-B^tB)-D^tD.$$
Each column of $T$ sums to zero. It is zero off the positions where $D=1$, and has a signed unit at every such position. Consequently these are 60 vectors in the usual $A_{11}$ lattice of zero-sum integer twelve-tuples, of squared lengths zero, two or four.

## Rank and a bound of sixteen choices per label

The formulas extend to a graph with the same common-neighbor parameters and degree $n+2$, with $n(n-2)/2$ exterior vertices and exterior degree $n-4$. In the displayed formula for $K$ replace $12I$ by $nI$. This normalization supplies a positive control at $n=20$.

Let $M_1,M_2$ be the internal mate matchings of $Q,R$, and let $U$ be direct adjacency from $Q$ to $R$, a permutation matrix. The known intersection counts within each wing give $B_j B_j^t=(n-3)I+J-M_j$. Across $Q,R$ they give $B_1B_2^t=2J-U-M_1U-UM_2-I$. The last identity term counts the indirect path through $P$. Hence
$$TT^t=2(n-2)I-2J-M_1-M_2+U+U^t+M_1U+U^tM_1+UM_2+M_2U^t.$$
The last eight signed permutation terms have combined operator norm at most eight. On the centered label space this puts the spectrum between $2n-12$ and $2n+4$. Constants are killed. For $n=12$, $K$ therefore has rank **exactly eleven** and every nonzero eigenvalue belongs to $[12,28]$.

For label $i$, put $S_i=\{y:D_{iy}=1\}$, of size at most $2(n-2)$. Its signed row belongs to the subspace $E_i$ of the image of $K$ supported on $S_i$. To bound its dimension, identify the image with $T^t(\mathbf1^\perp)$ and lift $E_i$ back to $\mathbf1^\perp$. This lifted subspace contains $p_i=e_i-\mathbf1/n$. In the part orthogonal to $p_i$, a unit vector has total squared evaluations at least $2n-12$, all supported on $S_i$. For an orthonormal basis of that part, the sum of these evaluations at $y\in S_i$ is at most $K_{yy}-n/(n-1)$ by Bessel's inequality, since the projection onto the line of $p_i$ already uses $n/(n-1)$ of the squared length. It follows that
$$(\dim E_i-1)(2n-12)\le |S_i|\big(4-n/(n-1)\big).$$
At $n=12$ this gives $\dim E_i\le5$. On a basis of evaluation positions for this subspace a signed-unit row is fixed by at most five signs. Up to reversing the whole row there are **at most sixteen** possibilities for each of the twelve labels. At $n=20$ the same bound gives dimension at most four.

## Reconstruction

1. Compute $D,K$ and their support, rank and spectral tests from $F$. Obtain $E_i$ by imposing zeros outside $S_i$ on the column space of $K$. Enumerate its signed rows up to sign. If $y,z$ share only label $i$ in their supports, their required row product is already $K_{yz}$.
2. Retain selections of one row per label whose outer products add to $K$. The selected rows have rank $n-1$, so their linear dependence is unique up to scalar. It must have all coefficients of the same nonzero absolute value. Use its signs to orient the rows so that every column sums to zero. Simultaneous reversal merely exchanges $Q$ and $R$.
3. Form $B_1=(D+T)/2$, $B_2=(D-T)/2$. Within either missing wing the unique distinct row disjoint from a given row must be its mate, and every nonmate pair must meet once. The whole remaining cross matching is also forced. With rows at $R$ and columns at $Q$ it is $2J-B B_1^t-I-M_0-M_1$, by counting common neighbors of $P_i,Q_j$. Check that it is a permutation matrix.
4. Assemble the 99-vertex adjacency, and accept only a symmetric binary matrix with zero diagonal obeying $A^2+A=12I+2J$. Its diagonal equation gives degree 14; its other entries give both common-neighbor counts.

Every true graph passes after the specified labeling of the first wing. Conversely the final matrix test directly certifies any positive outcome.

The [reconstructor](one_wing.py) uses exact integer and rational arithmetic with python-flint. With no input it constructs and verifies the 243-vertex graph of degree 22, discards its shell and its contacts, and feeds just the labeled 180-vertex exterior to the algorithm. All twenty unsigned rows are unique in this control. The recovered adjacency agrees entry for entry with the original up to exchanging the last two parents and their wings. With a JSON adjacency matrix as its argument the script uses the Conway parameters.

## Choosing a first row

Write $t$ for the number of triangles in the induced graph on the 36 wing sites. These triangles use one site in each wing, since the edges between two wings form a matching. There are 36 edges between different wings. Of these, $3t$ have their common neighbor in the wings, and every other one has its unique common neighbor in the exterior. Edges between mates are already completed by their triangle parent. Thus for the number $e_y$ of edges among the six wing contacts of $y$ we have $\sum_y e_y=36-3t$. At least $24+3t$ exterior vertices have $e_y=0$.

At exactly $t$ labels the sites $Q_i,R_i$ are adjacent, in which case their common neighbor is $P_i$. At every other label at most one exterior site can see both $Q_i,R_i$, since they already share $P_i$. Directly matched $P_i,Q_i$ and $P_i,R_i$ cannot occur together when $e_y=0$. It follows that at least $12+4t$ sites $y$ have six independent contacts carrying six different first-wing labels. Each such $y$ lies in exactly one triangle in the exterior. Its six contacts pair with six of its eight exterior neighbors inside its neighborhood, leaving the other two paired to each other.

Choose one such $y$ and relabel its two first-wing neighbors as $0,2$. Its other four contact labels form a four-subset $S$ avoiding $0,2$. In the pair labeling, its eight exterior neighbors form a simple graph $H$ on the twelve labels, omitting mate pairs and the root pair $(0,2)$. The displayed equation for $D$ prescribes its degree at $i$ as $2-1_{i\in\{0,1,2,3\}}-1_{i\in S}$. The group preserving the mate pairs and the root pair has order $2\cdot 4!\cdot 2^4=768$. The exact first-row census under this group is as follows.

| Four labels | Subsets in orbit | Labeled rows per subset | Orbits of rows with subset |
| --- | ---: | ---: | ---: |
| 1,3,4,5 | 4 | 6,226 | 51 |
| 1,3,4,6 | 24 | 6,836 | 261 |
| 1,4,5,6 | 48 | 15,457 | 1,045 |
| 1,4,6,8 | 64 | 17,010 | 1,458 |
| 4,5,6,7 | 6 | 34,762 | 367 |
| 4,5,6,8 | 48 | 38,194 | 2,592 |
| 4,6,8,10 | 16 | 41,940 | 953 |

The [enumerator](one_wing_seeds.py) selects all later neighbors of the least unprocessed label according to its prescribed degree. For each subset it partitions the resulting rows by the subgroup fixing that subset. The total is 4,732,468 labeled pairs $(S,H)$ in 6,727 orbits. These are starting cases with the remaining edges of $F$ unspecified.

## A determinant test on the exterior

Let $I$ consist of eleven independent columns of $K$, let $G=K_{II}$ and take an integer row basis $X$ for $K_{*,I}$ by Hermite normal form. The rows give product coordinates against the chosen eleven vectors, so the generated lattice has determinant $\det(X)^2/\det(G)$. The columns of $T$ belong to the centered integer lattice $A_{11}$, which has determinant twelve. Consequently this ratio must be twelve times an integer square. The reconstructor checks this before enumerating signed rows. In the 243-point control the analogous index in $A_{19}$ is 81.

If the index is one, even the subspace alone allows at most one signed row on each prescribed support, up to sign. Indeed an integer vector in the real image of $K$ has the form $T^t a$ with $a$ centered and integral on the column lattice. In the index-one case $a$ lies in $A_{11}^*$. A nonzero element of that dual has norm squared at least $11/12$ because its coordinate differences are integers and $12\|a\|^2=\sum_{i<j}(a_i-a_j)^2\ge11$. There are at least eleven unequal pairs for nonconstant coordinates. The spectral bound gives $\|T^t a\|^2\ge 11$. If two nonproportional signed rows have the same support, their half sum and half difference are nonzero integer vectors of disjoint supports with total squared length at most twenty. This contradicts the lower bound of eleven for each one.
