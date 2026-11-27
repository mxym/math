# A six-dimensional kissing code cannot exceed 72 around an integral core of 22 antipodal pairs

**Theorem.** Let $C\subset S^5$ have $x\cdot y\le 1/2$ for distinct points. If $C$ contains 22 antipodal pairs whose representatives have mutual inner products in $\{0,\pm1/2\}$, then $|C|\le72$. Every other point of $C$ is arbitrary. The bound on cardinality is attained by $E_6$; **22 is sufficient, not asserted necessary**.

Equivalently, if a 73-point code exists, in every selection of 22 of its paired axes at least two have acute angle strictly between $60^\circ$ and $90^\circ$. The condition is about the **actual angles inside one selected core**, not all code angles, and no line-system orientation or root system is prescribed in advance. This does not prove the unrestricted six-dimensional kissing number.

We use radius $\sqrt2$ below, so the kissing inner-product cutoff is $1$.

## 1. Only two geometries of the core

Take the integer span of one representative of each selected line. It is an even integral lattice: choose a linearly independent subfamily and use the inverse of its integral Gram matrix to see that all coefficients have a bounded common denominator. Its norm-two vectors form a finite reduced simply-laced root system, since reflections $y\mapsto y-(y\cdot r)r$ preserve the lattice for every such $r$. The [ADE classification](https://ocw.mit.edu/courses/18-745-lie-groups-and-lie-algebras-i-fall-2020/mit18_745_f20_lec_full.pdf) now suffices. Rank at most five gives at most 20 axes, and any reducible system in rank six has at most $20+1=21$. Type $A_6$ also has only 21. The selected lines must therefore occur in a $D_6$ or an $E_6$. We bound each case separately.

## 2. The exceptional frame: a simultaneous assignment of sites to missing roots

Choose 22 paired axes in an $E_6$; call its other 14 axes weak. An outsider is any point not itself an $E_6$ root. Its *mask* $B(x)=\{r\in E_6:r\cdot x>1\}$ consists of signed roots on the weak axes. The [exact mask theorem](KissingE6GlobalMaskCapacity.md) proves $5\le |B(x)|\le16$ and that two outsiders of a kissing code cannot share a mask.

Here is the sufficient certificate we seek for each weak-axis set. Give every possible site mask a **color which is one of its own signed blockers**; two masks with the same color must be geometrically incompatible. Then any simultaneous collection of outsiders uses distinct colors, all corresponding to absent original roots. Replacing the outsiders by those original roots injectively gives the count $|C|\le72$; no actual movement is required. Unlike imposing a fixed sign on every weak axis, this argument allows both signs of any weak axis to be absent.

The [exceptional-frame replay](verify-kissing-six-integral-core-e6.js) builds the full conservative site dictionary from the [earlier chamber calculations](KissingE6TwentyPairs.md). There are 357,444 candidate signed masks before restricting to a weak-axis set. The norm-two section of each Weyl chamber cell lies in its certified rational outer hull. To discard a pair, all relative chambers must rule it out. In addition to the previous product tests, the checker may separate the sum of two outer hulls from the closed Euclidean ball of squared radius 6: for actual sites, $\|x+y\|^2=4+2x\cdot y$, so strict separation proves $x\cdot y>1$. A proposed supporting vector is rounded to an integer vector and tested on all generators with exact arithmetic. A failed numerical search merely retains the pair.

For the orbit census, choose the $D_5$ equator for which the 16 complementary axes contain the most weak axes. Quotient those 16 coordinates by the order-1,920 equator stabilizer, and the 20 equatorial coordinates by the remaining stabilizer. Check for a lexicographically smaller representative in every one of the 27 equator placements with the same maximum. There are **79,034** weak-axis orbits; an independent Burnside coefficient calculation on all 51,840 projective group elements gives the same count.

If at most one weak axis lies in the chosen equator, the [38-of-40 signed $D_5$ theorem](KissingPartialD5D6Equators.md) applies directly. Otherwise the checker tests list colorings and explicitly verifies the assigned color and every forbidden collision. A supplementary exact test handles small lists without a coloring: find a maximum matching of sites to their signed blockers; if it covers the sites, every subfamily has an injection. Otherwise the unmatched sites and their alternating forest give a deficient set $S$; the complementary sites are already matched to blockers outside $N(S)$, so only $S$ needs checking. Disjoint incidence components separate. A conflicting pair can be resolved by excluding one site, or by excluding its incompatible neighbors. Failure to resolve a case is an error, never success. The replay partitions the 79,034 cases into 20 equatorial cases, 10,331 empty site lists, 45,236 directly colored lists, eight lists solved by recoloring, and 23,439 matching/branch checks. All pass.

## 3. The classical frame: a rational cap cover for each punctured $D_6$

Write the 30 $D_6$ axes as $e_i\pm e_j$, $1\le i<j\le6$. Choose 22 paired axes and let $W$ consist of the other eight. Every point not among the 44 prescribed roots lies in
$$
P_W=\{x\in[-3/2,3/2]^6: |r\cdot x|\le1 \text{ on the 22 prescribed axes}\},
\quad \|x\|^2=2 .
$$
There are **653** orbits of $W$ under signed coordinate permutations. For 648 orbits the [classical-frame replay](verify-kissing-six-integral-core-d6.js) supplies at most 14 nonzero integer directions $h$. For each direction put
$$
 b_h=\big\lceil4096 \sqrt{3(h\cdot h)/2}\big\rceil/4096.
$$
The verifier proves every vertex of $P_W\cap\{|h\cdot x|\le b_h\text{ for all listed }h\}$ has squared norm strictly less than 2. Thus every additional sphere point lies in an **open** angular cap of radius $30^\circ$ about some $h$ or $-h$. A cap contains at most one kissing point by the spherical triangle inequality, including when the kissing separation equals $60^\circ$. There are at most 28 caps, giving $44+28=72$. Each of the five remaining orbits has a coordinate $D_5$ with at most one weak axis, already covered by the same equatorial theorem.

Here are the details of the exact polytope replay. At an original vertex the independent active equalities are $x_i=\pm x_j\pm1$ or $x_i=\pm3/2$. In each connected component, signs and integer shifts express every coordinate through one parameter. Full rank forces either a box endpoint or a cycle determining twice the parameter. Hence every vertex lies on the half-integer grid of the box. Enumerate those feasible grid points with active normals of rank six. Add the rational cuts one at a time. New vertices can only be intersections of the cutting plane with an old edge. The endpoints of an edge share active normals of rank five, so the verifier takes every crossing pair passing this rank test, computes its intersection in integer homogeneous coordinates, and retains the previously feasible vertices. Active normals of a new vertex are exactly the old common constraints plus the cutting plane, with duplicate records merged. Ranks, intersections, rounded square roots and final squared norms are all checked by integer arithmetic. This proves a covering of the **entire sphere section**, not just of sampled directions.

**Replay:** run the two linked scripts with Node.js. They have no package or network dependencies. The $E_6$ script regenerates the orbit census, chamber tests and colorings; the $D_6$ script regenerates all weak-axis orbits and independently checks the provided integer directions. Neither the numerical optimizers used to search for cuts nor a trust assumption about their covering quality are needed.
