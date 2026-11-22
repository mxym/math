# Full square coverage forces a saturated triangle

If every induced square in a Conway 99-graph belongs to a triangular prism, some triangle has all twelve possible prism partners. In particular its 99 points partition into 33 triangles by the [single saturated triangle argument](covered-spread.md). No symmetry or condition on the rank modulo seven is assumed.

Equivalently, any Conway graph with no saturated triangle contains an uncovered square. In that case one can choose a square with one of the first five [exterior degree distributions](square-profiles.md). In the fully covered case the twelve partner triangles at a saturated line partition its 36 wing sites and its 60 far sites partition into twenty more triangles. This leaves both the general uncovered case and the existence of a graph with a saturated triangle open.

## The grid forced by local diagrams

Suppose every square is covered and there is no saturated triangle. Write the type of a line as $(t/2,g)$ where $t$ is its number of prism partners and $g$ is its number of three-by-three grids. Every point lies on a grid by the [grid-free point obstruction](covered-spread.md). In a covered-root diagram an axis with outgoing and incoming degrees $o,i$ has type $(6-o,6-o-i)$. Absence of saturation gives $o\ge2$, by the [flow equations](../../conway-99-involution/uncovered-squares/covered-root/Theorem.md). Thus there are at least fourteen dirty arcs.

Here are the ten remaining root diagrams. In the fourteen-arc case the seven outdegrees all equal two. Enumerate their pairs of targets after sorting the incoming degrees, which belong to $\{0,2,3,4\}$. Test the necessary cycle through each dirty arc after removing opposite roles, as in the [covered-grid choice](covered-grid-choice.md). Every surviving labeled diagram is a relabeling of the one in the table. For fifteen through twenty arcs filter the 9,057-entry covered-root catalogue by absence of saturation and use the ternary-flow row, cell-sum and Gram equations. There are 1,559 direct exclusions at positive grid count, split between the [earlier certificates](covered-grid-choice-cert.json.gz) and [supplementary ones](grid-pentagons/line-density.json.gz).

| Number of grids at the point | Diagram codes |
| --- | --- |
| 1 | 733007422869 |
| 3 | 389074278760, 733002486440, 1557099336360, 2931409920340 |
| 5 | 389074212160, 727628534440, 727633208960, 2920672502100 |
| 7 | 710436620800 |

Call a line of type $(4,1)$ a target for this argument. In nine diagrams at least one target occurs. The other diagram is the exceptional pentagon diagram. The [nine-point obstruction](grid-pentagons/README.md) proves that no grid consists entirely of exceptional points. A target therefore exists.

Whenever one axis of a clean cell in these diagrams is a target, its other axis is also a target and the two have identical sets of two outgoing neighbors. These assertions depend only on the listed diagrams. The [line checker](grid-pentagons/verify_lines.py) tests each clean pair. Choose the unique grid $B$ on any target. At every point of the target its perpendicular line in $B$ is a target too. Intersecting these three perpendiculars gives the assertion for the other two parallel lines. Thus all six lines of $B$ are targets and their moving axes coincide at each of their nine intersections.

## The two moving axes

For $p\in B$ let $F_p$ be its ten outside neighbors. The grid is one-dominating, so the $F_p$ partition the remaining ninety sites. The ten sites of $F_p$ form five mate pairs. The two grid lines at $p$ have the same two outgoing outside axes. Their four sites form a set $M_p$; the other six belong to $F_p\setminus M_p$. To see the meaning of outgoing, root at $p$ on a grid line $L$. A dirty incoming cell contributes two fixed partner labels to $L$, a clean cell contributes two fixed grid labels, and a dirty outgoing cell contributes the pair of moving labels. Transfers along $L$ preserve the moving set and send whole mate pairs to whole mate pairs by the [triangle-neighborhood argument](covered-square.md).

For adjacent $p,q$ there is a perfect matching between $F_p,F_q$. It restricts to a bijection of the two moving axes at each end. Around any of the six grid lines its product swaps the two axes. Indeed the moving transfer has no one-cycle on mate axes. A positive one-cycle would give fixed labels and a negative one-cycle would give a six-site component with three common neighbors for a pair of sites. Choose labels $0,1$ for the two moving axes at each point. Normalize the eight tree maps as in the [pentagon enumeration](grid-pentagons/README.md). Only four binary maps are free, since the six products on triangles are prescribed. This gives sixteen tables.

For a grid line $L$, the twelve sites $M_L=\bigcup_{p\in L}M_p$ are a union of components of its cubic three-wing graph. Any far vertex sees exactly two points of $M_L$. One direct proof takes the vector $z=1_{M_L}-\tfrac13 1_{\rm wings}$, zero off the 36 wings. It has sum zero, and its restriction to the wings is a 3-eigenvector of their cubic graph since it is constant on components. Thus $z^tAz=3z^tz$. On the orthogonal complement of constants the largest eigenvalue of the Conway graph is three, so $Az=3z$. Evaluating at a far point, which has six wing contacts, gives the assertion.

Let $y\in F_s$. For each grid line avoiding $s$, one of its three positions is adjacent to $s$ and two are opposite to $s$. The contact at the adjacent position belongs to its moving set exactly when $y\in M_s$. At the four opposite positions of $s$ arrange the counts of contacts in $M_q$ in a two-by-two square. The result just proved gives every row and column sum $2-1_{y\in M_s}$. Consequently:

* If $y\in M_s$, it sees one moving site in each of two diagonally opposite positions of this two-by-two square. It also sees its mate in $M_s$ and one moving site, on the transferred axis, at each adjacent position.
* Otherwise its moving contacts are all at opposite positions. There is either one at each of the four, or two at each of two diagonally opposite positions. Two contacts at the same position belong to different axes because an adjacent mate pair already has its common neighbor in $B$.

This gives 306 unsigned contact words per table. They distinguish the starting axis and position when needed, but do not record the signs inside pairs.

## The integer contradiction

Index the eighteen moving pairs by $a$. Let $U$ have their 99-dimensional indicator columns and put $W=AU$. The matrix equation $A^2+A=12I+2J$ gives
$$W^tW+U^tW=24I_{18}+8J_{18}.$$
A point of $B$ contributes four to entry $(a,b)$ of the first term precisely when $a,b$ belong to that grid position, and zero to the second term. The remaining demand is therefore $d_{ab}=8+24[a=b]-4[\mathrm{pos}(a)=\mathrm{pos}(b)]$. For an outside point, let $S$ be the set of moving pairs among its neighbors and let $h$ be its own moving pair if present. Its contribution is $([a\in S]+[h=a])[b\in S]$. Hence the demand vector for the 171 entries $a\le b$ must be a nonnegative sum of the 306 word columns.

For each of the sixteen tables the [integer weights](grid-pentagons/moving-pair-cert.json.gz) give nonpositive score to every word and positive score to the required vector. The [standard-library checker](grid-pentagons/verify_moving.py) recomputes all words and tests these inequalities directly. This excludes the target grid and proves the theorem.

## Verification

Run the existing [covered-root catalogue verifier](../../conway-99-involution/uncovered-squares/covered-root/verify.py) and the [grid-free point verifier](covered_spread.py). Then run `grid-pentagons/verify.py`, `grid-pentagons/verify_lines.py`, and `grid-pentagons/verify_moving.py` with Python and NumPy. The pentagon verifier also uses a C++17 compiler. All exclusion certificates replay over the integers.

A [nine-triangle obstruction](triangle-array.md) rules out arranging nine disjoint triangles in three rows and three columns all inducing rook grids under full coverage. The partition above gives disjoint triangles but leaves their arrangement open.

For each pair of grids on the saturated line, their perpendicular directions span another grid at at most two of its three vertices. The [five-grid obstruction](five-grids/README.md) proves this for any line under full square coverage.
