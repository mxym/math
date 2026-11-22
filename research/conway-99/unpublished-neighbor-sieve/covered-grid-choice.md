# Three alternatives under full square coverage

The [full-coverage theorem](saturated-choice.md) now forces a saturated triangle, allowing any number of grids.

Suppose every square in a Conway graph lies in a triangular prism. At least one of the following holds.

1. Some triangle has twelve prism partners and therefore extends to a partition into 33 triangles.
2. Some triangle has eight prism partners and lies on exactly one three-by-three rook grid. Four labeled-neighborhood types suffice up to relabeling.
3. Eleven disjoint induced rook grids partition the graph. The edges between any two of them form a perfect matching. Each of the 66 grid triangles has two prism partners, and each of the other 165 triangles has eight. A grid triangle can be chosen with one of two 39-site neighborhoods.

In particular, a fully covered graph either admits a partition into triangles or contains a triangle with one of the four neighborhoods in item 2. In item 3, choosing three rows in each grid already gives a partition. These alternatives are necessary and may overlap.

## Root diagrams including clean cells

Use the [root equations and integer certificate method](covered-spread.md). At a point each pair of incident triangles determines either a clean cell (one grid) or a dirty arc. For an axis with outgoing and incoming degrees $o,i$, its line has $2(6-o)$ prism partners and lies on $6-o-i$ grids. A dirty incoming cell or a grid gives two partners, and a dirty outgoing cell gives none. Both degrees differ from one by flow conservation.

Assume neither item 1 nor item 2 holds. Every axis has outgoing degree at least two, and the ordered pair $(6-o,6-o-i)$ never equals $(4,1)$. No point lies outside all grids, by the [grid-free point theorem](covered-spread.md). It suffices to determine which root diagrams with 14 through 20 dirty arcs can occur.

For 14 arcs all seven outgoing degrees are two. The allowed incoming degrees are zero, two and four. After sorting them, enumerate the two targets of each source, discarding loops and mutually opposite arcs. This gives 28,944 labeled diagrams. At an arc $a\to b$, a row belonging to its own cell is nonzero on that arc and vanishes on arcs ending at $a$ or starting at $b$. After excluding those latter arcs, the given arc therefore lies on a cycle of the bipartite role graph. Equivalently, after contracting each degree-two source to an edge on its two targets, the two targets of source $a$ must be connected even after removing the edges labeled $a,b$ and the vertex $a$. All 28,944 diagrams fail this test at some arc.

For 15 or more arcs take the [complete catalogue of covered-root orientations](../../conway-99-involution/uncovered-squares/covered-root/Theorem.md). Filtering by the axis restrictions and requiring some clean cell leaves 72, 49, 30 and 1 diagram with one, two, three and four clean cells respectively, and none with more. At a clean cell all dirty columns intersecting it vanish pointwise. For disjoint columns retain all ternary values consistent with the flow equations. The cell sums of each dirty column over a clean cell vanish because the clean column is zero and the Gram identity is symmetric. Impose the same remaining equations as for a grid-free point. Exact integer separation or an empty required cell eliminates 151 of the 152 diagrams.

The exception has five axes of type $(4,0)$ and two of type $(1,1)$. At its two grid axes the five outgoing cells carry a derangement, by the [pair-matching argument](covered-spread.md). The argument applies to any outgoing group because clean cells have no spare neighbors carrying the shared axis. At the first of these grid axes, the ten possible undirected patterns of a two-cycle and a three-cycle all fail the same equations. The derangement at that axis must be a five-cycle. The [checker](covered_grid_choice.py) reconstructs the rows and replays the [integer certificates](covered-grid-choice-cert.json.gz). The supplementary 14-arc count is independent of the catalogue.

## Consequences on the entire graph

In the exceptional diagram every point lies on exactly one grid. The grids therefore partition all 99 points. A grid has degree four at each of its nine points; any point outside sees at most one point of the grid, since each pair in the grid already has its full common-neighbor quota there. Its 90 outgoing edges account for all 90 outside points, proving the matching assertion. Each grid has six triangles. Every other triangle meets three grids and has eight partners, by the five remaining axis types at each point.

For item 2, the [triangle-neighborhood description](covered-square.md) on eight fixed labels has one common mate pair from its grid. The remaining six fixed labels support three mutually disjoint perfect matchings. There are two types with the roles fixed, up to simultaneous relabeling. The two moving axes form a two-cycle with either sign. For item 3 the two fixed labels form a common mate pair. On the five remaining axes the transfer is the derangement just tested. Indeed, the signs of an outgoing cell in the two nonroot wings are labeled by the signed neighbors in the root wing; passing from its positive root-axis pair to its matched negative pair is exactly the transfer between these two wings. A single five-cycle has two possible signs. This establishes the stated neighborhood counts without deciding whether any extends to 99 points.
