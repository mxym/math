# At most fourteen rook grids through a point

In a strongly regular graph with parameters $(99,14,1,2)$, every vertex belongs to at most fourteen induced three-by-three rook grids. This local exclusion applies to all four remaining Seidel ranks.

The [preceding cell classification](seventeen-exclusion.md) excludes more than fifteen grids through a point. In the fifteen-grid case the six missing pairs form $K_{2,3}$. Label the axes in its parts by $0,1$ and $2,3,4$, leaving $5,6$ unused. Write $C_a$ for the four vertices whose two signed parents are on the axes in $a$. The eight regular cells are indexed by $01,05,06,15,16,23,24,34$. Each is a square with a bijective matching into every cell with disjoint axes and no edges to any other cell meeting one of its axes.

At a regular cell the ten neighbors of each vertex in disjoint cells pair off into five triangles with that vertex. Their two cells must be disjoint or both among the six missing pairs. Enumerate these pairings and choose a multiset of four for each regular cell. For a triple of cells, impose even triangle count whenever it has a pair of disjoint regular endpoints, or a pair of disjoint grid cells all three of whose common disjoint cells are grid cells. These are precisely the evenness tests of the [earlier count](seventeen-exclusion.md). On triples containing several regular cells the counts computed from each must agree. An exhaustive enumeration gives 90 count profiles. For each, the counts uniquely determine the unordered four pairings at each regular cell. Permuting axes within the three parts of sizes two, three and two partitions the 90 profiles into eight orbits of sizes $6,6,6,12,12,12,12,24$. This relabels the diagram about the chosen point and assumes no automorphism of the graph.

## Testing the actual neighbors

At each regular cell label a vertex by its two parental signs, written as a two-bit number $x$. Its two neighbors in its own cell have labels $x\mathbin{\mathrm{xor}}1$ and $x\mathbin{\mathrm{xor}}2$. Allow every assignment of the four site pairings of the profile to these four labels. At other cells, number the four vertices arbitrarily. Use one unknown perfect matching for each disjoint cell pair with at least one regular endpoint.

If the pairing chosen at $x$ in $C_a$ pairs cells $b,c$, its contacts in $C_b,C_c$ have to be adjacent. Impose this whenever $b$ or $c$ is regular, so that their mutual matching has been introduced. For two points $x,y$ in distinct regular cells $a,b$, count one path for each vertex in a common disjoint cell matched to both. Call this count $N(x,y)$.

* If $a,b$ meet in axis $i$, the only other possible common neighbor is the signed parent on $i$. The two vertices are nonadjacent. Thus $N(x,y)$ plus the indicator that the two signs on $i$ agree equals two.
* If $a,b$ are disjoint, add to $N(x,y)$ the number of the two internal neighbors of $x$ matched to $y$ and the number of the two internal neighbors of $y$ matched to $x$. Add one more if $x$ is matched to $y$. The sum must equal two, since adjacent vertices have one common neighbor and nonadjacent vertices have two.

For these two counts every possible intermediate vertex has been accounted for. An intermediate cell vertex outside $C_a,C_b$ must have axes disjoint from both since both endpoints are regular. The root has no neighbors in either cell.

The [checker](fifteen_grid_exclusion.py) constructs one Boolean feasibility problem for each orbit. Each of the eight systems is inconsistent. Any graph with the hypothesized point would satisfy its orbit's system. This excludes the fifteen-grid case. The argument places no lower bound on the number of grids through a vertex.

## Reproducing the finite check

Use Python with the `python-sat` package installed in the interpreter. From this directory run

```sh
python fifteen_grid_exclusion.py --proof-dir /tmp/conway-fifteen-proofs
```

The directory contains one DIMACS formula and one DRAT refutation per orbit. To verify each refutation with a separately built `drat-trim` checker, run

```sh
for i in 1 2 3 4 5 6 7 8
do
  drat-trim "/tmp/conway-fifteen-proofs/case-$i.cnf" "/tmp/conway-fifteen-proofs/case-$i.drat" || exit 1
done
```
