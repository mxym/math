# MaxCut versus random-cut imbalance: all unweighted simple graphs

For any finite simple graph, the maximum cut is at least two fifths of the edge count plus eight fifteenths of the expected absolute difference between the two internal edge counts in a uniformly random cut. Among graphs with at least one edge, equality holds precisely for a triangle or a five-clique with any number of isolated vertices.

Braverman, Efremenko, Kol, Saxena and Zhang conjectured this for arbitrary nonnegative weights, and had already proved it for cliques and for unweighted graphs with at least a billion edges. Their examples K₃ and K₅ were already known to be tight. The result here removes the size threshold for unweighted simple graphs and rules out any other unweighted extremizers. It does **not** resolve the general weighted conjecture, establish the one-round channel resilience 7/23, or give a protocol.

The [proof](PROOF.md) combines the Edwards–Erdős bound with de Caen’s inequality in orders ≥17. For smaller orders convexity reduces each vertex/edge count to one degree vector, leaving 575 integer comparisons. The two checking programs agree on every row minimum and equality case.

- [Sources and search boundary](SOURCES.md)
- [Independent internal review](REVIEW.md)
- [Reproduction output](CHECKS.txt)

Run `python3 -B -O verify.py` and `python3 -B -O independent.py`. Both use only the Python standard library. AI-assisted research draft, not externally peer reviewed. No guarantee of bibliographic priority.
