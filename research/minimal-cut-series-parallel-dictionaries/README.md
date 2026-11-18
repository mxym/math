# The growth rate of minimal vertex cuts in finite series/parallel dictionaries

Start with a finite list of connected graphs, each with two designated terminals, and allow a single edge as well. Assemble disjoint copies in series or in parallel, in any recursive arrangement. The constituents need **not** be planar. How many inclusion-minimal vertex sets can disconnect the assembled graph?

For a basic cell $B$ with $p_B>0$ internal vertices, let $h_B$ count inclusion-minimal separators of its terminals that leave exactly two components. Then the growth rate is
$$
\rho=\max\bigl(\{3^{1/3}\}\cup\{h_B^{1/p_B}:p_B>0,\ B\text{ in the dictionary}\}\bigr).
$$
More precisely, the maximum number of global minimal cuts among the resulting $n$-vertex graphs has $n$th root tending to $\rho$ along **all orders**. So does the maximum number of clean separators of the designated terminals. A path with three internal vertices accounts for the term $3^{1/3}$; repeat a winning cell in parallel and use short paths to fill any leftover order. The upper bound works for arbitrary recursion by tracking also the graph obtained by adding an edge between the terminals.

The [preceding parallel-template result](../minimal-cut-parallel-nonattainment/README.md) gives strict inequality between this finite-dictionary rate and the unrestricted Erdős–Nešetřil growth constant. Its value is **not** determined here. These claims concern inclusion-minimal **vertex** cuts, not minimum-cardinality cuts, edge cuts, or all fixed-treewidth classes. The exponent for the planar, ordinary two-terminal series-parallel and treewidth-at-most-two specializations is already implicit in earlier results; it is not claimed as new.

- [Proof for arbitrary finite dictionaries](PROOF.md)
- [Full-order lower bound and block specialization](ALL-ORDERS.md)
- [Prior work, the planar implication, and search limits](SOURCES.md)
- [Independent mathematical review](REVIEW.md) and [recorded finite checks](CHECKS.txt)

Run the two standard-library Python programs with `python3 -B -O verify.py` and `python3 -B -O planar_check.py`. Independently compile and run `c++ -O2 -std=c++17 independent.cpp -o /tmp/series-cut-check && /tmp/series-cut-check`. The finite programs test the cut identities and the planar one-way implication; the proof establishes the asymptotic result.

AI-assisted research, independently checked internally by a second AI. Not externally peer-reviewed; no priority claim.
