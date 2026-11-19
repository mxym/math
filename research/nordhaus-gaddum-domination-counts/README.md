# Which graph and complement have the most dominating sets?

**Answer for every order $n\ge160$:** the balanced complete bipartite graph and its complement are the only maximizers. If $\partial(G)$ counts all vertex sets that dominate $G$, the maximum of $\partial(G)+\partial(\overline G)$ is
$$
2(2^{\lfloor n/2\rfloor}-1)(2^{\lceil n/2\rceil}-1)+2 .
$$

This is a large-order result for the [Keough–Shane conjecture](https://doi.org/10.2140/involve.2019.12.1175), not a proof at every order. Keough and Shane reported checking the numerical inequality through order 10. The argument here does not determine the unrestricted cases $11\le n\le159$. [Sanh](https://arxiv.org/html/2607.25188v1) already proved the inequality for bipartite graphs at every order, including a stronger bound for prescribed parts and its equality cases. No claim is made that 160 is necessary.

The [proof](PROOF.md) counts *failures* of domination as unions of families of subsets of neighborhoods, a viewpoint used in the [2024 BIRS workshop report, §3.4](https://stats.birs.ca/workshops/2024/24w5298/report24w5298.pdf). Three well-separated adjacency rows would make too many sets fail. With only two groups of similar rows, a short count forces repeated neighborhoods, and any edge breaking their two-part pattern would again produce too many failures. This argument determines both the value and all equality cases.

[SOURCES.md](SOURCES.md) distinguishes earlier quantitative bounds, the common-neighborhood formulation, and the bipartite theorem. [REVIEW.md](REVIEW.md) records an independent internal proof audit. This AI-assisted research note has not been externally peer reviewed and does not establish priority.

The proof is mathematical and does not depend on enumeration. To reproduce the auxiliary exact checks, run from this directory:

    python3 -O verify.py
    python3 -O verify_twins.py
    python3 -O independent.py
    sha256sum -c SHA256SUMS

The first two results are in [AUTHOR-CHECKS.txt](AUTHOR-CHECKS.txt), the separate audit run in [INDEPENDENT-CHECKS.txt](INDEPENDENT-CHECKS.txt). Python's standard library suffices. Source references are linked, not reproduced.
