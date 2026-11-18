# The Elphick–Linz–Wocjan clique inequality for strongly regular graphs

Let $G$ be a finite simple strongly regular graph on at least one vertex. Write $m$ for its number of edges, $\omega$ for its clique number, and $\lambda_1\ge\cdots\ge\lambda_n$ for the eigenvalues of its adjacency matrix. If $n^+$ counts the strictly positive eigenvalues with multiplicity, and $\ell=\min\{\omega,n^+\}$, then

$$
\sum_{i=1}^{\ell}\lambda_i^2\ \le\ 2m\left(1-\frac1\omega\right).
$$

This is the strongly regular case of [Elphick–Linz–Wocjan Conjecture 2](https://arxiv.org/pdf/2101.05229#page=9). It is **not** the statement for all graphs, which remains open, or a claim to prove the already settled two-eigenvalue Bollobás–Nikiforov conjecture. No equality classification is asserted.

[Read the proof](PROOF.md) · [Internal mathematical review](REVIEW.md)

The main point is to avoid guessing the clique number. For a primitive strongly regular graph, Elphick, Linz and Wocjan reduced their inequality to the sign of an explicit function of that number. Here we place it in an interval on which that function is concave. The neighborhood Turán bound supplies the lower endpoint. At the upper endpoint the Delsarte bound does not always suffice; a multiplicity bound combined with the Krein and absolute bounds supplies an alternative.

**Scope and verification.** This is an AI-assisted research draft. A separate internal AI review rederived the spectral identities, checked the parameter ranges, and recomputed the exact coefficient certificate. This is not external peer review or a proof-assistant formalization. The search for prior results was not exhaustive; no priority claim is made.

From this directory, with Python 3 and SymPy installed, run:

```sh
python3 check.py
python3 check_independent.py
```

The first script verifies the displayed algebraic identities and finite exceptions. The second independently derives the parameters and signs and runs bounded exact arithmetic tests, including irrational conference spectra. Formal parameter rows are not assumed to be realized by graphs. The proof applies to all sizes and does not rely on these bounded tests.

**Prior work.** The [original paper](https://doi.org/10.1016/j.laa.2023.12.010), §4.2.3, gives the strongly regular reduction, treats Type C and $\lambda=1$ strongly regular graphs, and identifies the general strongly regular case as unresolved there. [Kumar–Pragada](https://arxiv.org/abs/2407.19341) proved the higher-rank bound for graphs with few triangles under quantitative conditions; [Zeng–Zhang](https://doi.org/10.1016/j.laa.2025.01.037) also treat few triangles and line graphs with additional hypotheses. The [Coutinho–Liu–Spier–Tang–Zhang two-eigenvalue result](https://github.com/shengtongz/BN) and the [Liu–Tang–Zhang total positive square-energy theorem](https://arxiv.org/abs/2607.18044) concern different inequalities.
