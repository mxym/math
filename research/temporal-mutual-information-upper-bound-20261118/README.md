# A partial-trace test of a proposed upper bound on two-time mutual information

[Read the three-page proof](paper.pdf) · [LaTeX source](paper.tex)

This note tests a dimension bound suggested, on numerical evidence, by [Fullwood and Parzygnat (2025), §5](https://doi.org/10.3390/e27040331). The bound concerns their **signed, two-time mutual information**, not ordinary mutual information of a bipartite quantum state.

**Candidate counterexample.** A partial-trace channel takes two spatial registers of dimension d and discards the first. Prepare the input uniformly on the symmetric or antisymmetric subspace. With c = log(27/16)/6, the respective two-time mutual informations are exactly log d − (d−1)c and log d + (d+1)c (natural logs). At d = 64, the former is negative and the latter exceeds the suggested upper bound 2 log d. An output isometry gives an equal-input/output-dimension counterexample at d = 256, even accounting for the larger bound after padding. The construction has exactly two times. Unboundedness is across dimensions, not at a fixed dimension.

**Prior work.** The antisymmetric d = 2 input is exactly the singlet/partial-trace process of [Fullwood–Parzygnat, Example 4](https://doi.org/10.3390/e27040331), including their negative two-time joint entropy. Negative *mutual information* itself was already demonstrated using the [five-level Werner–Holevo channel](https://www.trureturing.org/research/fullwood-parzygnat-2025-states-over-time-subadditivity/) and subsequently in [smaller systems](https://evidencepress.org/releases/negative-mutual-information-in-time/). The five-level example with maximally mixed input already yields unboundedness below by parallel repetition. Here the same partial trace in each dimension produces linear growth in **both** directions, including failure of the proposed upper bound. For the distinction between the Jamiołkowski and Choi conventions see [Fullwood–Yang, Eq. (2.4)](https://arxiv.org/html/2608.28946v1#S2).

**Reproduction.** The general argument is analytic. Two exact computational checks are included:

- [verify_spectra.py](verify_spectra.py) uses only the Python standard library. It builds all orbit blocks for d = 2,…,7, expands their characteristic polynomials, and checks the finite witness inequalities.
- [audit_orbits.py](audit_orbits.py), implemented independently during internal review, uses Python and SymPy (tested with 1.14.0). It builds representative blocks from the Kraus operators and checks their full multiplicities at d = 2, 3, 64 and 256. It also checks three direct integer comparisons without the intermediate logarithmic bound.

Run each script with `python -O`. Rebuild the PDF with two passes of `pdflatex paper.tex` under TeX Live.

**Review status:** AI-assisted working proof, 18 November 2026. The calculation received a separate internal review, not external peer review or formal verification. No historical priority or optimality is claimed.
