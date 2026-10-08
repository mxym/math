# Robust permutation permanent inequalities: all arities, sharp-order radius

This note proves a quantitative all-arity transfer of the robust four-row permanent inequality in the OpenAI/math September 26, 2026 Thorp-shuffle manuscript. The result gives an explicit total-variation neighborhood of the uniform permutation law, conditional on uniform one-point marginals, on which the normalized permanent inequality holds for **every** exponent strictly above the sharp uniform-law exponent
`q_n = n log(n) / log(n!)`. It proves that the admissible perturbation radius has the *optimal linear order* as `p` approaches `q_n`.

**Primary result:** [Complete manuscript and proof](paper.md), Theorems 1--2 and equations (4)--(11). This note is independent of repository entries 001--009 and does not revise or duplicate 005. The induced tensorization allows independent, nonidentical perturbations at each coordinate.

For `q_n < p <= 2`, set `B_n=(1+2n)^(n-1)-1`. A rigorous sufficient radius is
`TV(nu,uniform) < (p-q_n)/(4*n^4*B_n)`.
A cyclic-subgroup mixture proves an explicit upper bound on any universal radius and sharpness of its *linear order*. Without exact uniform one-point marginals the inequality fails; at `p=q_n` it is not stable under arbitrarily small marginal-preserving perturbations.

The manuscript imports one published theorem: Bristiel--Caputo (2024), Corollary 1.14, the sharp uniform-law permanent inequality. Every new quantitative step is written in full. No numerical experiment or solver output is a proof input.

## Reproduction

Using standard Python 3.9 or later, with no dependencies:

```bash
python notes/sharp-robust-permanent/code/check_examples.py
```

The program uses exact integers and fractions to verify algebraic identities, four explicitly certified exponent comparisons, small permutation marginal identities, and illustrative violating cyclic mixtures. It is intentionally **not** presented as a finite verification of the infinite family of inequalities: the mathematical proof is in [paper.md](paper.md).

## Provenance and verification status

- **Known theorem:** A. Bristiel and P. Caputo, *Entropy inequalities for random walks and permutations* (2024), Cor. 1.14, DOI: [10.1214/22-AIHP1267](https://doi.org/10.1214/22-AIHP1267).
- **Inspiration:** [OpenAI, *A strict four-row permanent inequality and permutation moments*](https://github.com/openai/math/blob/main/preprints/A-strict-four-row-permanent-inequality-and-permutation-moments-September-26-2026/build/sections/02-permanent.tex) (Sept. 26, 2026), Section 2, proved existence of a non-sharp exponent and radius for four rows.
- **Derived here:** an explicit radius for every arity, full permitted exponent range strictly above the sharp threshold, necessary marginal condition, a cyclic endpoint obstruction, a sharp-order two-sided radius estimate, tensorization.

**Status:** full proof draft and exact illustrative checker; awaiting independent mathematical review and literature novelty assessment. Not a Lean formalization, formal verification certificate, priority assertion, or external peer review.

## Sharp single-atom modulus (subsequent strengthening)

[Section 8 of the proof](paper.md#8-further-result-the-exact-local-single-atom-tv-modulus) also proves the sharp concentration coefficient
`|nu(sigma)-1/n!| <= (n-2)/n * TV(nu,u)`
for any uniform-one-point-marginal law, with exact attainment for every sufficiently small TV distance. A disjoint-support construction combining the identity, uniform derangements, and uniform transpositions establishes sharpness. It improves the upper critical-window radius coefficient by a factor `n-2` over the initial cyclic-subgroup witness, without changing the already proved optimal linear order.

The additional [rational witness checker](code/check_atom_modulus.py) enumerates `S_n` for `n=3,4,5,6` and verifies the constructed probability distributions, matching marginals, TV values, and atom excesses exactly. Run `python notes/sharp-robust-permanent/code/check_atom_modulus.py` from the repository root. This only certifies finite witnesses; the proposition for every `n>=3` is proved mathematically in the manuscript.
