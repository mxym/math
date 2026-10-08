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

## Exact three-row critical radius at exponent two

The [new Section 9](paper.md#9-a-complete-sharp-radius-at-three-rows-and-exponent-two) determines **exactly** the previously unspecified optimal radius in the first nontrivial arity:
`R_3(2) = 1/sqrt(3) - 1/2` (inclusive boundary). In fact, an `S_3` law with all one-point marginals uniform satisfies the three-row normalized `L^2` permanent inequality **if and only if** its TV distance from uniform does not exceed that number.

The proof is self-contained and uses an exact sharp trilinear `3x3` permanent--determinant inequality. All three principal `2x2` minors of an explicit `3x3` Gram matrix factor with nonnegative coefficients; its determinant is a nonnegative symmetric polynomial by AM--GM. The [SymPy exact checker](code/check_s3_exact.py) verifies the polynomial identities in `Q(sqrt(3))[a,b,c]`, independent of numerical optimization. Run:

```bash
python notes/sharp-robust-permanent/code/check_s3_exact.py
```

This exact `n=3,p=2` result is additional to the earlier all-arity sharp-order analysis; a complete formula for `R_3(p)` at other exponents is not yet claimed.

## Equality rigidity, quadratic phase transition, and entropy criterion

[Section 10 of the manuscript](paper.md#10-equality-classification-and-the-quadratic-saturation-barrier) classifies **every** equality case at the sharp `S_3,p=2` radius: aside from a zero row, they are the constant rows and, exactly at the boundary, singleton rows supported on an even or odd permutation as dictated by the sign of the perturbation. It proves a general **quadratic saturation barrier**: for `p>2`, a law assigning the singleton-critical mass to a permutation and positive mass to a neighboring transposition necessarily violates the `L^p` inequality. For every `2<p<3`, this yields a strict improvement over the singleton upper radius, with an explicit quantitative bound.

A fully rational `p=5/2` counterexample demonstrates that *passing every singleton test does not imply the permanent inequality* above exponent two. The [exact checker](code/check_s3_phase.py) verifies the strict rational inequalities, `S_3` parity incidence, and equality kernels. This counterexample is a **mathematical theorem** proved in the manuscript, not an inference from numerical search.

[Section 11](paper.md#11-an-exact-six-variable-entropy-criterion-for-the-remaining-exponent-problem) gives an exact necessary-and-sufficient `K_{3,3}` entropy variational criterion for the entire `S_3` problem. It proves that parity-pure entropy tests reduce precisely to singleton tests, and that each parity block has at most two distinct positive values at any interior stationary obstruction. This variational criterion does **not** by itself settle the exact best radius for `q_3<p<2`. The conjectured singleton sufficiency in that interval remains explicitly open.
