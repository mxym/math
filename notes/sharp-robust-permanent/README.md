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

## Exact critical window below exponent two

[Theorem 12 and its full analytic proof](paper.md#12-exact-critical-radius-on-an-entire-interval-below-two) prove an actual **interval**, not just the endpoint `p=2`: there exists `p_0\in(q_3,2)` such that

```math
R_3(p)=3(3^{-3/p}-1/6) \qquad (p_0\le p\le 2).
```

This combines uniform strict local estimates near **every** classified `p=2` extremizer with a strict compactness argument on the complement. No numerical optimizer or discretization is used. The existence of `p_0` is rigorous but **non-effective**; no particular numerical exponent below two has been certified by this proof. By contrast, Corollary 8 proves the same singleton formula is strictly *incorrect* as soon as `2<p<3`.

[Proposition 13](paper.md#13-exact-infinitesimal-entropy-obstruction) computes the exact quadratic entropy threshold `p\ge 3/2+9|t|` for any full-support `nu_t`. It is a necessary local condition, not a global sufficiency assertion. The fully exact `q_3<p<p_0` interval and the optimal numeric value of `p_0` remain unresolved.


## Explicit local certificates and doubly transitive extension

[Section 14](paper.md#14-fully-rational-local-stability-neighborhoods) makes the two local estimates used in the one-sided exact interval quantitative and rational. Uniformly for \(q_3\le p\le2\), a mean-zero \(1/1000\) perturbation of the constant triple has permanent deficit at least \(V/100\); an off-diagonal \(1/100\) perturbation of an even-permutation singleton triple has deficit at least \(S/1200\). [Exact integer checker](code/check_local_gaps.py). These local estimates **do not certify a specific \(p_0\)**, because the compact complement is still treated qualitatively.

[Theorem 15](paper.md#15-a-sharp-atom-modulus-theorem-for-all-doubly-transitive-groups) extends the optimal atom-concentration mechanism to **every finite doubly transitive permutation group**. For group \(G\) of degree \(n\ge3\) with minimal degree \(m(G)\), the sharp coefficient relating one atom's deviation from uniform to total variation is \((n-m(G))/n\), under exact uniform one-point marginals. Explicit identity/derangement/minimum-support mixtures attain equality. This includes symmetric groups \((n-2)/n\), alternating groups \((n-3)/n\) for \(n\ge4\), and affine \(\operatorname{AGL}(1,\mathbb F_q)\) groups \(1/q\). The [pure-rational checker](code/check_doubly_transitive.py) replays nine finite witnesses; the all-group proof is analytic, not an extrapolation of enumeration.


## Two-subset exact formula and universal orbital duality

[Theorem 16](paper.md#16-exact-non-doubly-transitive-obstruction-the-edge-action-of-s_5) proves that for the S5 action on the ten edges of K5 the **sharp atom-vs-TV coefficient is exactly 1/3**, strictly below the minimal-degree bound 2/5. An explicit dual function built from fixed-edge and adjacent-edge counts has range exactly 1/3, and identity/3-cycle versus transposition probability mixtures attain equality. Its [fully rational 120-permutation checker](code/check_edge_action_s5.py) independently verifies all seven cycle types, all 100 edge-image marginals and the sharp primal-dual equality.

[Theorem 17](paper.md#17-exact-sharp-atom-modulus-for-every-two-subset-action-of-s_n) extends the S5 example to the **complete infinite family** of natural Sn-actions on unordered vertex pairs. The exact sharp constant is

\[
C_n=
\begin{cases}
(n^2-2n+8)/[(n+2)(n+4)],&n\ge4\text{ even},\\
(n^2-n+4)/[(n+3)(n+4)],&n\ge5\text{ odd}.
\end{cases}
\]

The proof gives simple all-n **quadratic dual inequalities** and matching **explicit class-mixture primal measures** in each parity. It strictly improves the minimal-degree coefficient for every n≥5. The [independent finite conjugacy checker](code/check_all_two_subset_actions.py) uses only integer/Fraction arithmetic to exhaust all integer partitions for 4≤n≤40 and verify the rational formulas, dual inequalities, and matching moment/positivity certificates. This finite replay is supplementary; the analytic proof covers every n≥4.

[Theorem 18](paper.md#18-universal-orbital-primal-dual-theorem-for-finite-permutation-actions) proves an **exact general framework** valid for any finite permutation group action: its sharp single-atom TV response equals both a rational primal LP on class-invariant probability laws and a dual *orbital-count oscillation* LP. The theorem proves rational optimal certificates and existence of centrally symmetric disjoint-support extremal probability measures (when the coefficient is positive). The earlier 2-transitive and pair-action results become rank-two and rank-three instances. The full higher-order k-subset problem, k≥3, is not solved by the structural reduction alone.

### Public replay and review limits

The [verification record](VERIFICATION.md) separates the complete written proofs from the finite exact replay tools, records what each checker establishes, and identifies remaining open cases. No result is called externally peer reviewed, globally priority-certified, or Lean-formalized merely because its exact arithmetic checker passed.
