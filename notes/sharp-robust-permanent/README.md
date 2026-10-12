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


## Full exact rank-four triple-action spectrum through degree 23

[Theorem 19](paper.md#19-a-complete-certified-three-subset-spectrum-through-degree-23) determines the **complete exact optimal atom-vs-TV coefficient** for the natural action of S_n on its 3-element subsets, for every 3≤n≤23. For n=3,4,5 the answer follows from trivial action, doubly transitive action, or the two-subset complement, respectively. The 18 genuinely rank-four cases 6≤n≤23 use **fixed rational primal-dual certificates** in [certificates/three_subset_n6_23.json](certificates/three_subset_n6_23.json).

The [independent checker](code/check_three_subset_certificates.py) uses only standard-library integer and Fraction arithmetic, enumerates **every conjugacy class and every three-element subset** for each of the 18 degrees, verifies all orbital moment constraints and every dual inequality, and replays a valid small attaining perturbation. The [separate rational certificate generator](code/generate_three_subset_certificates.py) is not called by the checker. A fresh public GitHub download of the fixed JSON and checker into a new Windows directory passed all 18 degrees; see [replay scope](VERIFICATION.md#independent-fixed-certificate-three-subset-replay).

This is a **finite exact classification with full replayable proof evidence**, not a conjectural all-degree formula for triple actions. This subsection's original fixed certificates stop at n=23; the later Theorem 21 extends exact finite coverage through n=120, and Theorem 22 proves a sharp all-n first-order asymptotic. The exact optimum for individual n≥121 remains open.


## Three-cycle compression, full degree-120 classification, and sharp 18/n asymptotics

[Theorem 20](paper.md#20-an-exact-three-cycle-statistic-compression-theorem) proves that all four orbitals of the natural S_n action on three-element subsets are **explicit integer polynomials** in the counts of fixed points, 2-cycles, and 3-cycles. Every feasible count triple is realized by a canonical permutation, so exact classwise dual verification reduces from partition-number many classes to only O(n³) types.

[Theorem 21](paper.md#21-complete-exact-rank-four-atom-modulus-classification-through-degree-120) extends the exact coefficient classification from n≤23 to **every 3≤n≤120**. The 97 new degrees 24–120 have fully frozen [rational primal-dual certificates](certificates/three_subset_n24_120.json) and an [optimizer-free, standard-library integer checker](code/check_three_subset_compressed_24_120.py). A fresh **public-GitHub-source** replay from an isolated VPS directory verified **1,489,083 distinct compressed cycle states** and all class moment and positivity conditions, with exit status 0. This remains a *finite* theorem, not an all-degree exact formula.

The separate **infinite-parameter** [Theorem 22](paper.md#22-sharp-universal-first-order-asymptotics-for-all-three-subset-actions) establishes

\[
\boxed{C_n^{(3)}=1-\frac{18}{n}+O(n^{-2})\quad(n\to\infty).}
\]

The proof gives an explicit all-degree orbital dual with exact cubic-polynomial expansion, a rigorous global real-variable bound, and **four exact moment-matched rational primal families** indexed by n modulo 4. It includes the explicit (conservative) inequality
\(C_n^{(3)}\le1-18/n+406304/n^2\) for every n≥2048.
The [separate SymPy algebra checker](code/check_three_subset_asymptotic_algebra.py) validates the exact polynomial identities, leading determinant -192m⁹ and matching first-order probability masses for all four residue classes. The symbolic checker was freshly downloaded from public main and ran successfully on the authorized VPS. The all-n proof does **not** rely on extrapolating the degree-120 table.

The [verification and trust-boundary record](VERIFICATION.md) records what is machine checked, what is proved analytically, and what still requires independent human mathematical review. No complete exact all-degree formula, k≥4 asymptotic, external peer review or priority claim is made.


## Uniform higher-rank orbital limits and the Chebyshev mechanism

[Theorem 23](paper.md#23-general-k-subset-orbital-bernstein-limits-and-a-chebyshev-research-direction) proves, for **every fixed subset rank k**, a uniform quantitative approximation of its normalized orbitals by the \(k\)-th Bernstein polynomial basis. This rigorous all-k statement reduces higher-rank asymptotic orbital geometry to a space of degree-k polynomials, with an \(O_k(1/n)\) error valid uniformly over all permutations.

[Proposition 24](paper.md#23-general-k-subset-orbital-bernstein-limits-and-a-chebyshev-research-direction) identifies the already-proved leading dual polynomials at k=1,2,3 as \((1-T_k(2a-1))/2\), where \(T_k\) is the Chebyshev polynomial. Their endpoint derivatives give the *proved* sharp first-order constants 2, 8, and 18. **Historical status correction:** the proposed \(2k^2\) first-order constant for every fixed k≥4 has since been **proved in Theorem 25, Section 24**. The Bernstein approximation alone was insufficient; the completed proof requires the corrected Chebyshev dual and exact positive Chebyshev-node primal measures. Finite-n exact classification remains open.


## All-rank sharp Chebyshev asymptotic and exact transfer-matrix compression

The original **higher-rank conjecture is now rigorously resolved**. [Theorem 25 and its complete analytic proof](paper.md#24-resolution-of-the-fixed-rank-chebyshev-atom-modulus-conjecture) establish for **every fixed k≥1**

\[
C_n^{(k)}=1-\frac{2k^2}{n}+O_k(n^{-2}).
\]

The proof constructs (1) a uniform first-order expansion of all k-subset orbital laws in terms of fixed-point and two-cycle densities, (2) a **Chebyshev dual with a uniquely interpolated first-order correction** that works uniformly over every permutation, and (3) **exact marginal-matched positive central probability measures** from a rational k-by-k linear system at Chebyshev-Lobatto nodes. The first-order primal masses are explicit; their identity mass is \(1-2k^2/n+O_k(n^{-2})\), while their transposition-class mass is \(1-2(k^2-1)/(3n)+O_k(n^{-2})\).

The first previously unproved instance k=4 has [independent exact symbolic and rational-primal replay](code/check_k4_chebyshev_dual.py), including the explicit corrected dual with algebraic coefficient field Q(sqrt(2)), and exact positive probability weights at six large finite degrees. The **general k theorem is analytic** and is not inferred from those checks. No effective universal finite-n optimal constant or threshold is claimed.

Separately, [Theorem 30](paper.md#25-an-exact-cycle-index-and-transfer-matrix-compression-theorem-for-every-rank) proves an **all-n, all-k exact orbital formula** using the 2-by-2 transfer matrix M(u,t)=[[1,u],[1,ut]]. The entire k-subset orbital vector depends only on cycle counts c_1,...,c_k. Thus finite primal-dual certification can enumerate O_k(n^k) short-cycle types rather than all integer partitions. The [independent integer checker](code/check_all_k_orbital_compression.py) compares the transfer-matrix recurrence with direct subset enumeration for every partition of 3≤n≤12 and all 1≤k≤min(n,6).

These close the **leading asymptotic** and the **general exact compression framework**, while the exact optimal coefficient for arbitrary individual finite (n,k) remains a distinct open problem. See [verification scope](VERIFICATION.md).


## Complete fixed-degree four-subset certificate spectrum

[Theorem 31 in the full manuscript](paper.md#26-complete-exact-four-subset-atom-modulus-classification-for-4-le-n-le64) now determines **every exact optimal atom-vs-TV coefficient for S_n acting on its 4-element subsets, for all 4≤n≤64**. Degrees 4–7 reduce by complementation to previously proved trivial, one-, two-, and three-subset results; the remaining **57 degrees 8–64** have frozen [rational primal-dual certificates](certificates/four_subset_n8_64.json).

A completely separate, [optimizer-free Fraction/integer verifier](code/check_four_subset_n8_64.py) enumerates every feasible quadruple of 1-, 2-, 3-, and 4-cycle counts (including a possible residual cycle), validates five marginal-orbital moment equalities, nonnegative disjoint probability measures, dual contact and all class inequalities, and constructs a positive rational attaining perturbation. The checker and fixed certificates were downloaded fresh from public GitHub into an isolated VPS directory and replayed successfully:

    EXACT k4 FRACTIONAL OPTIMALITY CERTIFIED: 57 DEGREES, 440670 TYPES

The general compression proof is Theorem 30; rank-4 moment formulas are written explicitly in Section 26 as an independent combinatorial derivation. This is a **finite complete classification through n=64**, whereas Theorem 25 independently proves the **infinite** sharp leading coefficient \(32\) for all sufficiently large n. No exact all-finite-n formula, external human refereeing, or novelty-priority certification is claimed.


## Universal exact formula at arbitrary finite n and k

The new [dedicated proof](universal-exact/paper.md) establishes an exact rational arithmetic formula for the optimal marginal-preserving atom/TV coefficient **for every finite parameter pair**, not only a sharp asymptotic or finite table. Reduce by complements to \(m=\min(k,n-k)\). Enumerate feasible short-cycle counts and form an integer matrix of normalized mass and the first \(m\) intersection orbitals. The exact coefficient equals a **finite maximum of explicit alternating \((m+1)\)-minor ratios**, with no LP variables or solver dependence.

The proof establishes a universal nonzero rank determinant
\[
(-1)^m\prod_{r=0}^{m-1}\binom{n-2r}{m-r},
\]
shows an optimum always has an attaining signed perturbation on at most \(m+2\) conjugacy classes, and proves this support bound is **sharp** at \(n=11,k=4\). It generalizes the exact minor formula to every finite permutation group action through its conjugacy-class/orbital matrix.

The [pure-integer checker](code/check_universal_max_minors.py) evaluates the full finite maximum with Bareiss determinants and reproduces independently the earlier rank-1 through rank-4 values; the [six-contact exact checker](code/check_sparse_support_sharpness.py) certifies sharpness of the sparse support bound. [Generic exact random-matrix circuit audits](code/check_generic_circuit_audit.py) compare the determinant formula with an independent SymPy rational-nullspace circuit search. These supplement the full analytic proof and are run in GitHub Actions.

The initial [Lean proof fragment](formal/KernelMass.lean) is genuinely compiled but covers only the first-row mass-zero fact. The [Lean roadmap](universal-exact/LEAN_ROADMAP.md) lists the substantial remaining formalization obligations. **A compact elementary formula with no finite maximization is not claimed.**
