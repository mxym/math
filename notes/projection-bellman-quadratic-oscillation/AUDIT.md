# Dependency, proof and reproducibility audit

**Date:** 8 October 2026. **Type:** model-assisted author self-review; not external human peer review, world-first novelty determination or full proof-assistant formalization.

## Inherited mathematics

The cone invariant `a(K)` and the exact projection-body product/join state identities for `(D,H,Q)` are in `preprints/005-simplex-product-optimum/v2/paper.md` (Git blob `5d5b909b5b6532910af80e17ba5abf74c0ae4c02`). The binary simplex-seeded recursion and its convergent spectral rate are in `preprints/005-simplex-product-optimum/v5/paper.md` and the v2 spectral supplement. The earlier [Bellman profile method-obstruction paper](../projection-bellman-power-obstruction/paper.md) already proved exact interpolation at every binary orbit state (under the specified sharp, separately product/join inductive assumptions); the new manuscript re-proves it in Section 3 for self-containment.

We do **not** assume that the binary orbit attains the true unrestricted product/join spectral supremum. Every new theorem is conditional on the existence of an individually **sharp** Bellman potential with coefficient exactly equal to the binary orbit rate and closure on *all actually constructible* states. The goal is to constrain that architecture, not falsify an open global-optimality conjecture.

## New all-dimensional obstruction and its exact inputs

1. The original orbit forces exact interpolation from the slack amplification inequality `E_(j+1)>=4 E_j`, together with continuity at `H/D=0` and the known binary rate limit. The proof computes `lim psi(t_j)/t_j²=alpha_*` using a backward geometric sum of the exact binary step multipliers.
2. Joining `2^(j-1)` points to the `j`th actual binary body produces dimension `r_j=(16·4^j−1)/3+2^(j-1)` and `H_j'=13·2^(j-1)`, so `(H_j')²/r_j ->507/64`. The self-product closure inequality has a *strictly negative* quadratic-approximation limit `(25/144)*L−log(13/12)<-1/200`, proved using only `L<54/125` and `log(13/12)>2/25`.
3. Consequently any candidate's normalized quadratic residual has a zero subsequential limit on the original orbit but a `limsup` **strictly above `1/4000`** on the union of input/output arguments from the perturbed family. Thus no quadratic germ, and in particular no twice-differentiable germ, is permitted, irrespective of convexity. This is an **infinite-index analytic theorem**, not a numerical finite-sample observation.
4. The independent [`code/check.py`](code/check.py) **rederives the coarse orbit rate bound** using two-sided Robbins factorial inequalities, an exact finite atanh log series, Machin's rational arctangent pi bracket, and a proved closed remainder for the entire binary orbit. It verifies every rational constant and the oscillation margin. It does not call the older checker or use a numerical optimizer.

## Canonical nonanalytic candidate rejection

The new paper separately constructs a natural real-Gamma continuation of the exact binary orbit that satisfies all orbit interpolation conditions but fails product closure on a concrete attainable **dimension-eight** body `A=(T1×T2)*point^(*5)`, with `H=53/7`. The exact negative slack is **below `−1/20000`**, proving the canonical profile itself is not a valid sharp Bellman inductive envelope. This does not imply that **every** nonanalytic profile fails.

Two implementations agree:

- [`code/check_canonical_rational.py`](code/check_canonical_rational.py) uses only standard-library `Fraction` and outward-rounded dyadic rational intervals at 136 bits, exact rational atanh logarithm enclosures, Binet–Stirling with four Bernoulli correction terms and a signed next-term remainder, and closed geometric Gamma-ratio bounds for **every omitted index** of the infinite series. The complete analytic justifications for these bounds are in Section 7 of `paper.md`.
- [`code/check_canonical_arb.py`](code/check_canonical_arb.py) provides independent 192-bit SageMath/Arb real-ball computations using `log_gamma` instead of the rational Stirling expansion, with an independently derived closed Gamma-ratio tail. This is supplemental corroboration, not a required network service or proof dependency.

Both obtain the identical rational inequality `slack < −1/20000`. The published CI runs **only** the standalone standard-library rational checker, together with the no-quadratic-germ checker; the SageMath replay is optional. It is false to describe either a numerical optimizer or a finite list of samples as the proof of the infinite-index theorem.

## Corruption controls and exact scope

`code/negative_controls.py` deliberately corrupts the pi bracket, the binary spectral bound, a necessary natural-log enclosure, the exact binomial multiplier, and the infinite-series truncation count; each must trigger an explicit `RuntimeError`, even with `python3 -O`. All published package files, including replay logs, are SHA-256 pinned. The ordinary/optimized reports of both pure-rational checkers are byte-identical.

Neither theorem solves the full point-generated spectral maximization, supplies an exact full Bellman supersolution, or establishes geometric uniqueness. It **does** rule out any continuous-at-zero exactly sharp scalar homogeneous profile whose product/join closure is proved separately and which is twice differentiable at the origin, while specifying the minimal required second-order oscillation for any remaining candidate. Proofs that retain actual `Q`-dependent slack, depend on dimension, or use additional reachability parameters are outside the obstruction.
