# Verification and trust boundaries: universal finite \((n,k)\) exact-maximal-minor theorem

**Date:** 2026-10-08. Primary source: [complete proof](paper.md). **Status:** traditional mathematical proof draft + multiple independent exact computational replays; full Lean formalization and external human peer review remain pending.

## 1. Mathematical proof decomposition

The all-\((n,k)\) theorem is not inferred from a finite sample. The complete argument has four separate general components:

1. **All-parameter cycle-index integers.** The already published two-state transfer-matrix theorem gives exact counts \(F_h(c)\), in integer arithmetic, for every short-cycle vector \(c\). No optimization is used.
2. **Full-rank binomial-product determinant.** For every \(n\ge2m\), the proof exhibits a specific \((m+1)\times(m+1)\) orbital matrix with determinant
   \[
   (-1)^m\prod_{r=0}^{m-1}\binom{n-2r}{m-r}.
   \]
   The derivation uses finite differences of the long-cycle orbital polynomial and its Taylor coefficients at \(t=1\); it is a symbolic proof for all \(n,m\).
3. **General \(\ell^1\) circuit extremality.** A full-row-rank matrix with first row ones has a signed kernel norm optimum at a minimal-support circuit. Every such circuit can be extended to \(r+1\) columns, and the unique kernel vector is proportional to the alternating maximal-minor vector. This is a finite-dimensional convexity and linear-algebra proof, not an invocation of untrusted LP output.
4. **Exact group-action attainment.** Conjugation averaging and orbital aggregation reduce all admissible perturbations to the integer matrix kernel without losing the identity atom. Conversely, any rational maximal-minor kernel vector yields nonnegative central class-mixture probability laws with equal marginals and, at sufficiently small rational amplitude, a genuinely admissible attaining perturbation.

The exceptional \(n=1\) and \(m=0\) cases and subset complementation are explicitly covered. Theorem E extends the same finite determinant formula to arbitrary finite permutation group actions without requiring transitivity or faithfulness.

## 2. Independent public-source integer replay

The files [code/check_universal_max_minors.py](../code/check_universal_max_minors.py) and its exact input recurrence [code/check_all_k_orbital_compression.py](../code/check_all_k_orbital_compression.py) were **fetched afresh from public GitHub main**, then replayed together in the isolated VPS folder:

    /srv/mcp-workspace/permanent-continuation-20261007/universal-maxminor-replay/

The algorithm enumerates the **complete finite set** of maximal-minor candidates, uses integer Bareiss determinants, verifies the kernel equation for every nonzero cofactor vector, and compares only exact Fraction quotients. There are no floating-point operations, numerical LP, heuristics, truncation or solver calls.

Results: the binomial-product rank formula passed for ranks \(m=1,\ldots,9\) at multiple degrees; the exact formula reproduced all fixed regression values in ranks 1–4. In particular, \((n,k)=(9,4)\) evaluated **118,755** candidate matrices and returned \(5/14\). The replay exited successfully and printed:

    UNIFIED DETERMINANT FORMULA FINITE REPLAY PASSED

These tests are **crosschecks** of the general proof, not a finite-parameter substitute.

The separate [code/check_generic_circuit_audit.py](../code/check_generic_circuit_audit.py) compares the maximal-minor implementation against an independent exact SymPy nullspace circuit enumerator. **214 deterministically generated full-row-rank integer matrices** passed, including rank degeneracies and duplicate-column circuits. This is still a finite audit, not a formal proof of the general circuit lemma.

## 3. Sharpness of the sparse support theorem

At \((n,k)=(11,4)\), the complete public [rank-four finite certificates](../certificates/four_subset_n8_64.json) give an optimal dual with **exactly six** tight short-cycle types: three upper contacts and three lower contacts. The \(5\times6\) contact matrix has rank five and all six alternating maximal minors are nonzero, so every optimal signed marginal-preserving perturbation requires all six types. This proves the \(m+2\) bound cannot be reduced to \(m+1\) globally.

The independent [code/check_sparse_support_sharpness.py](../code/check_sparse_support_sharpness.py) was fetched from public main with the fixed JSON and replayed successfully in the same isolated VPS folder:

    SHARP m+2 SUPPORT BOUND CERTIFIED

## 4. GitHub-hosted CI

The [read-only orbital certificate workflow](https://github.com/mxym/math/blob/main/.github/workflows/permutation-orbital-certificates.yml) now includes the entire universal-max-minor fixed regression suite, the sparse-support sharpness checker, and the independent SymPy circuit audit. A [successful GitHub Actions run](https://github.com/mxym/math/actions/runs/37732496636) independently replayed the updated checkers on a GitHub-hosted runner, not the VPS or Windows discovery machine. Exact step results remain publicly inspectable at that URL.

CI success attests that the exact published **programs and frozen finite inputs** run as claimed; it is **not** a Lean proof of the universal mathematical theorem.

## 5. Lean formalization status

A [generic Lean theorem](../formal/KernelMass.lean) proves that the kernel of a rational constraint matrix with a first row of ones consists of signed vectors of total mass zero. Its public source was fetched from GitHub, compiled under Lean 4.34.1 with the available Mathlib basic matrix library on the authorized Windows machine, and returned:

    PUBLIC LEAN KERNEL-MASS FRAGMENT COMPILED SUCCESSFULLY

This is a **real kernel-checked, sorry-free lemma**, but covers only a small component of the proof. The [Lean roadmap](LEAN_ROADMAP.md) lists the unformalized cycle-index theorem, rank determinant, general circuit lemma, group-action reduction and final finite-maximum equality. The full all-\((n,k)\) theorem is therefore **not formally certified in Lean**.

## 6. Scope, novelty, and unfinished stronger questions

The main result supplies a **uniform finite exact rational expression** for every parameter pair, with explicit deterministic instructions and bounded support. It is not an elementary piecewise-rational formula without a finite maximum. Selecting the maximizing circuit types at all parameter pairs remains an additional structural classification problem. The formula is polynomial in \(n\) for fixed \(m=\min(k,n-k)\), but may be infeasible for large growing \(m\).

Classical inputs include determinant expansions, signed circuits of vector configurations, basic convexity, and conjugation averaging. Prior project results supply the orbital LP and exact cycle-index recurrence. A comprehensive literature novelty search and independent human referee evaluation remain **incomplete**. Do not claim a world-first theorem, external refereeing, or Lean formal completion.
