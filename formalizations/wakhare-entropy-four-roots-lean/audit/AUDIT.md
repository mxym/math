# Formal proof audit — four roots of Wakhare's original entropy polynomial

## Mathematical scope

This is a **full proof for the concrete published counterexample `(11,10)`** to Wakhare's Conjecture 2, not a result about arbitrary `k,r`, all possible entropy inequalities, or Frankl's union-closed sets problem. The actual binomial-sum definition of `h_{11,s}` is formalized, and α is the **unique positive algebraic solution** `α^10(1+α)=1`, equivalent on positive reals to the original fractional exponent definition for `s=11/10`.

The main theorem constructs **four different** interior roots, with strict increasing order. Neither root multiplicities nor an upper bound of four total roots is asserted. The direct polynomial object is `EntropyRoot.witnessPolynomial : ℝ[X]`.

## Proof chain

- `EntropyWakhare.Core`: original sums, rational functions and real-independent inner binomial coefficients.
- `EntropyWakhare.Signs`: exact positive multipliers and exact five strict ratio inequalities at `1/5`, `2/5`, `3/5`, `2/3`, `4/5`. All computed using integers and rationals by `norm_num` without `native_decide`.
- `EntropyWakhare.Alpha`: IVT existence, strict rational enclosure and strict-monotonicity uniqueness of the positive parameter.
- `EntropyWakhare.FourRoots`: original real-evaluation reconstruction, continuity, five alternating signs and four independent IVT root witnesses on disjoint intervals.
- `EntropyWakhare.Polynomial`: actual Mathlib `Polynomial ℝ`, agreement of its evaluation with the original formula, and the principal ordered-root theorem.

No fixed polynomial coefficient lists are trusted without derivation; the binomial combinatorics are inside the exact Lean definitions. No numerical root solver participates.

## Kernel, library and local replay

- **Lean**: v4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`.
- **Mathlib**: v4.34.1, exact Git SHA `d13f23b723b8a846827a245b89c10fc7d3f11612` (manifest also pins all its dependencies).
- Main proof should use only standard axioms `propext`, `Classical.choice`, `Quot.sound`. `scripts/check_axioms.py` fails on any additional axiom or missing root declaration.
- `audit/InvalidProof.lean` contains an **intentionally incorrect proof of `False` from `True.intro`**; the Lean kernel must reject it with a proof-type error. This failure is a successful *negative* test, not a source of assertions in the theorem.
- A positive kernel compile with `lake build EntropyWakhare` and ordinary/optimized source integrity checks are distinguished from syntax-only validation; CI must actually finish for remote success to be reported.

## Reproduction

```sh
lake exe cache get
bash scripts/replay.sh
sha256sum -c SHA256SUMS
```

The first command is required only when the pinned Mathlib dependencies/caches are not yet available. No binaries, private toolchains or local absolute machine paths are committed. The package source and main formalized theorem do not import the earlier unverified JSON certificates as proof assumptions.

## Publication and attribution

This theorem formalizes the previously released [complete mathematical proof and exact arithmetic witnesses](../../../notes/entropy-polynomial-counterexample/COUNTEREXAMPLE_PROOF.md). No modification to the historical proof or authorship of the earlier result is implied. The original conjecture is from Wakhare's *Iterated Entropy Derivatives and Binary Entropy Inequalities*, Journal of Approximation Theory 307 (2025), 106143. This is AI-assisted mathematical formalization, not a priority determination or outside peer-review opinion.
