# Independent additive audit: original real-power parameter

Date: 2026-10-08 UTC.

This additive audit covers the frozen `RealPowerBridge.lean`, SHA-256 `9a51cdd8d6cb3d87fbe97cf6121198ea891b115cd0a07ad29379ed2df7607249`. The five original mathematical source files are unchanged and match the earlier independent audit's source hashes. This report supersedes only the earlier limitation that equivalence with the original real-power equation had not been formalized.

## Verdict

PASS: fresh bridge compilation and all six theorem/owned-declaration axiom audits passed with zero warnings and only the standard three axioms. The complete 18,783-declaration closure of all six bridge roots passed genuine empty-kernel replay at trust level zero in 82.780 seconds, with no skipped roots. The actual original-real-power final theorem was explicitly required among those roots.

## Source correspondence

[Wakhare, arXiv:2312.14743v2](https://arxiv.org/html/2312.14743v2), equation (1.1), defines the parameter at exponent `k/r` by `a = 1 / (1+a)^(k/r-1)`. The new source writes this with `Real.rpow` and explicitly real exponents, including real division. It does not use natural-number division or natural-number exponentiation for that defining exponent.

For the pair `(11,10)`, the bridge proves the equivalence on the positive real domain between that equation and `a^10 * (1+a) = 1`. The forward proof takes a positive real tenth root using proved `Real.mul_rpow` and power/root cancellation identities. The reverse proof raises the equivalent product equality to the natural tenth power. Positivity ensures the real-power denominator is nonzero and the cancellation hypotheses are valid.

The constructed parameter satisfies the original real-power equation and is its unique solution in `(0,1)`. The existing interior-root lower bound therefore applies to every parameter specified by that original equation. The final existential counterexample and universal negation both use the paper's original real-power expression directly.

## Exact final theorem

```lean
EntropyCounterexample.wakhare_conjecture_two_false_original_real_power :
  ¬ (∀ k r : ℕ, 0 < r → r < k → Nat.Coprime k r →
      ∀ a : ℝ, a ∈ Set.Ioo 0 1 →
        a = 1 / Real.rpow (1+a) ((k : ℝ)/r-1) →
        unitRootCount (pPolynomial k r a) = 2)
```

There are no outer hypotheses. The polynomial and multiplicity-count definitions are precisely the original ones independently audited in the five-module core. The original source-to-paper finite-sum audit, four-distinct-root argument, and scope restrictions remain unchanged.

## Additive verification method

`run_bridge_audit.sh` creates an empty new bridge build directory and compiles only the new frozen source into it. Its imports use the earlier independent audit's fresh owned output for the unchanged five modules, plus the disclosed read-only official dependency cache. It never imports the author's `RealPowerBridge.olean` or any author's owned build directory.

All six new explicit theorem signatures and axiom sets are printed. The auditor enumerates every declaration belonging to the bridge module, rejects unsafe/partial declarations and nonstandard axiom dependencies, and computes their complete transitive dependency closure. It explicitly requires `wakhare_conjecture_two_false_original_real_power` to be among the replay roots. The replay starts with `mkEmptyEnvironment 0` and checks that every replayed root has the original type and universe parameters. Thus the new real-power theorem, not merely the previously audited integer-power theorem, is included in a genuine trust-zero empty-kernel replay.

The existing deliberate-invalid-proof negative control and the unchanged five-module audit are reused, not rerun. Their report and hashes are bound in `VERIFICATION.json`. This is an additive independent audit in the shared environment, not an independently implemented kernel or a full rebuild of all mathlib.

## Evidence and scope

`VERIFICATION.json` records the completed result, replay counts and time, full six-file source hashes, reused core artifact hashes, and prior-gate identity. `theorems.txt` lists the six new explicit theorems. `all-bridge-owned-axioms.json` includes generated declarations. The `logs/` directory records the fresh compile, checked signatures, and actual empty-kernel replay. `SHA256SUMS` binds the audit files.

The result is a counterexample to Conjecture 2, with at least four distinct interior roots and a multiplicity count at least four. It does not assert exactly four roots, a smallest example, novelty, failure of the entropy inequality, or a solution to the union-closed sets conjecture. No author sources, git state, or public artifacts were changed by this audit.
