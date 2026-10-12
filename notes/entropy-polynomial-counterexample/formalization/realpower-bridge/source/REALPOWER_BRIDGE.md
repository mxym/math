# Additive real-power parameter bridge (v1.1)

This extension leaves the five frozen v1 proof sources and their 37 theorems
unchanged. It adds six kernel-checked theorems in `RealPowerBridge.lean`.

For every positive real `a`, the new bridge proves the exact equivalence

`a^10 * (1+a) = 1` if and only if
`a = 1 / Real.rpow (1+a) ((11 : ℝ)/10-1)`.

The right side is the paper's original parameter definition (1.1) specialized
to `k/r = 11/10`. The real exponent is exactly `1/10`; no numerical real-power
approximation is used. Positivity justifies the real-power cancellation laws.

The added interface also proves existence and uniqueness of this originally
defined parameter in `(0,1)`, a root multiplicity count of at least four for any
parameter satisfying that real-power definition, and the unconditional negation
of the universal two-root assertion with its parameter written in the original
real-power form.

All six names below belong to the `EntropyCounterexample` namespace:

1. `parameter_equation_iff_original_real_power`
2. `alpha_original_real_power`
3. `alpha_existsUnique_original_real_power`
4. `counterexample_original_real_power`
5. `counterexample_to_conjecture_two_original_real_power`
6. `wakhare_conjecture_two_false_original_real_power`

The last theorem is the direct original-definition conjecture-negation interface.
It has no external assumptions. As in v1, the result proves at least four roots,
not exactly four; it concerns Wakhare's Conjecture 2, not Ho's entropy inequality
or Frankl's union-closed sets conjecture.

## Reproducibility

Run `./verify_realpower_bridge.sh`. It checks that all five original source
hashes are unchanged, compiles those five sources plus the additive module into
a new empty output directory, and checks the six additional theorem signatures
and axiom dependencies. No existing v1 artifact is overwritten.

- Frozen source inventory: `REALPOWER_BRIDGE_SOURCE_SHA256.json`
- Machine-readable result: `REALPOWER_BRIDGE_VERIFICATION.json`
- Clean compilation log: `logs/realpower_bridge/cleancompile.log`
- Full signatures and axioms: `logs/realpower_bridge/signatures-and-axioms.log`
- Toolchain pins: `logs/realpower_bridge/pins.log`

The new source has no `sorry`, custom axioms, `native_decide`, or `unsafe`.
Each new theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`.
The pinned Lean version and mathlib revision are identical to v1.

This additive archive intentionally excludes development logs, scratch files,
and old or temporary compiled artifacts. Its original base proof dependencies
are the separately frozen v1 source files, not a silently replaced release.
