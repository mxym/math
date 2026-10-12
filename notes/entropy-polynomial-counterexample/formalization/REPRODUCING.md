# Reproducing the audited Lean sources

The mathematical sources are the five unchanged files in `source/`: Alpha, Definitions, Signs, FourRoots and Counterexample. The independent audit freshly compiled those five modules and replayed the closure of all 79 owned declarations into an empty official Lean kernel at trust level zero. Its 16,089-declaration replay passed with no skipped owned declarations; the deliberate ill-typed-proof control was rejected. The 37 named theorem dependencies are standard Lean axioms only.

## Pinned environment

- Lean 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`.
- Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- Other package revisions are in [DEPENDENCY_MANIFEST.json](DEPENDENCY_MANIFEST.json).

The audit used already provisioned upstream compiled dependencies. It did not build all of Lean/mathlib from source, and those caches are not bundled. Before the commands below, provision the pinned Lean distribution and matching dependency checkouts/builds. Merely having a different recent Mathlib version is insufficient. The publisher checked the listed nine dependency repository HEADs and clean source status; that check is not a fresh dependency build or an independent cache-object proof.

The archived author's `source/run_lean.sh` and `source/verify.sh` preserve the original environment-specific sibling-directory convention. They are historical launchers and are not a portable entrypoint in a fresh clone. Use explicit locations below instead. The instructions mirror the audited compile and check commands; this packaging step did not rerun a new large build/replay using this relocated public layout.

## Explicit source compilation and audit commands

From this formalization directory, replace the two example paths with your actual pinned installations. The dependency directory must contain the package directories listed in the loop, with their matching compiled `.lake/build/lib/lean` artifacts.

```sh
ENTROPY_LEAN_BIN=/path/to/pinned-lean-4.34.1/bin/lean
ENTROPY_DEP_PACKAGES=/path/to/pinned-dependency-project/.lake/packages
"$ENTROPY_LEAN_BIN" --version
git -C "$ENTROPY_DEP_PACKAGES/mathlib" rev-parse HEAD
ENTROPY_BUILD=$(mktemp -d)
export LEAN_PATH="$ENTROPY_BUILD"
for pkg in LeanSearchClient aesop batteries proofwidgets importGraph mathlib plausible Qq; do
  LEAN_PATH="$LEAN_PATH:$ENTROPY_DEP_PACKAGES/$pkg/.lake/build/lib/lean"
done
export LEAN_PATH
cd source
for mod in Alpha Definitions Signs FourRoots Counterexample; do
  "$ENTROPY_LEAN_BIN" -o "$ENTROPY_BUILD/$mod.olean" "$mod.lean" || exit 1
done
cd ../independent/checks
"$ENTROPY_LEAN_BIN" TheoremSignatures.lean
"$ENTROPY_LEAN_BIN" KernelNegativeControl.lean
"$ENTROPY_LEAN_BIN" ReplayAllOwned.lean
cd ../../realpower-bridge/source
"$ENTROPY_LEAN_BIN" -o "$ENTROPY_BUILD/RealPowerBridge.olean" RealPowerBridge.lean
cd ../independent/checks
"$ENTROPY_LEAN_BIN" BridgeSignatures.lean
"$ENTROPY_LEAN_BIN" ReplayAllBridgeOwned.lean
```

The first directory on LEAN_PATH is newly empty for each run; none of the original author-owned or old independent owned objects is included. The three checks respectively print theorem signatures/axioms, reject a deliberately invalid proof, and run `Lean.Kernel.Environment.replay` from `mkEmptyEnvironment 0`. A successful import or compilation alone is not the empty-kernel replay.

The standard axioms `propext`, `Classical.choice`, and `Quot.sound` remain axioms. The same official Lean kernel implementation is reused; this is not an independently implemented checker. The paper-to-formal-definition comparison is a semantic audit. The original five-module result uses the integer-power parameter equation (6.1). The separate realpower-bridge source proves equivalence to the original real-power definition (1.1) for (11,10), and proves the original-real-power conjecture-negation theorem without outer hypotheses. Its independent additive audit freshly compiled the bridge using the previously independently fresh core artifacts, then replayed all six new roots and their complete 18,783-declaration closure at trust level zero in 82.780 seconds. The above public recipe rebuilds all six modules in one newly empty output directory; the publication writer has not rerun that relocated recipe. The 16,089 and 18,783 closures overlap and are not added together.
