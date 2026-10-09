# All-graph Laplacian strong Chollet — complete Lean proof

`Chollet.strongChollet_all_graphs` in [CholletAllGraphs.lean](src/CholletAllGraphs.lean) proves the exact shared `Chollet.StrongChollet` target for **every finite simple unweighted graph and every principal vertex subset**. It uses the actual mathlib graph Laplacian and `Matrix.permanent`, and the diagonal product contains degrees in the original graph. Empty principal subsets, isolated vertices, disconnected graphs, and singular Laplacians are included. There are no connectivity or minimum-degree assumptions in the main theorem.

For a principal matrix `L[S]`, the conclusion is

```text
per(L[S] ∘ L[S]) ≤ per(L[S]) · ∏_{v∈S} degree_G(v).
```

The stronger theorem `laplacianDiagonalStrong_all` proves the whole-matrix strong inequality for the Laplacian plus any nonnegative real diagonal addition. This supplies all original-degree principal cases through a proved degree correction.

## Independent verification

The 83 source modules are frozen in `case.json` with SHA-256 hashes and a complete import order. Lean is pinned to 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`; mathlib is pinned to `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Final independent verification completed on 2026-10-09: **MECHANICAL_PASS**. All 83 modules compiled fresh into a new isolated build directory. All **985 owned declarations** and their **44,173-declaration transitive closure** replayed successfully from an empty kernel at **trust level 0**. The full main theorem itself has 42,988 declarations in its dependency closure. The deliberately invalid proof was rejected, and the shared dependency-cache fingerprint was unchanged. See `verification/final-review.json`, `replay-summary.json`, `status.json`, and `negative-kernel.log`.

The audit includes every declaration owned by every bundled source module, including copied upstream matching and matrix proofs. It checks theorem dependencies and the pinned signatures of `propext`, `Classical.choice`, and `Quot.sound`. No additional mathematical axiom, omitted proof, unsafe or partial declaration, or `native_decide` is permitted. An invalid-proof control is required to fail in the empty trust-zero kernel. The source-token scan is supplementary; the kernel/dependency check is authoritative.

The first full audit rejected a compiler-generated partial runtime helper for the recursive walk weight. The definition was made explicitly noncomputable, its generated declarations were checked, and the full fresh audit was restarted on the changed bytes. `verification/previous-attempt-fix.json` preserves the failed attempt and exact source change.

The final record concerns these exact 83 modules. Earlier partial checkpoints have separate scopes and are not used as evidence for rebuilt or later source bytes. This directory retains the historical `all-graphs-progress` name so existing coordination links remain usable.

## Proof and source review

[SEMANTIC_REVIEW.md](SEMANTIC_REVIEW.md) gives the complete mathematical chain and checks the endpoint against the target definition. The degree-two block argument uses a vanishing third trace and uniformly scaled matching weights. General graph assembly uses vertex-count induction strengthened by arbitrary nonnegative diagonal additions. These arguments avoid cycle enumeration and a full block-tree formalization.

The theorem concerns simple unweighted graphs over the real Laplacian. It makes no claim about arbitrary PSD matrices or arbitrary weighted graphs. The source review is an internal independent rederivation, not an external human peer-review certificate. [THIRD_PARTY.md](THIRD_PARTY.md) records copied proofs, exact commits, import adaptations, licenses, and source hashes.

## Reproduction

For a normal candidate build, use `lake build` with the pinned `lean-toolchain` and `lakefile.lean`. For independent fresh compilation and empty-kernel replay using already-installed official dependencies:

```sh
python3 reproduce.py --output /path/to/new-verifier-output \
  --toolchain /path/to/lean4.34.1 \
  --packages-root /path/to/pinned-packages \
  --cache-root /path/to/existing-mathlib-cache > replay.log 2>&1
```

The output directory must be new. The verifier checks toolchain/package commits, every source hash, all owned declarations and their transitive dependencies, empty-kernel replay, invalid-proof rejection, and an unchanged shared dependency-cache fingerprint. It installs nothing and uses no old owned `.olean` files. `verification/` contains the final logs, inventory, closure, axiom signatures, and replay summary.
