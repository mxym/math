# All-graph Laplacian strong Chollet — partial Lean progress

The complete theorem for every finite simple unweighted graph and every principal index set is **not yet proved in Lean**. The exact target is `Chollet.StrongChollet` in `src/Target.lean`, using the actual Mathlib Laplacian and permanent, and degrees from the original graph. Empty and singular cases are retained.

This checkpoint contains 59 modules. They were compiled fresh into a new build directory with Lean 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`, and mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. All 769 owned declarations and their 43,704-declaration transitive closure passed replay from an empty kernel at trust level 0. Dependencies use only `propext`, `Classical.choice`, and `Quot.sound`, whose pinned signatures were checked. No owned declaration is an axiom, unsafe or partial; no `sorry`, `admit`, or `native_decide` is used. The deliberately invalid proof was rejected by the empty kernel.

The original driver lost its stdout pipe after successful replay when the execution environment reconnected. `verification/status.json` preserves that failure. `verification/TAIL_COMPLETION.json` records the subsequent negative-control test and source/environment rechecks. An unchanged shared-cache fingerprint is not claimed for that interrupted driver run. The earlier 54-module run completed normally and is retained locally; its record is not used as proof of the later source bytes.

## Proved scope

- Ordinary matching polytope and weighted matching selection, derived from the imported perfect-matching theorem by a doubled graph construction.
- Actual real PSD permanent nonnegativity, singleton/pair lower bounds, matching lower bounds, and diagonal-product lower bound, including singular matrices. The block sizes needed here are proved directly; no general Lieb theorem is assumed.
- Actual permutation cycle expansion and the simple-cycle product upper bound.
- Row-sum contraction, `tr(C^(n+2)) <= r^n tr(C^2)`, and the exact finite `19/24` trace-series coefficient.
- All odd-set constraints for actual vertex-robust minimum-degree-two graphs with a vertex of degree at least three. Additional theorems cover every even-order or order-at-least-ten vertex-robust graph. Vertex robustness is stated as connectivity of every literal vertex-deleted induced graph, rather than a hidden combinatorial assumption.
- Injection-based restriction of ordinary fractional matchings, and the required normalized logarithmic permanent lower bound for **every actual principal submatrix** of a noncycle block. Both oriented edges are retained at half weight; the `4/5` coefficient over oriented edges equals `8/5` over unordered edges.
- Exact diagonal scaling and normalization using ambient degrees; PSD pivot assumptions discharged in the diagonal-addition and rooted one-point-sum interfaces.
- Reused public all-bipartite and induced-bipartite cases, and exact matrix permanent coalescence identities.

## Remaining whole-theorem work

1. Inject rooted simple cycles into weighted closed walks and connect the cycle sum to the trace upper bound. The weighted closed-walk trace identity is already compiled in the ongoing local development, but is outside these 59 audited modules.
2. Close the small odd-cycle endpoint, or a uniform all-cycle endpoint.
3. Assemble arbitrary graph splits/blocks and all hereditary principal cases into `StrongChollet`, with isolated vertices and disconnected components.

These gaps are not replaced by axioms or hypotheses disguised as a completed endpoint. Historical assessment propositions in `CholletInterfaces.lean` are definitions, not asserted theorems.

## Reproduction

For a normal candidate build, use `lake build` with the pinned `lean-toolchain` and `lakefile.lean`. For independent fresh compilation and empty-kernel replay using already-installed official dependencies:

```sh
python3 reproduce.py --output /path/to/new-verifier-output \
  --toolchain /path/to/lean4.34.1 \
  --packages-root /path/to/pinned-packages \
  --cache-root /path/to/existing-mathlib-cache > replay.log 2>&1
```

The output directory must be new. The verifier checks toolchain/package commits, source hashes, every owned declaration and its dependencies, the three standard axiom signatures, empty-kernel replay, and invalid-proof rejection. It installs nothing and does not reuse owned build files. Source hashes and import order are in `case.json`; full dependency records are compressed under `verification/`.

See `THIRD_PARTY.md` for copied source attribution, licenses, commits, and hashes. This checkpoint is for coordination and independent checking, not a completed proof announcement.
