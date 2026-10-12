# Actual truncation sharpness for entry005

The principal theorem is
`Entry005.truncationSharpness : Entry005.truncationSharpnessGoal`.
It proves the original published target using the actual geometric defect,
a genuine globally maximum inscribed simplex, its own original centroid,
and the original obstruction exponent `1/(d-1)`.
`formal/Entry005/Targets.lean` is byte-identical to the inspected public source.
The final theorem has no assumed geometric formula or maximum-simplex premise.

For `K_t = {x_i >= 0, t <= sum x_i <= 1}`, the source proves the actual
volume, every intrinsic facet area, actual projection body and directional
projection volumes, all ordered facet determinant sums, and the exact actual
entryDefect expression. It proves the chosen `S_t = conv(e_i, t e_j)` is
maximum among all inscribed simplices and its literal own-centroid excess is
`(d+1)t`. Positivity and the exact `t^(d-1)` asymptotic then close sharpness.

## Reproduce

The pinned compiler is Lean 4.34.1, commit
`5045d0056413266e57c625dcd7c365b10e377c52`; Lake 5.0.0-src. Mathlib is exactly
`d13f23b723b8a846827a245b89c10fc7d3f11612`. All nine package revisions and
source URLs are locked in `formal/lake-manifest.json`.

On Linux x86_64 with curl, tar/zstd, git, Python 3.11+ and ripgrep:

```bash
./scripts/bootstrap.sh
```

The bootstrap installs the official pinned Lean release locally, verifies
its archive SHA-256, uses the official maintained mathlib cache and all locked
dependencies, then runs the complete clean source verification. It preserves
inherited proxy/TLS settings and never runs `lake update`.

With the pinned toolchain already available:

```bash
ENTRY005_LEAN_BIN=/absolute/lean/bin ./scripts/bootstrap.sh
```

Or with the exact dependencies already provisioned:

```bash
python3 scripts/verify_truncation.py --lean-bin /absolute/lean/bin
```

`ENTRY005_MATHLIB_OVERLAY` can designate an independently verified official
mathlib cache `lib/lean` directory. Every delivered mathematical source is
compiled into a fresh owned directory
`formal/.lake/truncation-proof-check/lib/lean`. No prebuilt owned `.olean`
is bundled. The mathematical import target is
`Entry005.TruncationFormalization`; this small project avoids the unrelated
external packages required by the complete OpenAI/math library.

## Coverage, evidence and trust

The project cleanly compiles 125 mathematical modules: 102 unchanged inherited
modules plus 23 new modules. It audits 850 distinct public proof names: the
unchanged inherited 714 plus 136 new exports. Eight new exports reuse exact
OpenAI/math simplex-volume proof bodies; the other 128 are new public proof
bodies in this increment. These counts include supporting lemmas, not 850 new
research results.

`coverage.json` maps every new exported theorem to the inspected paper
statement or supporting mechanism, literal compiled type, complete assumptions,
source line, imported dependencies and actual transitive axioms.
`logs/truncation-clean-build.log`, `logs/truncation-all-statements-axioms.log`
and `logs/truncation-owned-closure.log` are the authoritative clean compilation,
explicit `#print axioms` and private/generated declaration audits.
`logs/truncation-verification.json` records the validated counts and claims.

Only `propext`, `Classical.choice` and `Quot.sound`, or subsets thereof, are
allowed. These mean propositional extensionality, classical choice and quotient
soundness. There is no sorry, admit, custom geometry axiom, native_decide or
unchecked trusted-evaluation shortcut in the delivered mathematical sources.
The transitive audit includes imported mathlib facts and reused OpenAI/math
and owner proofs. Mathlib uses its official pinned compiled cache; this is
not a fresh rebuild of the entire mathlib repository.

The complete prescribed stability upper-bound Main and its explicit constants
remain outside this increment. So do classification of all maximizing S_p,
arbitrary-p own-centroid formula, best-maximum infimum, Banach-Mazur estimates,
and the Rogers-Shephard obstruction proposition. Conditional scalar and
assembly helpers remain explicitly labeled, and their equality premises are
actually discharged in the final sharpness theorem.

`inherited-pyramid-checkpoint/` preserves the older frozen report and coverage.
Its historical scope exclusions describe that checkpoint, not this final
sharpness release. The old Library bundle was not modified.

No push, merge or public publication occurred. This is a private source delivery
for independent parent review and merge.
