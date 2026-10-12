# Sharp simplex stability: the original upper Main

The literal theorem `Entry005.sharpMain : Entry005.sharpMainGoal` is proved, also inhabiting the unchanged original alias `Entry005.MainTarget`. For every `d ≥ 3`, every qualifying actual compact convex body K, and every prescribed maximum-volume inscribed simplex S, it bounds the actual excess about S's own centroid by the original `gSharp d` times the actual defect to power `1/(d−1)`. No geometric bridge remains as an input premise.

## Exact scope and source composition

This project packages the independently audited **204-file composition**: the original 203-file patch (SHA256 `9a0a33f57cc6a3f9f373040ae11fd98ade985bbd5712f31fca3b82f702b7a932`) plus the exact missing `SelectedAnchorHullRoundness.lean` supplied by patch SHA256 `01dab955ed966f094eedb30de00a392af6615f8960114a8099187f7061a7a71e`. The original 203-file patch was incomplete as delivered; cached objects were not accepted as a substitute for that missing source.

The composition contains **123 owned mathematical modules, 848 public proofs, and 1,833 actual module-owned declarations**. All 123 mathematical source files are byte-for-byte unchanged. The independent audit freshly compiled every one, checked the complete 4,743-module source closure, and replayed both the literal Main (54,277 declarations) and all owned declarations (55,067 declarations) into genuinely empty kernels at trust level zero, with no skipped declaration. See [the technical report](audit/independent/TECHNICAL_REPORT.md), [the compact certificate](audit/independent/FINAL_PASS.json), and [verification instructions](VERIFICATION.md).

The two core stability objectives have been independently audited in separate source projects. This directory proves the **upper Main**. The sibling [simplex-truncation-sharpness](../simplex-truncation-sharpness/README.md), when distributed alongside it, proves the matching actual truncation-sharpness goal in 125 modules. Its older inherited checkpoint comments that Main was open describe that earlier source scope, not the current research result. Both projects retain identical original `Targets.lean` definitions, but they are intentionally not code-merged. The lower proof is not included or counted in this upper project. A sibling link does not assert that the sibling has been publicly published.

## Read and reproduce

- [Exact theorem and unchanged constants](THEOREM.md)
- [Complete mathematical route and source map](PROOF_ROADMAP.md)
- [Original written radial proof](project/proofs/CompleteSharpMainRadialProof.txt), preserved byte-for-byte
- [Independent traditional mathematical review](audit/mathematical/REVIEW.md), including the genuine polar construction and a brightness-without-scale counterexample
- [Input identity and public derivative lineage](PROVENANCE.md)
- [Existing licenses and attribution](LICENSE_NOTICE.md)

Start with `python3 -B scripts/verify_integrity.py`. The recommended proof command is `python3 -B scripts/verify.py --lean-bin /path/to/lean/bin --dependency-project /path/to/dependency-project --output /path/to/fresh-output`; optional `--extra-cache /path/to/external/lib/lean` locations are strictly read-only and never provide old owned objects. The verifier always recompiles **all 123 owned modules** before both kernel replays. It does not default to the former 20-module incremental test.

The old author README, evidence, manifests and incremental script are historical records. Their 122/845 counts, 131-additive-proof count and pending-audit wording are superseded; the composed additive count is 134 above the 714-proof foundation. Historical `Targets.lean` comments are retained to preserve mathematical byte identity. The current package manifest is `SOURCE_MANIFEST.json`, not any historical author manifest. `project/scripts/replay_upper_main.py` now forwards to the complete verifier; its former implementation is retained only under `audit/historical/`.

This is a source-only, locally prepared release candidate. It contains no owned objects or dependency cache. Local verification is not a claim of public publication, a new license, or human referee endorsement.
