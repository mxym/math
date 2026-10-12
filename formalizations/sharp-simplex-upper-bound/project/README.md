HISTORICAL AUTHOR DELIVERY. Its 122/845 counts, incomplete 203-file source claim, incremental 20-module checks, and pending-independent-audit wording are superseded. Read ../../sharp-simplex-upper-bound/README.md and ../audit/independent/TECHNICAL_REPORT.md for this composed 123/848 release. The historical text below is preserved for lineage only.

The sharp upper Main is now proved as `Entry005.sharpMain : sharpMainGoal` and
`Entry005.sharpMain : MainTarget`. The literal original target, constants,
actual `entryDefect`, universal quantifier over every prescribed maximum
simplex, original centroid and exponent `1/(d-1)` are unchanged.

The new route needs no finite Minkowski or first-variation proposition. For
actual supporting approximants Q_m, their actual radial facet cones cover P
after individual support-ratio dilations. This proves
`|P|/|K| <= 1+d*M^(d-1)*(I-1)` using the SAME compact-limit law and subsequence.
The SAME witness assignment bounds `I-1 <= M*cost`. Retaining the strong cost
`cost <= (d+1)(d+2)*t/(1+t)`, rather than only its coarse Q budget, lets the
ORIGINAL Q absorb `M^(d-1)*(d+1)(d+2)` and yields the original scale
`|P|/|K| <= (1+M*Q*t)^d`. The actual centered brightness, original J/L cap,
threshold, retention of the prescribed simplex and affine restoration then
give the literal Main.

`proofs/CompleteSharpMainRadialProof.txt` is the complete written proof,
including the actual polar-simplex construction and all endpoints. It is
kept byte-identical to the independent written review, SHA256
`0c2e2eebf7f4409f4fdb56d68879eb5281b4d6db71337c9864f497922715d0e4`.
Its historical statement that formal Main remained to be assembled is
superseded by `formal/Entry005/SharpUpperMain.lean` and the literal checks in
`formal/UpperMainAudit.lean`. The old conditional modules and comments are
also preserved as historical sources; the final theorem uses the new direct
radial route, without taking their open finite-Minkowski proposition as input.

The complete mathematical source has 122 owned modules and 845 public proofs.
It contains the exact 102-module verified714 foundation, 83 previously
delivered additive proofs, and 48 new upper-Main proofs. It does not add or
reprove truncation sharpness. The parent separately reported independent
empty-kernel PASS for the 714 foundation and the literal truncationSharpness
goal; those independent audit scopes are not extended to the new Main here.

Author-side validation of the new Main passes:

- All 20 additive modules rebuilt to fresh regular outputs over the verified
  foundation, with `autoImplicit=false`, `maxSynthPendingDepth=3` and
  `warningAsError=true`; every compilation log is empty.
- All 131 additive proof signatures and recursive axiom sets, plus ten polar
  definitions, are checked. Only `propext`, `Classical.choice` and `Quot.sound`
  occur. Literal `sharpLocalGoal`, `sharpMainGoal` and original `MainTarget`
  checks pass.
- Exact radial source copies were separately reviewed and recompiled, and
  the actual directional/polar interfaces have separate literal checks.
- Exact final Main, retention and original target-alias sources were also
  independently recompiled to fresh outputs. Twelve scoped checks pass,
  including expansions of the literal original centroid and actual defect;
  their recursive axiom sets use only the standard three axioms.
- All 102 verified714 source-module bytes match the supported readable
  handoff. `Constants.lean`, `Targets.lean` and `MainTarget.lean` retain their
  original SHA256 identities in `evidence/source-manifest.json`.

An independent empty-environment trust-zero replay of the NEW integration is
still a separate audit, not claimed by this release. The new strict replay and
recursive standard-axiom check are reproducible as follows, using the pinned
Lean and dependency sources and the independently verified714 object cache:

```bash
python3 scripts/replay_upper_main.py \
  --packages-dir /your/pinned/packages \
  --lean-bin /your/lean-4.34.1-linux/bin \
  --verified714-cache /your/verified714/lib/lean
```

`--rebuild-all-owned` additionally rebuilds every included owned module.
The script creates an isolated private cache, follows read-only namespace
views, excludes all additive precompiled objects, checks source hashes and
dependency pins, and never downloads or edits dependency sources. It uses
the official mathlib `maxSynthPendingDepth=3` option; no upstream mathematical
source was changed to force compilation. The initial cache-view replay failure
was a missing Mxym namespace view, repaired in the portable script before the
passing replay. It was not a mathematical proof failure.

No false intermediate result from arXiv2603.17726v3 is used. No publication,
push, external message, author contact, sharing-policy change or security
setting change is made. The independently audited explicit `1/d` theorem and
all earlier frozen artifacts remain unchanged.
