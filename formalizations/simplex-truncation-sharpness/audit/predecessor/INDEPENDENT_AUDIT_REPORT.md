# Actual finite-pyramid / B / same-body bridge: independent audit

Date: 2026-10-07 UTC. Audit target: the exact immutable Library v0 archive
`[private artifact identity omitted; see archive SHA-256]`,
`entry005-actual-pyramid-20261007.zip`, 526,968 bytes, 216 files, SHA256
`7cb50eb59e03ac286d9758aebd0a8b988e968e208c80d99e6f59f47711900bbd`.

## Outcome

**PASS for the exact audited bridge snapshot.**

- 102/102 mathematical owned modules freshly compiled; 16 pinned dependency
  modules also rebuilt. Zero successful-build or audit warnings.
- All 714 independently source-enumerated public theorem signatures and axiom
  reports checked, with actual declaring-module ownership.
- All 1,499 actual module-owned declarations independently enumerated:
  1,305 theorem declarations and 194 definitions, all safe and nonpartial.
  Four would be missed by a simple Entry005/Mxym/OAI namespace filter.
- All 1,499 owned roots replayed from an empty trust-level-zero kernel
  environment, across 54,678 recursive declarations, with unchanged root types
  and universe parameters; only the three permitted logical axioms.
- The intentionally ill-typed theorem was rejected by the kernel negative
  control. All 14 inherited mathematical control files passed.
- The ten audit-parser adversarial controls passed in normal and Python -O
  execution. Provenance checks also passed under Python -O.
- All 216 frozen source/archive files remain byte-identical after the checks.
  All nine dependency Git pins and tracked source cleanliness were rechecked.
- The two independent semantic reviews, all 27 inherited affine module byte
  identities, all 56 borrowed owner module identities, and the three narrow
  iid statement/body copies passed.

The full final machine-readable result is
`checks/independent-verification.json`; the independent source audit and
replay logs are under `logs/`. No delivered author's build log was substituted
for these new checks.

This is an independent audit of the finite-pyramid / B / normalized general-body
bridge in this exact snapshot. It is not an audit or completion claim for a later
627-assembly or truncation-sharpness release. The original prescribed-maximum-
simplex Main and full sharpness targets remain unproved by this increment.

## Mathematical findings

The source semantics were independently reviewed along two complementary paths.
Full reports are `FINITE_GEOMETRY_REVIEW.md` and `SAME_WITNESS_REVIEW.md`.

- The actual unit-height pyramid is a literal convex hull. Its actual Borel/Haar
  volume is proved to be V/(d+1) by real radial slices and Fubini.
- The actual bottom facet area is V. The side facet chart is a genuine linear
  isometry/translation of a radial cone, giving Ai sqrt(1+hi²)/d.
- An empty original supporting section becomes the singleton apex in the lifted
  side section. The proof treats this explicitly and proves zero side area.
- Actual finite Cauchy geometry, intrinsic hyperplane projection Jacobians and
  convex-fiber extrusion give the literal projection body as its facet zonotope
  and the extra volume term V d^(-d) |ΠK|. The segment normalization has no
  missing factor two.
- Height-first iid coordinates are transported by an actual Euclidean isometry.
  The exact ordered-iid/factorial coefficient and dilation give
  |sideZ| = V^(d+1)/(d+1)! B.
- The finite geometric entryA identity is B/((d+1)A). Positivity of V, the
  projection-body volume and A is proved before denominator cancellation.
- For compact convex K containing the closed unit ball, both A and B pass
  through one actual finite-law compact limit, with the same μ and subsequence φ.
  Actual pyramid dilation containment and projection-ratio continuity are proved.
- The final joint theorem destructs the owner's joint law/assignment existence
  result only once. It preserves that μ, φ and the original point tuple and
  assignment. The geometric entryA proof is applied to precisely these data.
  D=(d+1)A e and D/B=(d+1)e/(1+(d+1)e) are then obtained for that same law and
  used in its original assignment estimate. No separately selected existential
  law is silently identified with it.
- Generic iid algebra leaves honestly take an entryA premise. The final actual
  geometry wrappers prove and discharge that premise. No required pyramid
  volume, facet-area or B identity appears as an assumed final geometry premise.

### Essential scope

The principal finite projection-body/moment bridge has finite labels, a
nontrivial finite-dimensional real inner-product Borel ambient space, unit
injective normals, strictly positive support numbers, and compact halfspace
intersection. Distinct-normal redundant/empty/low-dimensional supporting
sections are allowed; duplicated normals are not covered. The pyramid height is
1; hi is a support number. The general compact-convex pyramid volume lemma is
broader and covers empty/zero-volume bases and dimension zero; this does not
remove the principal bridge's positive-dimension assumptions.

The arbitrary-body existence wrappers concern normalized K containing the closed
unit ball and nontrivial `Space d`. Their conditional limit leaves specify the
actual finite-law weak limit, the same μ and a strictly increasing φ. They do not
establish uniqueness of a general cone law or identify it with a separately
defined surface-area-measure construction.

The final joint conclusion exports D but does not add the separate D/B identity
as a conjunct; the identity is proved for the same witness and consumed in the
assignment proof. Its polar support is the literal level set h_K(x)=1, with raw
AE and measure-support inclusion. No separate frontier-equality theorem is
claimed. An inherited Targets comment calling thresholdGate unproved is stale:
the threshold gate is already proved. Main and sharpness remain distinct.

## Exact reconstruction and trust boundary

The frozen source extraction was checked against all 216 archive members and the
215-entry bundled file manifest. An independent source parser identified all
102 mathematical modules and 714 public theorem names, and reconstructed the
transitive import graph (4,722 modules). Public names are checked against actual
declaring modules in the newly compiled environment, rather than inferred only
from namespace prefixes.

The compiler is official Lean 4.34.1, commit
`5045d0056413266e57c625dcd7c365b10e377c52`; mathlib is
`d13f23b723b8a846827a245b89c10fc7d3f11612`. All nine lockfile package revisions
were independently compared to local Git HEAD and their tracked source trees
were clean. Exact results are in `checks/independent-pins.json`.

All current owned output starts in a new audit-owned directory. Only official
dependency cache and the prior cone533 audit's read-only dependency overlay are
borrowed. Entire cached subdirectories are symlinked; paths are expanded only
where a missing dependency must be rebuilt. No whole-cache copy is made. There
are 16 missing dependency modules, rebuilt from the pinned official sources.

An initial NormDet dependency compilation failed because the ad hoc direct
command omitted mathlib's official `maxSynthPendingDepth=3` option. The literal
official lakefile setting was added for the retry, which succeeded without
changing its source or weakening the kernel. The initial error remains in
`logs/build-driver-initial-option-mismatch.log`. Successful owned outputs from
an interrupted build were resumed by exact file/log checks; they were not
misrepresented as a new second complete build.

The independent empty-kernel replay replays the recursive
constant closure from an empty trust-level-zero kernel environment, follows
inductive constructors/recursors as well as used constants, and verifies every
owned root's type and universe parameters against the compiled environment.
The allowed logical axioms are exactly propext, Classical.choice and Quot.sound.
Compiler/frontend/runtime authenticity remains a trust boundary; the entire
mathlib source tree is not rebuilt.

## Historical identity and attribution

Independently read historical references were used, rather than treating the
current package's self-reported hashes as external evidence:

- Original affine147 Library v0 archive
  `[private artifact identity omitted; see archive SHA-256]`, SHA256
  `a113744d701fa5d0be2f917553cf1e433d079558409716835d8d9bbe1eb7e7ee`.
  All 26 inherited proof modules plus its umbrella are byte-identical.
- Of the 56 whole owner dependency modules, 54 are byte-identical to the
  independently audited frozen cone533 source archive.
- The two later polar/joint modules are byte-identical to the actual complete
  627 assembly source patch read from the owner's Page at sequence16:
  `[private artifact identity omitted; see archive SHA-256]`, v0, 925,856 bytes, SHA256
  `3a7b187e059d3da90e223ef087c4c592431ba4635b55d3271608a69098efb4b3`.
  This use checks historical file identity only, not the complete 627 assembly.
  These two modules are also compiled and kernel-audited as part of the current
  exact 714 package.
- A previously supplied supposed 562-source ID actually resolved to a 533
  source patch. It lacks the two later files, and was not used as their baseline.
  Its receipt/hash is retained as a provenance diagnostic, not accepted proof.
- The three narrow iid helper statements and bodies are exact substrings of
  the preserved owner module. Thus 82 public exports mean 79 new proof bodies
  and three narrowly reused exports, not 82 wholly novel proofs.
- Preserved OpenAI/math sources, Apache-2.0 license and adaptation notices are
  retained. The Model narrowed-import adaptation and inherited affine
  adaptations are disclosed; no whole-upstream certification is asserted.
  The maintained upstream source commit is adc7f1241b42e322a6451854ab7e4b4c146bf78a.
  All six preserved upstream source files were independently compared with that
  commit's local Git objects. The retained license differs from the original
  only by one extra terminal LF; its substantive text is unchanged.
  The generic copied UPSTREAM_NOTICE mentions a historical license path absent
  from this standalone bundle; the actual included license is
  sources/openai_math_LICENSE.txt. This is a minor packaging pointer issue.

Identity results are in `checks/frozen147-byte-identity.json`,
`checks/owner56-byte-identity.json`, `checks/iid-helper-byte-identity.json` and
`checks/license-provenance.json`.

## Explicit exclusions

- No full Main, final prescribed-simplex exponent/constants integration,
  equality classification or full sharpness proof is certified by this audit.
- No later 627-source assembly, Q supplement or newly delivered literal
  truncation-sharpness package is audited here.
- No clean source rebuild of all mathlib, compiler bootstrap, or operating
  system/runtime verification was performed.
- No public publication, GitHub push, source edit or sharing change was made.
- Files in the frozen target extraction are left byte-identical. Audit scripts,
  diagnostics, fresh build outputs and reports are separate.
