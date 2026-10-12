# Simplex truncation sharpness formalization

**The literal target `Entry005.truncationSharpnessGoal` is proved. The prescribed stability upper bound `Entry005.sharpMainGoal` remains open in this package.** This is a formalization of the truncation sharpness construction, not a formalization of the entire paper.

The closed theorem is

```lean
theorem Entry005.truncationSharpness : Entry005.truncationSharpnessGoal
```

It uses the actual geometric `entryDefect`, a simplex that is maximum among **all** inscribed affine simplices, that simplex's own original centroid, and the literal exponent `1/(d-1)`. The final theorem assumes no volume, facet, projection, defect, or maximality formula. Its statement and proof are in [TruncationSharpness.lean](project/formal/Entry005/TruncationSharpness.lean#L12); the [target definitions](project/formal/Entry005/Targets.lean) are byte-identical to the pinned public source.

For every dimension `d ≥ 3`, exponent `α > 1/(d-1)`, constant `C ≥ 0`, and tolerance `ε > 0`, the theorem supplies a parameter `0 < t < min(ε,1)`, the actual body

\[
K_t=\{x\in\mathbb R^d:x_i\ge0,\quad t\le\textstyle\sum_i x_i\le1\},
\]

and a genuine maximum inscribed simplex `S`, with `0 < entryDefect(K_t) < ε` and

\[
C\,\operatorname{entryDefect}(K_t)^\alpha
 < \operatorname{excess}(K_t,S).
\]

The exhibited simplex is `conv(t e_i,e_1,…,e_d)` for a coordinate index `i`. Its own-centroid excess is exactly `(d+1)t`; the actual defect is asymptotic to `d(d-1)/(d+1)² · t^(d-1)` as `t → 0+`. The obstruction existentially chooses a maximum simplex. It does not assert this excess for every maximum simplex or after minimizing over all maximum simplices.

## Read the result

- [THEOREM.md](THEOREM.md): definitions, complete quantifiers, exact identities, and non-claims.
- [PROOF_ROADMAP.md](PROOF_ROADMAP.md): the geometry, determinant bounds, centroid calculation, and real-power argument, linked to the Lean sources.
- [VERIFICATION.md](VERIFICATION.md): public replay instructions, independent evidence, controls, and trust boundary.
- [PROVENANCE.md](PROVENANCE.md): the exact input, inherited checkpoint, pinned public targets, and upstream reuse.
- [LICENSE_NOTICE.md](LICENSE_NOTICE.md): preserved attribution and existing component terms; no new blanket license is assigned.

## Recorded independent audit

The 2026-10-07 independent audit passed for this exact source snapshot:

- **125** mathematical modules freshly compiled, with zero warnings or failures.
- **850** public proof declarations checked against source-derived names and actual declaring modules.
- **1,849** module-owned declarations, including private and generated declarations, all safe and nonpartial.
- **1,849 roots and 55,163 recursive declarations** replayed from an empty Lean kernel environment at trust level zero; no skipped roots, and unchanged root types and universe parameters.
- Only `propext`, `Classical.choice`, and `Quot.sound`, or subsets thereof, occur as permitted logical axioms.
- Positive semantic probes and the intended negative target/formula/kernel controls passed.

These are declaration and verification counts, not counts of new research theorems. The 850 public exports comprise 714 inherited exports and 136 added exports; eight added exports reuse exact OpenAI/math simplex-volume proof bodies. The audit is independent AI/model-based verification, not an external human referee report or a novelty certification. Retained results are in [audit/independent/](audit/independent/); the independent Lean checking programs are in [audit/checks/](audit/checks/).

## Package layout and reproduction

- `project/`: all 290 files from the audited input: 288 byte-identical members and two explicitly redacted nonmathematical metadata records. All 125 mathematical modules are byte-identical, including the literal Targets file.
- `audit/independent/`: compact retained independent evidence, distinct from the source author's submitted logs.
- `audit/checks/`: independent Lean statement, ownership, replay, and boundary checks.
- `scripts/`: public integrity, fresh verification, and local archive entry points.
- `provenance/`: input identity, complete original-source hashes, required payload hashes, and toolchain-file hashes.
- `third_party_licenses/`: retained existing official licenses and notices.

Start with `python3 scripts/verify_integrity.py`, then follow [VERIFICATION.md](VERIFICATION.md) to prepare the exact pinned toolchain and run the public `scripts/verify.py` entry point. The public replay uses fresh owned outputs outside the preserved source payload. Checking hashes alone does not check the theorem, and importing compiled objects alone is not an empty-kernel replay.

The authoritative **current public manifest** is `SOURCE_MANIFEST.json`. The preserved `project/BUNDLE_MANIFEST.json` has 289 records describing the original input before the two metadata redactions; it is historical input identity, not the current public payload manifest. `project/SOURCE_FILES_SHA256.json` is a historical 215-record pyramid-checkpoint manifest, with seven mismatches against this later snapshot. Do not run the old `project/scripts/replay_text_bundle.py` or `project/scripts/package_pyramid.py` on the current source. Do not replace the historical manifest to conceal those differences. The original bootstrap/verifier does not read that old manifest, but writes logs inside its working copy; the public `scripts/bootstrap.py` creates a disposable copy outside the release and then runs the independent verifier. All `project/scripts/` files are retained original tools; do not run their packaging, freeze, coverage-generation, or build commands directly inside this sealed public tree.

The full Main upper bound, optimal upper constants, classification of all maximizing simplices, arbitrary-`p` centroid formulas, best-maximum estimates, Banach–Mazur estimates, and Rogers–Shephard claims are not certified here. Historical prose and comments are retained as records, not silently promoted to additional Lean results.
