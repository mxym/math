# Additive finite and projection-cap Lean checkpoint

This standalone project has 101 public source theorem exports: the unchanged
original 68 finite/scalar exports, seven stochastic determinant-rigidity exports,
and 26 Entry005 exports (16 geometric lemmas and ten constant-positivity proofs).
The counts include supporting lemmas; they are not 101 distinct paper theorems.

The new geometric endpoint is a genuine theorem about actual nested compact
convex bodies in a finite-dimensional real inner-product space of dimension
d >= 2. For B subset K subset P subset M B, M >= 0 and eta >= 0, an eta bound on
every actual intrinsic hyperplane projection-volume deficit implies

    d_H(K,P) <= (d-1)(M+1) eta^(1/(d-1)).

Its proof constructs the closest support, perpendicular projection and disjoint
cap, proves actual Haar-volume gain and a cube bound, and takes the root. It
includes eta=0. The genuine projection-deficit hypothesis remains required.

The full sharp simplex stability theorem is unproved. Cone-law representation,
Cauchy projection, Minkowski scale control, integrated witnesses, maximum-simplex
normalization, the actual simplex-volume/matrix bridge, same-centroid conversion,
constant gates, end-to-end assembly and truncation sharpness remain open.
Five explicit Prop goal definitions typecheck and are not counted as proofs.
The target-only correction makes the threshold gate explicit and requires
arbitrarily small positive defect in the truncation goal. Constant positivity
does not prove the threshold gate. No whole-paper formalization or novelty
claim is made. See [COMPLETENESS_MATRIX.md](COMPLETENESS_MATRIX.md).

## Reproduce

Requires Bash 4+, Python 3.11+, curl, git, tar and sha256sum on Linux x86_64.
Enter this project's lean directory and run:

```bash
sha256sum -c CHECKSUMS.sha256
bash scripts/bootstrap.sh
python3 scripts/check_controls.py
python3 scripts/check_extension_controls.py
PYTHONOPTIMIZE=1 bash scripts/verify.sh
PYTHONOPTIMIZE=1 python3 -O scripts/check_controls.py
PYTHONOPTIMIZE=1 python3 -O scripts/check_extension_controls.py
```

Bootstrap installs official elan 4.2.4 and Lean 4.34.1 into project-local paths,
fetches the exact committed dependency revisions and official mathlib module
cache, then clean-rebuilds all owned proof modules and regenerates current
evidence. Preserve lake-manifest.json; do not substitute lake update.
With the pinned toolchain and dependency cache already available, start with
bash scripts/verify.sh instead. Select the official pinned binaries on PATH;
for the project-local install set ELAN_HOME="$PWD/.elan" and prepend its bin.

## Verification, evidence and trust

- Lean 4.34.1, compiler 5045d0056413266e57c625dcd7c365b10e377c52
- Lake 5.0.0-src+5045d00
- mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 and all nine reviewed official dependency origins/revisions
- All 101 exact signatures and axiom sets in coverage.json, coverage.csv, Audit.lean, Statements.lean and logs
- Every original 68 signature, axiom set and protected proof/pin/reference/vendor byte checked against baseline
- Compiler declaration inventory and direct recursive stored-type/body dependency traversal
- Ordinary and optimized Python checks, original semantic/adversarial controls, added stochastic/geometric controls and four geometric meaning mutations

All checked logical axiom sets are subsets of propext, Classical.choice and
Quot.sound. No owned source uses sorry, custom axiom, unsafe/opaque declarations,
native_decide or disabled kernel checking. Compiler-generated evaluation
auxiliaries are inventoried; a pre-existing unsafe recursion evaluator is not
a logical proof dependency. All safe owned logical roots have no transitive
unsafe, partial or missing constant dependencies.

The trust boundary includes the official Lean binary, standard library and
pinned official dependency .olean cache. All owned modules were rebuilt from
source; Lean/mathlib were not rebuilt, and no separate external kernel checker
was run. Recorded public logs normalize machine-specific paths. Verification
regenerates logs and reports; CHECKSUMS.sha256 identifies the frozen delivered
payload before those changes. baseline/ contains labeled historical 68-export
records, not current 101-export verification claims.

[PROVENANCE.md](PROVENANCE.md), source-integrity.json and references/ document
original source pins, exact-byte imports and the sole target correction.
The existing OpenAI/math attribution and Apache-2.0 license remain unchanged.
The project does not assign a new license to the authored research/proofs.
