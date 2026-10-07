# Finite Lean proofs for mxym/math

This standalone project exports 68 kernel-checked theorems: the finite balanced
Rademacher bound and full equality criterion, a quantitative coefficient-defect
bound, normed-relation/cofactor balance, determinant sign identities, weighted
finite defect/Jensen results, transport scalar inequalities, explicitly defined
scalar recurrences, and four attributed OpenAI/math finite/scalar results.

The normed cofactor corollaries derive balance from the proved vector relation
and supplied unit norms on active columns. They retain both equality mechanisms:
support of size at most three or a half-mass coefficient. A convex-body norm,
boundary normalization, measure integration, exposed-point rigidity, geometric
classification, the coefficient-distance bound and global optimality are outside
scope. [coverage.json](coverage.json), [coverage.csv](coverage.csv) and
[COVERAGE_REPORT.txt](COVERAGE_REPORT.txt) give all exact assumptions and gaps.

## Reproduce

On Linux x86_64 with Bash 4+, curl, git, tar, sha256sum and Python 3.11+, enter
`lean/` and check the delivered files before running the official bootstrap:

```bash
sha256sum -c CHECKSUMS.sha256
bash scripts/bootstrap.sh
python3 scripts/check_controls.py
```

The bootstrap installs official elan 4.2.4 and Lean 4.34.1 under `.elan/`, fetches
the committed dependency revisions, obtains the official mathlib module cache,
performs a clean project build, audits all theorems and regenerates coverage.
The controls compile ordinary Lean semantic examples and reject deliberately
corrupted reporting/source inputs in isolated temporary copies.

With the pinned toolchain and dependencies already available:

```bash
bash scripts/verify.sh
python3 scripts/check_controls.py
```

Select the pinned elan binaries on PATH; for a project-local install:

```bash
export ELAN_HOME="$PWD/.elan"
export MATHLIB_CACHE_DIR="$PWD/.cache/mathlib"
export PATH="$ELAN_HOME/bin:$PATH"
```

On another supported platform, install official elan, then run
`elan toolchain install "$(cat lean-toolchain)"`, retrieve the modules listed in
`scripts/mathlib-modules.txt` with `lake exe cache get`, and run the verification
commands above. Preserve `lake-manifest.json`; do not substitute `lake update`.

## Pins and evidence

- Lean 4.34.1, compiler `5045d0056413266e57c625dcd7c365b10e377c52`.
- Lake `5.0.0-src+5045d00`.
- mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`; all nine dependencies
  have committed revisions and reviewed official origins.
- [INDEPENDENT_AUDIT.md](INDEPENDENT_AUDIT.md) summarizes the independent checks.
- `Audit.lean`, `axiom-report.json` and `logs/axioms.log` record every axiom set.
- `Statements.lean` and `logs/statements.log` record all 68 full signatures.
- `controls/IndependentAudit.lean` inventories compiler declarations and directly
  traverses checked constant types and stored proof bodies.

All theorem axiom sets are subsets of `propext`, `Classical.choice` and
`Quot.sound`. Project proofs use no sorry, custom axiom or trusted native proof
shortcut. The trust boundary includes the official Lean binary and official
pinned dependency `.olean` cache. Project proof modules were rebuilt from source;
Lean and all mathlib dependencies were not rebuilt from source, and no external
independent kernel checker was run.

The delivered build log records the verified clean build; its machine-specific
path was normalized to `.lake/build` for redistribution. The theorem signature
and axiom output is unchanged. Running verification replaces the logs with a new
run. CHECKSUMS.sha256 describes the delivered payload, before those updates.

Source attribution, exact upstream reuse and paper snapshot pins are in
[PROVENANCE.md](PROVENANCE.md) and `references/SOURCES.json`. Preserve
`vendor/openai/LICENSE` when using the upstream-derived files.
