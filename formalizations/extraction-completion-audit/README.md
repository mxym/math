# Independent completion endpoint audit

Current fixed mathematical/manuscript source:
`cfdd2a6c7954f1956f1832cdabe28dd6e018fe3a`.
Read `REVIEW_E4CF_20261019.md` for independent source/quantifier review and
`WRITTEN_REVIEW_PROVENANCE.json` for the separately archived internal written
review. Historical reviews and 29/27-root prechecks remain unchanged. This is
internal AI verification, not external human peer review or a novelty certificate.

`SCOPE.json` defines 518 theorem roots, 175 concrete model definitions and 84
same-type proof controls. Counts describe audit inputs. All 87 declarations in
the final author's 27-group manuscript map are explicit selected roots. The
original manuscript and old 39/91/235/444, 83/11,608 audit scopes are preserved;
4,378 tracked old inputs are compared against their initial aa1 Git blob bytes.

## Reproduction

`python3 reproduce.py --plan` performs source/list/map planning only.
`--preflight` also checks actual D backing, fixed execution hashes, pinned clean
dependencies and protected inputs; it does not verify mathematics.
Once final READY scope is settled, `--freeze-source` binds all mathematical,
configuration, audit, eight revised TeX, README and both source-map inputs.
`python3 reproduce.py --fresh` freshly builds the eleven selected new packages,
checks every declaration kind/type/axiom, replays the entire proof-and-definition
closure in an empty trust-zero kernel, and requires all 84 same-type forgeries
to fail at the exact root with kernel declaration-type mismatch. Every control
first positively replays its type dependencies. Allowed axioms are only propext,
Classical.choice and Quot.sound. Final PASS is scoped to exact bound source.

Local execution always uses the D mount/backing-image guard and shared build
lock. Fresh cleanup first validates all owned ordinary `.lake/build` paths; it
never removes shared Mathlib, earlier sources/evidence, the backing image or
Gaussian dirty work. Evidence is under this D-backed tree's `verification/`.

The limited snapshot scripts are historical/diagnostic tools, not final full
reproduction. `snapshot_precheck_be64.py --replay` selects only its literal ten
theorems/twelve definitions and four controls; every draft declaration still
gets an ordinary kind/type/axiom check. Do not generalize that limited replay.

## Hosted CI

`extraction-completion.workflow.yml` is a new workflow template for the parent
to copy byte-for-byte to `.github/workflows/extraction-completion.yml`; no old
workflow is changed. See `CI_PLAN.md`. Local D verification is not hosted CI.
`--github-actions` is explicit and rejects local Windows/WSL. It requires the
hosted Linux/X64 context, exact event SHA and runner workspace, runner-only
cache/temp/toolchain/evidence directories, actual resource checks and exact
Lean/Lake release binary hashes. CI does not bypass the local D rule.

`ci_driver.py` bootstraps pinned source/toolchain/cache, runs the whole fresh
bound audit, records pre/post input/tool hashes and seals a complete artifact.
A separate job downloads it and `verify_artifact.py` checks every byte, source
binding, kind/type/axiom coverage, positive trust-zero closure, exact controls,
fresh scope and run provenance. A real CI result is pending until those jobs run.

Classical compiler Turing bit complexity, the sharp APPT entropy optimizer/
maximum-capacity coefficient, growing-D inverse-Haar moment asymptotics and
unstated equality/cap-boundary laws remain excluded. Later circuit branch
successors outside cfdd are not certified.
