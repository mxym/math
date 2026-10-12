# Proposed public CI

The uninstalled draft is [`ci/geometric-avoidance.yml.proposed`](ci/geometric-avoidance.yml.proposed). If separately approved for installation, its destination is `.github/workflows/geometric-avoidance.yml` at the repository root. It was prepared and statically checked locally; no GitHub Actions run was started or observed for this workflow.

## Behavior

On relevant pushes and pull requests, or manual dispatch, the workflow fetches the exact GitHub event commit by SHA into a fresh directory, verifies the checked-out HEAD, and runs:

```sh
cd formalizations/geometric-avoidance
python3 scripts/reproduce.py --bootstrap --fetch-dependencies
```

For a normal `pull_request` event, GitHub defines this SHA as the test merge commit. The workflow does not use `pull_request_target` and does not switch to a mutable branch tip. See [GitHub's event documentation](https://docs.github.com/en/actions/reference/workflows-and-actions/events-that-trigger-workflows#pull_request) and [default variables](https://docs.github.com/en/actions/reference/workflows-and-actions/variables).

The intended reproduction command rebuilds the project's own Lean sources and runs its audits, positive controls, and expected-failure controls. The workflow calls the project's single entry point so its local and public checks have the same scope. The exact check results must be established by running that entry point; a syntax check of this YAML is not evidence that the proof or online bootstrap passed.

## Minimal permissions and pinned inputs

- `permissions: {contents: read}`; other GitHub token permissions are unspecified and therefore disabled, as described in [GitHub's workflow syntax](https://docs.github.com/en/actions/reference/workflows-and-actions/workflow-syntax#permissions).
- No `uses:` actions, mutable action tags, external installer scripts, repository writes, issue comments, deployments, secret inputs, or credential persistence.
- Public checkout is anonymous HTTPS. No GitHub token is passed to the shell or stored in Git configuration.
- Lean's official release archive has an exact SHA-256 pin. All nine Lean package sources are pinned to full commits in the supplied manifest. See [DEPENDENCIES.md](DEPENDENCIES.md).
- `ubuntu-24.04` selects GitHub's standard x86_64 runner. Its image and preinstalled system tools remain GitHub-managed, mutable inputs; this is not a bit-for-bit hermetic environment.
- The runner must provide Python 3, Git, tar, zstd, and curl >= 7.81. The workflow fails clearly if a prerequisite is absent instead of installing more software. The curl floor avoids mathlib's extra helper-download fallback.
- Dependency build-cache downloads and the official Lean binary remain explicit trust inputs. Project build outputs are not restored from an Actions cache.

## Validation and first-run limits

Local validation checks YAML structure, event and permission scope, absence of third-party actions and privileged triggers, exact command and directory, and Bash syntax for every run block. These checks do not emulate GitHub's scheduler, network, disk capacity, package-cache service, or runner image. The 90-minute job timeout is an initial cap, not an observed runtime guarantee.

The first authorized remote run should confirm the checked-out SHA, bootstrap digest check, unchanged dependency pins, clean own-source rebuild, and the reproduction report. Logs remain in GitHub's normal job log; this minimal draft does not upload artifacts with another action. Path filters intentionally limit automatic runs to this project and its workflow; do not configure this path-filtered check as an unconditional required check for unrelated repository changes.
