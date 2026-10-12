# Exact checks and reproducibility

The English proof is in `paper.md` and `paper.pdf`. The scripts provide finite
exact regressions; they do not formally verify the general probability-law,
measure-theoretic, or convex-geometric arguments. In particular, the
corner-truncation script checks the deficit formula and its rate, while the
lower bound on distance to every product in the equality class is a written
proof.

## Standalone replay

Python 3.10 or newer is sufficient. No third-party packages, Git checkout, or
network access are needed. From the extracted source package:

```sh
python3 code/verify.py --output-dir build/verification
```

The default output directory, if the option is omitted, is `build/verification`
relative to the package rather than the caller's working directory. An explicit
relative output path is relative to the caller's working directory. A separate
absolute output directory also works. Shipped sources and `results/` are
protected: an output directory inside the package must be below `build/`.

Each checker runs in ordinary and optimized Python. Outputs must agree
byte for byte, and every mathematical check uses an explicit exception rather
than a Python `assert` statement. The aggregate writes `verification.json` and
three `.log` files only after all requested checks succeed. Generated outputs
are confined to the chosen output directory; subprocess working directories
and temporary inherited reports are outside the source trees. Report files
are replaced atomically so that an existing hardlink cannot redirect a write
into a shipped input. Unsafe ambient temporary-directory paths are ignored.

| Script | Exact cases | Scope |
|---|---:|---|
| `code/check_balanced_defect.py` | 4,930 | Balanced denominator-30 coefficient multisets with 4–8 coefficients; quantitative defect bound and two equality/strictness guards. |
| `code/check_rank_identities.py` | 750 | Signed cofactor identities and annihilating relations for rational bases in dimensions 3–7, using fixed seed 541. |
| `code/check_truncation_obstruction.py` | 16 | Independent horizontal/lifted facet-minor sums for dimensions 3–6 and truncations 1, 1/2, 1/3, 1/7; deficit identity and upper rate. |

There are 5,696 cases in total; the additional guards are not added to that
count. All arithmetic is exact integer or `fractions.Fraction` arithmetic.
Standalone scripts may also be run directly with `python3` or `python3 -O`.

## Optional external dependency replay

The standalone package does not include a repository checkout. To verify the
specified dependency inputs or replay inherited checks, supply an external
checkout yourself. Git is needed for this optional mode. The required commit is
`6785c1c830f8e19e2eb07b0bb89f4d475a8b154a` from
[mxym/math](https://github.com/mxym/math/commit/6785c1c830f8e19e2eb07b0bb89f4d475a8b154a).

For example, with an independently obtained checkout at `/path/to/math`:

```sh
git -C /path/to/math checkout --detach 6785c1c830f8e19e2eb07b0bb89f4d475a8b154a
python3 code/verify.py --output-dir build/verification/with-dependencies \
  --dependency-checkout /path/to/math
```

This validates the external checkout without running inherited scripts. Add
`--run-inherited-checks` to replay the pinned v2, v3, and v4 checkers as well:

```sh
python3 code/verify.py --output-dir build/verification/with-dependencies \
  --dependency-checkout /path/to/math --run-inherited-checks
```

The complete input list and byte hashes are in `code/dependency-inputs.json`.
The runner requires the exact Git HEAD and checks the working-file SHA-256 and
size of each input before creating or touching its output directory. The list
contains the three dependency manuscripts, the v2 and v3 checker/certificate/
reference-report triples, and the v4 regression checker. This validates those
inputs; it does not claim to audit all other files in the supplied checkout.

The inherited v2 and v3 checkers receive explicit temporary report paths.
Their ordinary and optimized reports must agree byte for byte and match the
pinned reference reports. The v4 checker produces stdout rather than a JSON
reference report; its ordinary and optimized stdout must agree. The aggregate
copies this evidence into `inherited/` beneath its chosen output directory.
It does not modify the external checkout's reports.

## Packaging regressions

To reproduce the packaging tests, Python 3.10+ and Git are required:

```sh
python3 code/check_package.py --report build/verification/package-tests.json
```

The test builds and extracts a minimal source archive containing the standalone
inputs and a shipped-reference sentinel. It runs from an unrelated directory
without a repository, compares ordinary and optimized driver reports, and
checks that the extracted sources and reference sentinel remain unchanged.
The fixture includes a report hardlinked to the shipped sentinel and an unsafe
ambient `TMPDIR`; these must cause no writes to source files. An external-output
run checks every file in the package, including its existing `build/` files.
It also supplies a local Git fixture at the wrong commit and verifies that
failure leaves existing output byte-identical and creates no new output
directory. Attempts to write into shipped `results/`, or to run inherited
checks without a dependency argument, must fail before output mutation.

For additional positive and corrupted-hash preflight tests, supply the same
pinned external checkout:

```sh
python3 code/check_package.py --report build/verification/package-tests.json \
  --dependency-checkout /path/to/math
```

This also checks validation-only mode and builds an isolated fixture with the
genuine pinned commit object but a corrupted manuscript. Both an existing
output directory and a nonexistent one must remain unchanged on hash failure.
The supplied checkout itself is read only.

Recorded reports in `results/` are release evidence. Fresh replay output goes
to `build/verification/` or another explicit separate directory; it is not
written over those recorded reports. A successful hash check establishes file
identity, not the correctness of a theorem.
