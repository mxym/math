# Portable exact verification

Python 3.10 or newer and its standard library suffice. No network access, Git checkout, SciPy, prior manuscript file, or numerical point generator is required. Read `DEPENDENCIES.md` for the mathematical premises imported from pinned entry-005 sources.

## Complete replay

From the package directory:

```sh
python3 verify.py
```

From any other working directory, pass the actual location of the script:

```sh
python3 /path/to/package/verify.py
```

The script resolves supplied inputs relative to its own file. It checks the publication manifest, the original candidate's protected certificate/data hashes, and unchanged arithmetic source segments. It then runs all new upper checkers in ordinary and optimized Python, from an unrelated temporary directory, with temporary output reports. Normal and optimized finite, tail and contextual reports must be byte-identical and match the supplied exact reports. It also checks the analytic large-factor constants and the optional classical-context constants.

The default leaves every delivered certificate and report unchanged.

Verify the received bundle **before** rebuilding the PDF. The publication manifest checks its as-delivered bytes. A local TeX version, PDF metadata, or build environment may change `paper.pdf` even when the mathematical text is unchanged; no byte-identical PDF rebuild is claimed. The exact certificates and arithmetic sources have separate immutable-input checks.

To retain a summary outside the package:

```sh
python3 verify.py --report /path/to/replay-summary.json
```

Individual mode and integrity-only options are available:

```sh
python3 verify.py --mode ordinary
python3 -O verify.py --mode optimized
python3 verify.py --integrity-only
```

An integrity-only run reports that mathematics was not replayed; it must not be presented as a new proof replay.

## Direct checkers

These commands also work when the script is invoked by its actual path from an unrelated working directory. The finite and tail checkers default to their sibling certificate files:

```sh
python3 check_finite.py --quiet
python3 check_mixed_tail.py
python3 check_mixed_large_dimensions.py
python3 check_classical_upper.py
```

Explicit certificates and output paths are optional:

```sh
python3 check_finite.py mixed_finite_points.json --quiet --report /path/to/finite.json
python3 check_mixed_tail.py mixed_tail_certificate.json --report /path/to/tail.json
python3 check_classical_upper.py --output /path/to/classical.json
```

A caller-supplied relative path is interpreted relative to that caller's working directory. Default input paths are interpreted relative to the script. The classical checker is read-only unless `--output` is specified; its inequalities concern existing unrestricted comparison constants, not a new theorem.

## What is verified

- The finite certificate covers all 19,900 integer pairs 1≤r≤s≤199. Each rational supporting plane proves its entire continuous state rectangle, with certified uniform upper margin below −3/2000.
- The tail certificate covers 15,568 dyadic cells, of depth at most seven, with exact adjacency and no overlap for every r=1,…,199 and the entire real reciprocal-dimension interval [0,1/200]. Strong concavity bounds prove all continuous states in every cell; the uniform upper margin is below −1/10^8.
- The large-factor checker verifies exact constants for the analytic closure proof when r,s≥160, plus exp(1049/1000)<571/200. The infinite-dimensional conclusion uses the written analytic argument, not a finite regression grid.
- The class is generated from a point by finite products and joins and **invertible affine maps on affine hulls**. Rank-dropping maps are excluded. The package proves Γ_C≤exp(1049/1000)<2.855 for that class.

Every proof decision uses explicit exceptions, integers, fractions, and proved rational logarithm intervals. Python optimization therefore removes no mathematical condition. Numerical generators are discovery aids only and require SciPy; they are not imported by the verifier and should not be run to validate the saved certificates.

The inherited lower endpoint and its historical replay are documented separately in `DEPENDENCIES.md`. The complete replay here certifies the new upper computation; it does not silently download or rerun the old lower certificate.

## Assembly-only option

While preparing a publication manifest, an editor may use:

```sh
python3 verify.py --skip-publication-manifest
```

This still checks immutable inputs and arithmetic and runs every chosen mathematical checker, but explicitly reports that publication-manifest integrity was skipped. Final recipients should use the default command after the publication manifest is generated.

`SOURCE_MAP.json` records original candidate hashes, the pinned upstream statements, and editorial transformations. The publication manifest hashes the current assembly. Neither is a digital signature or a proof-assistant certificate; the exact mathematical argument remains the supplied English proof and its checked inequalities.
