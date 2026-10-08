# Fractional covering spectra and near-design extremizers

[Complete manuscript](paper.md) · [PDF](paper.pdf) · [Proof review](../REVIEW.md) · [Source map](../SOURCES.md)

The entire intersecting finite-ratio limiting frontier, quantitative design-boundary deletion stability and an iff characterization at integer ratios, the exact fixed-matching limiting spectrum and its finite allocation formula, and the limit at diverging matching number. Part F allows rank at most r. The near-design statements in Part D require r-uniformity. Fractional and integer assertions are explicitly distinguished.

## Verification and reproduction

From the repository root:

```sh
python3 -B notes/sharp-fractional-cover-frontier/verify.py --lean
python3 -B notes/fractional-design-stability/verify.py --lean
python3 -B notes/fractional-matching-spectrum/verify.py --lean
```

Put the pinned Lean bin directory on PATH before running these commands. The three finite formal projects expose nine frontier exports, seven extraction/converse exports, and three additional anchor exports (plus nine reused frontier exports). They do not formalize all limits, LP duality, Wilson design existence or Kahn covering inputs. The complete written proofs cover those dependencies and steps. No exact finite optimum for every arithmetic (r,m), general weighted nonuniform conjecture, or unrestricted integer-cover frontier is claimed.

The [common finite replay](../../verification/finalization/replay_finite.py) runs
all relevant exact checkers in disposable copies and compares normal and
optimized-launcher output with assertions enabled. The
[verification directory](../../verification/finalization/README.md) supplies
fresh records, commands, exact pins and the trust boundary. Hashes establish
file identity, not mathematical correctness. Floating diagnostics are never
used as universal proof certificates.

## Build and scope

```sh
python3 -B manuscripts/assemble.py
python3 -B manuscripts/build.py --output /tmp/new-paper-build
```

The common builder produces all five PDFs without TeX shell escape. Historical
proof sources remain unchanged. This is an AI-assisted manuscript with a
complete written argument; no external human peer review, journal submission,
or literature-wide priority certification is represented as completed. See
[PRIOR_WORK.md](../PRIOR_WORK.md) for the limited attribution comparison.
