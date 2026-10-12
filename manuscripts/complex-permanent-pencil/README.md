# Sharp permanent--determinant norms in three and four rows

[Complete manuscript](paper.md) · [PDF](paper.pdf) · [Proof review](../REVIEW.md) · [Source map](../SOURCES.md)

The exact norm for every complex coefficient lambda, the exact coefficient lens, complete equality classification for the sharp absolute-value endpoint, the exact norm of every marginal-preserving three-row law, and the product of the exact amplification factors over independent nonidentical columns.

Part Q includes the sharp four-row absolute-value tradeoff for every nonnegative
determinant weight, all equality cases and pairwise quantitative deficits, the
four-row pencil norm for real coefficients, and exact parity tensor norms.
The rectangular two-row spectrum is proved for every column count.

## Verification and reproduction

From the repository root:

```sh
python3 -B verification/finalization/strict_checker.py \
  notes/complex-permanent-determinant/check_full_norm.py
python3 -B verification/finalization/strict_checker.py \
  notes/complex-permanent-determinant/check_lens.py
```

The full six-variable rational identities use 4096 interpolation nodes each,
with separate degree at most three. The lens identities use 1024 nodes each.
Repeated univariate interpolation makes these identity proofs. The four-row
checker verifies the two-row and Laplace identities by integer coefficient
comparison. Analytic inequalities, equality and tensorization are proved in
the text. There is no full Lean formalization or all-arity claim. The exact
four-row pencil formula is asserted for real coefficients only, and the
four-row probability result concerns the parity subfamily only.

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
