# Sharp simplex stability with an explicit quadratic coefficient

[Complete manuscript](paper.tex) · [PDF](paper.pdf) · [Proof review](../REVIEW.md) · [Source map](../SOURCES.md)

Every full-dimensional compact convex body in dimension d >= 3 and every prescribed maximum-volume inscribed simplex. The sharp exponent is 1/(d-1), the coefficient is at most 4096 d^2, and the original simplex centroid is retained. The exact truncation calculation proves the obstruction even for the best maximum simplex and for affine Banach--Mazur distance.

## Verification and reproduction

From the repository root:

```sh
python3 -B formalizations/sharp-simplex-upper-bound/scripts/verify.py \
  --lean-bin /path/to/lean-4.34.1/bin \
  --dependency-project /path/to/pinned-dependency-project \
  --output /tmp/new-simplex-upper
python3 -B formalizations/simplex-truncation-sharpness/scripts/verify.py \
  --lean-bin /path/to/lean-4.34.1/bin \
  --dependency-project /path/to/pinned-dependency-project \
  --output /tmp/new-simplex-lower
```

The exact targets are `Entry005.sharpMain : Entry005.sharpMainGoal` and `Entry005.truncationSharpness : Entry005.truncationSharpnessGoal`. The former uses the original larger `gSharp` coefficient. The quadratic coefficient in this manuscript has a complete traditional proof, not a full Lean formalization. These are separate claims. The literal `Main` target is included in the upper replay; the lower package does not claim the upper theorem. The optimal dimension order remains between linear and quadratic.

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
