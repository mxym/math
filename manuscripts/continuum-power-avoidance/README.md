# Large closed sets avoiding a continuum of power asymptotics

[Complete manuscript](paper.tex) · [PDF](paper.pdf) · [Proof review](../REVIEW.md) · [Source map](../SOURCES.md)

For each prescribed nonempty countable family with bounded gaps in its occupied dyadic logarithmic bins, and each epsilon > 0, one closed nowhere dense 1-periodic set of measure greater than 1-epsilon in every unit interval avoids infinitely many distinct values in every tail of every nonzero power germ with a power-controlled higher remainder. The compact corollary covers every affine null geometric progression, simultaneously over all ratios in (0,1).

## Verification and reproduction

From the repository root:

```sh
python3 -B verification/finalization/replay_continuum.py \
  --lean-bin /path/to/lean-4.34.1/bin \
  --dependency-project /path/to/pinned-dependency-project \
  --output /tmp/new-continuum-run
```

The main endpoint is `ContinuumRemainder.continuum_power_target : ContinuumPowerTarget`; the compact endpoint is `ContinuumRemainder.compact_power_avoidance`. The main traditional proof is unchanged. The public frozen release is at `formalizations/continuum-remainder-avoidance`. Use the pinned cache-miss adapter above for correct import parsing and Mathlib build options. The auxiliary upper-Banach-density obstruction is a written scope result, not part of the full Lean endpoint. This does not settle the entire Erdos similarity conjecture or avoid arbitrary flat smooth germs.

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
