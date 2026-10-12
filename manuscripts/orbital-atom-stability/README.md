# Orbital primal--dual theory and exact permutation-action atom stability

[Complete manuscript](paper.md) · [PDF](paper.pdf) · [Proof review](../REVIEW.md) · [Source map](../SOURCES.md)

A universal sharp orbital characterization for every finite action, a sharp
minimal-degree formula for doubly transitive actions, the complete two-subset
law for every n >= 4, three-subset classification for 3 <= n <= 120 and its
sharp all-degree asymptotic `1-18/n+O(n^-2)`. Part J proves all-rank transfer and
the rank hierarchy, and certifies every four-subset degree 11--50.

## Verification and reproduction

From the repository root:

```sh
python3 -B verification/finalization/strict_checker.py \
  notes/sharp-robust-permanent/code/check_all_two_subset_actions.py
python3 -B verification/finalization/strict_checker.py \
  notes/sharp-robust-permanent/code/check_three_subset_certificates.py
python3 -B verification/finalization/check_replay_guards.py
```

Two fixed triple-action JSON files contain 115 rational primal--dual witnesses
for degrees 6--120. The first 18 are checked on every conjugacy class; the next
97 use the proved compression and exhaust all 1,489,083 feasible types. Degrees
3,4,5 follow by triviality or complementation. The separate asymptotic proof
uses global analytic dual bounds and four positive rational primal families;
its symbolic replay requires SymPy 1.14 or compatible. The two-subset finite
replay through 40 supplements an all-degree proof. Four-subset certificates
cover 40 degrees 11--50, including 129,523 exhaustive type checks for 26--50.
Exact all-degree formulas beyond two-subsets and the higher-rank sharp
asymptotic conjecture remain open. There is no full Lean formalization.
The launcher preserves assertions in the entrypoint and imported helpers by
restarting an unoptimized isolated child when necessary.

This paper freezes the integration snapshot in SOURCE_PINS.json. Later parent
Sections 24 onward contain an all-fixed-rank theorem, added during finalization.
Those later results are outside this manuscript's replay scope; the conjecture
in its historical Section 23 should be read with that version context.

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
