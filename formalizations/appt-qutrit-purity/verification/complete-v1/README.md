# Complete all-dimension physical APPT purity verification

**PASS.** Run `37968137659` verified source commit `f372047c63ba501b13301b4b3ba089c261e3722e`.
`RUN.json` is the original successful runner output, not a reconstructed status.
`workflow-run.json` and `workflow-jobs.json` are retrieved GitHub records.

## Scope and completed checks

The theorem is `APPT.Quantum.appt_purity_maximum_formula`: the attained maximum
of actual trace-square purity over physical APPT density matrices on C^3 tensor
C^n, for every n>=3. Its statement does not assume a spectral characterization
or PSD-corner conditions. It includes both the universal upper bound and attainment.

All 18 stages passed: exact source inventory; both deterministic generators;
original/mutated certificate checks; paired small kernel replay controls;
module-graph validation; all 879 bounded local modules; default Lake build;
sparse, corner, and endpoint positive/negative controls; the three endpoint
maximum controls; full positive empty-kernel replay; replay-support compilation;
and forged-final-theorem rejection.

The full positive replay checked **155,787 declarations / 58 roots** at
trust level zero. Root types and universe parameters were compared with the
originals. The only axioms are `Classical.choice`, `propext`, and `Quot.sound`.

The negative control preserves the original final theorem name, type, and
universe parameters but replaces the proof by `True.intro`. Its **8,581** actual
type/proof dependencies first replayed successfully; a separate fresh trust-zero
kernel then rejected that forged theorem for a declaration type mismatch.
Missing dependencies, unrelated errors, and timeouts cannot substitute for this
rejection. The original proof's full certificate closure is checked by the full
positive replay, not redundantly as unused dependencies of the corrupted proof.

## Source and build provenance

All 942 pinned source/tool/data files matched the successful report before
publication. All 879 module source hashes and log hashes were checked as well.
The final CI reused independently compiled, source/object-hash-bound components;
it does **not** claim a fresh 879-module build on one runner. `COMPONENTS.json`,
original component-job records, and `UNIFORM_CACHE_PROVENANCE.json` preserve that
distinction. Cached proof objects are not proof oracles: the original mathematical
closure is independently checked in an initially empty kernel at trust zero.

`python3 reproduce.py --fresh --jobs 2` removes this package's build directory
and recompiles the complete project with individual module limits. External
Mathlib dependency caches remain separate.

## Literal records and earlier failures

`literal-evidence.tar.gz` retains the entire original CI artifact, including all
module records/logs and complete declaration inventories. Readable logs here are
verbatim copies. `SUMMARY.json` records scope, counts, source binding, and archive
hash. No earlier failed run is relabeled as successful.

Run 37956727424 passed the full proof replay but failed an auxiliary n=3 test
whose tactic did not normalize rational arithmetic. Run 37961424823 passed the
corrected tests and full replay again, but its redundant corruption replay timed
out. This final run resolves those verification issues without changing any of
the 879 mathematical source files from the original successful proof replay.
