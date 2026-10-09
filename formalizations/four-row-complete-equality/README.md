# Complete equality classification for the sharp four-row tradeoff

**Yongxian Zhang (张永贤)**, School of Computer Science and Engineering,
South China University of Technology. Email: mxymmxym1@gmail.com.
ORCID: 0009-0000-3864-3536. No external funding; AI-assisted research.
Original new material: all rights reserved, subject to existing repository
licenses and third-party notices. This is formal verification, not external
peer review or a priority claim.

## Exact theorem

For every actual complex 4x4 matrix A and every real c>=0,

    |per A| + c |det A| <= max(3/2, 1+c) * product_i ||A_i||_2.

Equality holds if and only if at least one of the following applies:

* A has a zero row.
* A_ij=u_i v_j, all u_i and v_j are nonzero, all |v_j| are equal, and c<=1/2.
* A is monomial (one nonzero entry in each row and each column), and c>=1/2.

Thus the entire inequality and equality statement of **Theorem 1** in
[the manuscript](../../notes/four-row-permanent-tradeoff/PAPER.md) is covered,
including the critical weight and degenerate zero-row cases. Optimality and
the exact real-coefficient pencil norm from v1 are included unchanged.
The all-n rectangular, quantitative-deficit, convex-power, and tensorization
extensions are **not** certified by this package.

Import `FourRowCompleteEquality`; the main theorem is
`FourRowTradeoff.sharp_four_row_complete`. The exact matrix classes are
`FourRowTradeoff.IsFlatRankOne` and `FourRowTradeoff.IsMonomial`.
The final theorem assumes neither nonzero rows nor any equality bridge.
See the [paper-to-Lean map](FORMALIZATION_MAP.md),
[complete proof supplement](PROOF_SUPPLEMENT.md), and `Statements.lean`.

## Fixed versions and reproduction

Lean 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`.
Mathlib commit `d13f23b723b8a846827a245b89c10fc7d3f11612`.
All transitive dependency revisions are fixed in `lake-manifest.json`.
The six original v1 modules are byte-identical copies, identified in
`PROOF_SOURCES.json`; the old package and old verification evidence are not modified.

With pinned dependencies prepared in this directory:

```sh
lake build
python3 reproduce.py
```

Or reuse a matching dependency project read-only, with the actual Lean binary:

```sh
python3 reproduce.py --dependency-project /path/to/pinned/project \
  --lean /path/to/lean-4.34.1/bin/lean \
  --work-dir /path/to/new-nonexistent-directory
```

The runner verifies source hashes and every dependency commit, rejects tracked
modifications in dependencies, clears external LEAN_PATH overrides, creates
an empty owned-build directory, and recompiles all 12 modules. It then replays
all 112 named declarations and their entire dependency closure into an empty
Lean kernel at trust level zero, comparing the root types and universe levels.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted as axioms.
No external mathematical premise, `sorry`, custom axiom, or native computation
oracle is used. The dependency collector itself is verification tooling,
outside the mathematical closure.

Three positive examples and two deliberately invalid proof controls are
included. The invalid controls must fail at a proof goal, not because of
missing imports. They are not registered as Lake library roots.

## Current verification evidence

[evidence/v2/VERIFICATION.json](evidence/v2/VERIFICATION.json) records the newly
performed run, completed at **2026-10-09T09:09:14.503384+00:00**: all **12 modules**
were freshly compiled, and **112 named roots / 15,593 dependency declarations**
were replayed in an empty kernel at trust level zero. Its axiom list is exactly
`Classical.choice`, `Quot.sound`, and `propext`. All three positive controls passed;
both omitted-zero-row and wrong-weight controls were rejected at proof goals.

A second, separate fresh `lake build` completed at
**2026-10-09T09:15:05.856729+00:00**; see
[evidence/v2/LAKE_BUILD.json](evidence/v2/LAKE_BUILD.json).
Both runs used a newly created own-build directory and the fixed source bytes.
They are distinct executions in the same WSL environment, not a claim of an
independent physical machine or external human review. No old v1 logs are
relabelled as verification of the new classification.

The evidence includes every build/control log, printed definitions and final
theorem, the complete replayed root and dependency lists, and SHA256 bindings
for source files, logs, toolchain binary and produced objects. Source hashes
were checked before and after the run. Compiled objects themselves are not
published, and cross-machine byte equality of object serialization is not
required for the theorem. The copied v1 sources are separately identified.
