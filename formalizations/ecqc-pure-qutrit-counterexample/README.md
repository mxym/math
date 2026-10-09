# Complete Lean proof: the pure qutrit ECQC counterexample

**Verified scope:** the actual explicit pure qutrit counterexample to the original ECQC inequality. The proof starts from a normalized complex bipartite vector, its positive-semidefinite trace-one density matrix and actual partial traces, and four explicit complete MUB measurement bases. It derives actual spectral and Shannon entropies from actual Born probabilities. It proves the original minimum over every three-setting subset, not a selected-subset score.

**Main entries:** `ECQC.Qutrit.pure_qutrit_counterexample`, `ECQC.Qutrit.exists_pure_qutrit_counterexample`, and `ECQC.Qutrit.pure_prime_dimensional_ecqc_is_false`, in `ECQC.lean`.

The exact values are Q(ρ)=2 log 2 and ECQC(ρ)=3 log 2. The full retained-value set is proved to be the nonempty singleton {3 log 2}, and the minimum is attained. Thus the universal pure-state ECQC claim is false already at prime dimension three.

## Current verification record

The fresh run in `evidence/v1/VERIFICATION.json` recompiles **all eight mathematical modules** in a genuinely new directory, then replays the full dependency closure of **73 roots** (definitions and theorems) into an **empty kernel with trust level zero**. The closure contains **35,401 declarations**. It permits exactly the standard logical axioms `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, `admit`, custom axiom, `native_decide`, external quantum theorem, or unproved entropy/Born bridge occurs in the proof.

This record was produced from the present proof-source hashes in the current run, not copied from another project's log. `PROOF_SOURCES.json` records all mathematical sources, pins, replay code, runner, and selected roots. The evidence directory contains the individual compilation logs, full replayed closure, root list, axiom list, source/compiled-object/log hashes, actual Lean executable hash, actual dependency revisions, and UTC timestamps. The replay runs in a separate empty kernel using the same fixed Lean implementation; it is not an independently implemented proof assistant. Cached third-party dependencies are reused, not claimed to have been rebuilt from source.

## Fixed environment and reproduction

Lean: **4.34.1**, commit `5045d0056413266e57c625dcd7c365b10e377c52`.

Mathlib: **`d13f23b723b8a846827a245b89c10fc7d3f11612`**. All nine Git dependency revisions are fixed in `lake-manifest.json`. Keep that manifest; do not update it to floating revisions.

From this directory, with Elan installed:

```sh
lake exe cache get Mathlib.Analysis.Matrix.PosDef Mathlib.Analysis.SpecialFunctions.Log.Basic Mathlib.Tactic
lake build
python3 reproduce.py
```

Lake uses the checked-in manifest to materialize the pinned dependencies. The reproduction runner creates a new empty build directory and checks the actual Lean version, dependency commit IDs, and every proof-source hash before recompilation. It rejects a pre-existing directory passed through `--work-dir` and verifies the hashes again afterward. Only mathematical proof dependencies may contain the three permitted logical axioms; procedural replay code is not an axiom of any endpoint.

With an already prepared matching dependency project:

```sh
python3 reproduce.py \
  --dependency-project /path/to/pinned/project \
  --lean /path/to/lean-4.34.1/bin/lean \
  --work-dir /path/to/new-empty-build-directory
```

An additional clean `lake build` of the complete Lake library is recorded separately in `evidence/v1/LAKE_BUILD.json` and `clean-lake-build.log`.

## Mathematics and exact limits

`PROOF_SUPPLEMENT.md` explains every quantum definition and the full proof. `FORMALIZATION_MAP.md` gives the paper → mathematical lemma → Lean endpoint correspondence. The source paper is `research/ecqc-pure-state-counterexamples/paper.tex`, especially the explicit qutrit construction; the supplemental `QUTRIT_EXACT.md` describes the same witness.

A reusable spectral lemma proves S(A)=-log a whenever a Hermitian trace-one matrix satisfies A²=aA, using Mathlib's actual eigenvalues and eigenvectors. A second reusable lemma proves the pure-density Born expectation equals the squared modulus of the actual amplitude. These close the core mathematical bridges; the witness does not use Holevo as an assumed input.

The **entire prime-dimensional classification is not claimed to be Lean-complete**. Holevo's bound, the two-dimensional positive theorem, optimality of the 3/2 ratio, five-dimensional constructions, full-Schmidt-rank strengthening, and the all-prime analytic family are outside this certificate. This proof formalizes an existing explicit witness; it is not a new-priority or external-peer-review claim.

## Authorship, assistance, and rights

Yongxian Zhang (张永贤), School of Computer Science and Engineering, South China University of Technology. Email: mxymmxym1@gmail.com. ORCID: 0009-0000-3864-3536. AI-assisted research, implementation, documentation, and self-audit; no external funding or external professional peer review.

Separately authored original material is copyright 2026 Yongxian Zhang, all rights reserved. Mathlib, other dependencies, and inherited material retain their licenses. The replay driver and reproduction runner are adapted from the repository's earlier verification packages. Existing immutable releases and third-party notices are unchanged.
