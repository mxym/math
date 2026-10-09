# Pure qutrit ECQC counterexample — complete theorem sources

This package proves the original pure-state ECQC statement false using the actual normalized qutrit vector, its positive-semidefinite trace-one density matrix, both actual partial traces, four explicit complete MUB measurements, their actual Born tables, and actual spectral/Shannon entropies.

The two main exports in `ECQC.lean` are `ECQC.Qutrit.pure_qutrit_counterexample` and `ECQC.Qutrit.pure_prime_dimensional_ecqc_is_false`. The exact values are Q=2 log 2 and ECQC=3 log 2. The ECQC definition takes the infimum of all three-setting sums; the proof establishes its nonempty singleton value set and attainment.

All eight mathematical modules were compiled in the development directory in the current run. The two main exports report only propext, Classical.choice, and Quot.sound. A separate fresh-directory compilation and empty-kernel replay is in progress; this initial source commit does not claim that the fresh replay has finished. No sorry, admit, custom axioms, native_decide, or external quantum theorem is used.

The selected theorem is the complete explicit qutrit counterexample, not the whole prime-dimensional classification. Holevo, optimal ratios, qubit validity, ququint constructions, full-Schmidt-rank strengthening, and the all-prime analytic family remain outside this package.

See `PROOF_SUPPLEMENT.md` for the mathematical proof and definition interpretation, `FORMALIZATION_MAP.md` for correspondence to the paper, and `PROOF_SOURCES.json` for exact proof-source hashes and audit roots. Lean is fixed at 4.34.1 and Mathlib at d13f23b723b8a846827a245b89c10fc7d3f11612; the complete transitive pins are in lake-manifest.json.

Reproduction after preparing the pinned dependencies:

```sh
lake update
lake exe cache get
python3 reproduce.py
```

With an existing pinned dependency project:

```sh
python3 reproduce.py --dependency-project /path/to/pinned/project --lean /path/to/lean
```

The runner requires a genuinely new build directory, hashes every mathematical source, compiles every own module, audits the complete root dependency closure, and replays it from an empty Lean kernel at trust level zero. Its procedural checker is not an axiom of the mathematical endpoints. Cached third-party dependencies are reused; they are not claimed to have been rebuilt from source in this run.

Author: Yongxian Zhang (张永贤), School of Computer Science and Engineering, South China University of Technology. Email: mxymmxym1@gmail.com. ORCID: 0009-0000-3864-3536. AI-assisted; no external funding or external professional peer review. Separately authored original material is copyright 2026 Yongxian Zhang, all rights reserved; dependency and inherited-code licenses are preserved.
