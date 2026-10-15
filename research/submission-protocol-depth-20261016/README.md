# Finite-block universal extraction and the cost of an unknown support

Author continuation of the explicitly globally preprocessed extraction model, based on commit `44d096fe63e4b1ef9462a338b941a11ed931b790`. The main research tree and prior formal audits were not edited by this work.

Current mathematical sources:

- [PAPER-v4.md](PAPER-v4.md): all-finite-k coherent Schur packing; explicit dimension-dependent information-spectrum bounds and quantitative Gaussian/triangular-array consequences; general common-support/average-state minimax principle; rank-s support and Haar collision asymptotics; exact classical support-rank polynomials; sharp all-target minimax laws, zero-error and fixed-error logarithmic costs; compatibility of an all-state family with the pure-input sharp law.
- [ADDENDUM_FIXED_SPECTRUM-v2.md](ADDENDUM_FIXED_SPECTRUM-v2.md): the same sharp minimax law already holds with the flat spectrum fully known and only its support unknown; every known positive rank-s spectrum has the same zero-error law. A larger faithful capacity for nonuniform spectra is strictly asserted only in the entropy-limited regime.
- [ADDENDUM_PURE_CIRCUIT-v3.md](ADDENDUM_PURE_CIRCUIT-v3.md): unknown pure two-qubit inputs, original 2k qubits, optimal integer Bell-pair target at every k, and a genuine polynomial circuit with no supplied pre-unitary ancilla. Continuous gates give exact extraction; computable inverse-closed discrete libraries give approximation up to irrelevant global phase.

The general mixed-state construction is not claimed to be efficiently implemented. The rank-budget minimax protocols may know the supplied rank ceiling; they are not silently substituted for the single all-state family. Every result retains the free global entangling unitary as an explicit resource. These results do not solve ordinary LOCC mixed-state distillation.

The new ordinary mathematics and scope corrections have been read by a separate internal AI reviewer. This is not external human peer review. The final combined journal manuscript requires its own frozen-source read. The underlying symmetric compression, representation identities, Gessel/RSK counting, Rains converse, Berry--Esseen and Solovay--Kitaev inputs are credited. No exhaustive priority certification is asserted.

A separate sibling task formalizes the actual finite-dimensional packing and cPPT effect core. The Schur/Haar identification, asymptotics, probability limits and circuit-complexity results here do not carry complete Lean certification. Old Lean audit scopes were not expanded.

## Reproduce

Run from this directory with Python 3 and its standard library:

```sh
python3 verify_sources.py
python3 check.py --report verification/exact-checks.json
python3 -O check.py --report verification/exact-checks-optimized.json
python3 check_rank_polynomial.py
python3 check_pure_circuit.py
python3 verify_sources.py
```

The exact controls include 240 independent Weyl/hook/support cases, 596 actual Kraus dyads, 46 tensor-power/Schur-spectrum cases including zeros, and 240 exact Toeplitz-polynomial comparisons. Pure-circuit controls check 58,904 occupation branch vectors and 1,364 Pauli-projector phase identities with exact arithmetic, plus actual small complex-vector compression simulations explicitly marked as floating diagnostics. These finite controls do not certify the unbounded proofs. False Weyl ratios, omitted unknown-support costs, wrong Haar spectra, false finite flatness, integer-free packing, wrong fidelities and wrong branch amplitudes are rejected.

All earlier draft bytes are preserved. `SOURCE_HASHES.json` binds both these sources and the exact predecessor inputs. `verification/literature-check.json` records primary read scope and retrieval fingerprints, without redistributing third-party article files. No external submission, message, Release or DOI was created.
