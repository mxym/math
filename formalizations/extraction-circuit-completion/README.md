# Ancilla-free circuit completion — current formal scope

Status: **BUILD_ONLY**. Lean 4.34.1, Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
This is a new, independent scope. It does not extend or revise the frozen
608-root Connections audit or the older protocol/APPT audits. No fresh
empty-kernel replay or forged-proof controls have been run for this package.

## What is now proved

The primitive syntax contains only arbitrary one-qubit unitaries on an
existing wire and CNOT between two existing wires. Every circuit is a literal
finite list with matrix semantics and actual list-length gate count.

| Component | Actual checked endpoint |
|---|---|
| Original input convention | Explicit copywise base-m/n coordinates, actual recursive paired-copy `2k`-bit coordinates, normalized bit-occupation branching, density preservation, and the fixed relabeling of the old tensor convention |
| Elementary semantics | Single-wire action, CNOT bit action, chronological composition, inverse words |
| Ancilla-free Pauli synthesis | Parity compute/phase/uncompute; selected-string phase word of length at most `2^n (2n+1)` |
| Two-level synthesis | Actual Gray-path transpositions and arbitrary real plane rotations; `mergeWord_denote` equals the literal square-root Givens matrix, including zero masses |
| Raw compiler | `compileProgram_denote` and actual gate count at most `20 n^2 2^n` times the raw swap/Givens instruction count |
| Permutations | A recursively generated finite transposition program, at most `2^n` swaps, and its actual elementary synthesis |
| Occupation branching | Actual word-fiber cons/erase recurrence, normalized occupation-vector branching, and disjoint occupied predecessor labels |
| Common occupation step | `occupationStepCircuit_matrix`: one constructed word maps all actual normalized encoded branches to any prescribed next coordinate embedding; length at most `80 q^2 (2^q)^2` |
| Existing spectators | Full matrix equalities for both prefix and suffix embedding, respectively `U tensor I` and `I tensor U`; no zero-state premise |
| Integer activity width | Actual symmetric-projector rank, `clog 4` width, width increment, available original wires, and polynomial active dimension |
| Coherent successor expansion | Original occupation vectors after an explicitly stated previous-stage compression map expand into the correct normalized branches |
| Literal Bell preparation | Two original zero wires, actual H+CNOT word, and exact equality to the physical Bool Bell projector, including arbitrary existing spectators |
| Error | True Euclidean operator norm, literal-word telescoping, and actual complete PPT postprocessing fidelity at least `1-2 delta`, including removal of overall phase |

The occupation-step theorem does **not** take Schur blocks, branch
orthogonality, a target budget, or the desired extraction fidelity as an
unproved premise. Occupied labels, their disjointness and their masses are
derived inside the proof. Missing letters are omitted from sparse programs;
no dummy coordinate is inserted into a different occupation block.

`Budget.lean` proves an explicit arithmetic envelope

```
20480 k (k+2)^6 (6 clog_2(k+3)+2)^2 + 100 k^2.
```

This bounds the sum of the proved stage budgets. It is **not yet** a theorem
that a complete recursively assembled extraction circuit attains this budget.

## Exact remaining gap to the paper

`unknown-support.tex`, proposition `prop:pure-circuit`, and
`ADDENDUM_PURE_CIRCUIT-v3.md` are **not fully formalized** by this package.

1. Assemble the common one-step words into the all-k original `2k`-wire
   recursion, including explicit code padding by the already-present zero
   wires and the base case. Exact normalized word-to-bit coordinates, prefix
   and suffix gate embedding, and the coherent successor formula are available;
   their complete inductive composition remains to be written.
2. Construct the final actual wire redistribution, H/CNOT Bell preparation,
   and local readout from that recursively constructed code, linked to the
   original pure-input family and the exact optimal integer yield.
3. Bind the arithmetic budget to that complete word and prove the stated
   asymptotic complexity. The displayed arithmetic estimate alone does not
   establish existence of the whole word.
4. Prove an effective classical algorithm and its precision/bit complexity.
   `mergeAngle` is an explicit real `arg` expression, but several finite
   choices and real-valued gate definitions remain `noncomputable` in Lean;
   no efficiency theorem for evaluating them is claimed.
5. Prove or correctly import a complete finite-gate-set Solovay–Kitaev
   algorithm, including its base-net construction/calibration and precision
   bounds. No SK theorem is assumed as an axiom or inserted as a completed
   synthesis premise here. The per-gate telescoping theorem is a conditional
   stability lemma, not a proof that such a finite-library compiler exists.

The old `canonicalRelabel` is only a mathematical coordinate bridge. Its old
cardinality-chosen basis convention is not claimed to have an efficient
physical permutation implementation. The effective construction must use the
explicit copywise/bit coordinates throughout.

## Reproduction and evidence

Use the existing external pinned Mathlib cache; do not copy it or run an
update/cache download. Current WSL builds must first pass the D-storage guard
and use D-backed temporary/cache directories, as required by the workspace
storage policy.

```
python3 build_only.py --check-only
python3 build_only.py --build
```

The build command performs an ordinary Lake build and records printed root
types and axiom dependencies from `Check.lean`. It deliberately performs no
fresh empty-kernel audit. `SOURCE_SHA256.json` binds the owned inputs;
`ROOTS.txt` names the exact ordinary-build scope. An early metadata-helper
report rejected universe-suffixed names of the three permitted axioms; its
ordinary build and root printing had succeeded. That parser mismatch was
corrected, and the historical failed helper report is retained. Only the
latest source-matching BUILD_ONLY summary describes the current scope.
The parent Connections
workflow will decide the later independent audit scope.

The quantum compression mechanism and generic gate-synthesis methods are
prior work; see `SOURCE_REVIEW.md`. This package is an independently written
formalization attempt and does not claim a new discovery of compression or
of universal elementary gate synthesis.
