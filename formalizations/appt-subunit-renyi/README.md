# APPT subunit Rényi entropy: verified proof dependencies

The [complete mathematical research proof](../../research/appt-multilevel-counterexample/SUBUNIT_RENYI.md)
establishes, for each fixed 0<α<1 and uniformly in n≥m as m grows,

    mn [log(mn)−min_APPT S_α] ~ max{2α,1}+(α/2)max{4,n/m}.

The new spectral transition is α=1/2. This Lake package verifies the new
nonlinear half-order head bound on **actual sorted APPT eigenvalues**, and an
actual finite downward-spike density/APPT family with exact trace-square purity.
The complete arbitrary-order asymptotic theorem is not yet a Lean theorem.

## Actual verified endpoints

- `APPTSubunit.density_appt_paper_halfEntropyHead`: only local dimensions,
  actual complex density and all-unitary APPT are assumed; the exact lower-tail
  paper pivot, all signs, ordering and shifted-star budget are proved internally.
- `APPTSubunit.halfEntropyHead_le_two`: all finite head sizes, including the
  zero least-eigenvalue endpoint. Its core polynomial inequality covers an
  entire continuum with seven exact rational Bernstein identities.
- `APPTSubunit.negativeSpike_absolutelyPPT`: every positive contraction and
  actual complex unit vector, with all global unitaries and arbitrary complex
  test vectors. No Schmidt data, rank model or asymptotic positivity assumption.
- `APPTSubunit.exists_negative_rank_state`: for every actual rank k<mn and
  finite admissible parameter, constructs a density/APPT matrix with the
  exact original `trace(A*A).re` objective. Positivity, normalization and integer
  support cardinality are discharged.

The finite 3×12 control proves actual density/APPT/purity. Deleting the finite
hole reserve produces a true 2×2 density matrix that an exact APPT orbit rejects.
`decide +kernel` is used for finite support arithmetic; no `native_decide`,
`sorry`, `admit` or custom axioms are used in the proof modules.

## Versions, reproduction and audit

Lean 4.34.1 and Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 are fixed.
The two sibling APPT packages are explicit local dependencies. Clone the whole
repository so that those paths exist, then from this directory run:

```sh
lake exe cache get
python3 reproduce.py --check-only
python3 reproduce.py --fresh
```

The runner checks all local import sources and pinned manifests, rebuilds all
eight own modules in a newly emptied own build directory, and replays the entire
selected proof closure in a new Lean kernel at trust level zero. It verifies
that only `propext`, `Classical.choice`, and `Quot.sound` occur as axioms, and
rejects six unchanged-type forged proofs. `SOURCE_HASHES.json`, `ROOTS.txt` and
`verification/reproduction/` bind the actual sources and logs. Retaining
unchanged dependency caches is explicit; no old logs count as a new verification.

This package uses [the prior physical APPT review](../appt-high-dimensional-review/README.md)
and [qutrit quantum foundations](../appt-qutrit-purity/README.md). Their existing
licenses and notices apply to their original files. No published immutable
archive is modified. New original files: copyright 2026 Yongxian Zhang, all
rights reserved. AI assistance: OpenAI AI assistants; no external funding.

**This checkpoint passed a fresh isolated build and trust-zero replay on 13 October 2026:** 8 own modules, 39 theorem roots, 35,882 transitive declarations, 91 bound local inputs, only the three standard axioms, and all six unchanged-type corruption controls rejected. The exact rational certificate also passed with and without Python assertions enabled. See `verification/reproduction/SUMMARY.json`. This is the actual run for these sources.

## Remaining boundary

The real-power comparisons for arbitrary α, the entire entropy objective and
centering/limit passage, the negative high-hierarchy physical construction, and
companion flat-family dependencies remain ordinary mathematical inputs to the
research proof. They are explicitly disclosed, not recorded as kernel-verified
by this package. Neither finite checks nor the kernel audit constitute external
peer review or establish historical priority. Exact finite minima, transition
rigidity, fixed-local subunit equivalents and absolute separability remain
separate directions.
