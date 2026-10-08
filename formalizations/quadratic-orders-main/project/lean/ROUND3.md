# Round 3: literal finite sieve closed; all-order main theorem conditional

The two unconditional compiled and fully audited endpoints are:

```lean
Entry002.finiteSieveTarget_proved : Entry002.FiniteSieveTarget
Entry002.finiteSieveNoWalkTarget_proved : Entry002.FiniteSieveNoWalkTarget
```

These are the unchanged universal A1–A5 theorem and its one-finite-pool-before-
all-walks formulation. The actual periodic component conclusion is Q².
The final types have no batch certificate, information-rate, entropy, coverage,
error bound, or target-result premise. Actual arbitrary-lattice windows, one
literal common time law, nested selected-prime families and honest logarithmic
budgets are derived inside the proof. No Gaussian theorem or finite v4
classification replaces the universal result.

The isolated arithmetic project proves the following two conditional endpoints:

```lean
Entry002.arithmeticSupply_principalSupply_of_primeIdealPNT
  (hPrimeIdeal : ∀ (N : Type) [Field N] [NumberField N],
    Tendsto (fun x : ℝ =>
      ((nonzeroPrimeIdealsUpTo N ⌊x⌋₊).card : ℝ) / (x / Real.log x))
      atTop (nhds 1)) : Entry002.PrincipalSplitPrimeSupplyTarget

Entry002.arithmeticSupply_mainTarget_of_primeIdealPNT
  (hPrimeIdeal : ∀ (N : Type) [Field N] [NumberField N],
    Tendsto (fun x : ℝ =>
      ((nonzeroPrimeIdealsUpTo N ⌊x⌋₊).card : ℝ) / (x / Real.log x))
      atTop (nhds 1)) : Entry002.MainTarget
```

The count is the genuine bounded-norm nonzero prime-ideal count. Actual arbitrary
ray moduli, local-to-global 1 mod f congruence, conductor-order generators,
nonidentity quadratic conjugation, distinct unramified degree-one kernels,
normal-closure splitting descent, finite exclusions and natural dyadic density
are discharged in these conditional proofs. The analytic premise remains OPEN;
therefore unconditional MainTarget and PrincipalSplitPrimeSupplyTarget remain
OPEN. Their complete compiler types are preserved in the isolated audit logs.
Every quadratic field, positive conductor, integral basis, full planar linear
isomorphism and nonnegative step bound remains quantified.

## Fresh main verification

`bash scripts/verify.sh` exited 0 after removing only this isolated project's
owned build output. The fresh build completed 4153 jobs. The owned project has
80 substantive modules plus one umbrella, or 81 compilation units.

Every safe stored logical root was audited, including private generated proofs:
2248 roots = 1918 theorem roots + 330 definition roots, in an inventory of
2284 declarations. These are compiler declaration counts, not independent
mathematical theorem counts. Only `propext`, `Classical.choice`, and `Quot.sound`
occur; there are no unsafe, partial or missing proof dependencies. Exactly the
two previously documented TimeLaw generated data definitions have cached
axiom metadata differences. Their complete actual closure is still checked;
every other root retains strict stored-closure/collectAxioms agreement.

The closed finite-sieve endpoint traverses 52086 constants; its no-walk
corollary traverses 52087. The conditional main assembly in the main library
traverses 60284. Separately, the isolated conditional supply and Main endpoints
traverse 117960 and 121903 constants, respectively, with strict axiom agreement.
All seven new conditional/cutoff/helper roots pass. The earlier conductor
workload covers 246 actual stored roots; the original external workloads have
16, six and three specified roots. These separate workloads can overlap and
must not be added as independent mathematical theorems.

Proof reuse verification passes 48 exact licensed bodies/spans and 21 distinctly
recorded adaptations. Source maps, real compiler types, exact root inventories,
source hashes and unedited build/audit logs are included. Official Lean/stdlib
and exact official package artifacts are trusted. No full mathlib rebuild or
second kernel is claimed. A written-proof verdict is not kernel proof evidence.

## Verification provenance and isolation

The immutable round2 archive SHA256 is
0f0ca876bbeb77839fd94bcb01a418701781ce36d7afb9cd0e9dac9d048f84f3.
It was extracted into this fresh workspace. Round2 source/evidence is not
overwritten. Reused compiler tools are read-only; owned sources and build
outputs are isolated. Copied historical logs are distinguished in
logs/verification-commands.txt. The three literal target source files remain
byte-identical, recorded in logs/round3-literal-target-preservation.json.

The external verifier now enforces exact named root sets, all 82 owned proof
module names and all 19 configuration/auditor/evidence paths. It rejects
duplicates and missing ledger rows. Complete bridge/auditor source hashes,
136 authenticated Git commit/tree objects and exact patch replay authenticate
all 999 imported external source paths (original bytes or original absence)
and their resulting bytes. Among
these, 76 source files are changed by the exact patch, including 48 new files.
This authenticates content at the pinned commit, not an author's signature.
All 15 production negative controls reject deletion/substitution of roots,
omitted owned/control ledger rows, a missing source and an altered patch;
stable proof files are never mutated. Final selected-build/recursive-audit
results are recorded in the isolated project's final logs. These provenance
checks are distinct from mathematical progress.

The hardened portable verifier exits 0. Afterwards, only the six isolated
owned module outputs were removed and freshly rebuilt successfully. Five
`.olean` objects are byte-identical; RayBridge differs from the inherited
object. The exact conditional seven, Ray 16 and conductor 246 workloads were
therefore rerun against the fresh objects and all pass. Final object hashes
bind the delivered evidence to the clean-build outputs. See
logs/arithmetic-isolated-postfresh-verification.log and
logs/round3-external-audit-summary.json. The 995 external class-field module
cache and official mathlib caches are retained; their exact sources and pins
are rechecked. No full fresh round3 CFT or mathlib rebuild is claimed.

The parent separately reported an independent round2 rebuild and strong
stored-body closure audit. Its scope and supplied archive hash are recorded
in logs/parent-round2-independent-review-note.json, explicitly as a received
report rather than work executed here. It did not perform an empty-kernel
replay or independently rebuild external CFT/PNT. It is not an independent
round3 audit. Its cold probe also found cached undercount on the TimeLaw
inductive declaration itself. That declaration is outside the safe
theorem/definition root set; it remains traversed through the constructor
closure. The two exceptions described above concern safe definition roots.

Lean remains 4.34.1 and official mathlib remains
d13f23b723b8a846827a245b89c10fc7d3f11612. No GitHub push/publication occurred.
The unrelated mounted repository was neither inspected nor modified.
