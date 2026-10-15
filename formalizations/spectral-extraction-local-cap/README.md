# Actual local-dimension cap and complete finite envelope

A new audit scope on top of the frozen spectral-extraction-core package at
131aedf3b7329a94d3e9a52e25af8268cb7bd26e. The earlier 83-root audit, its source
bindings, its configuration, and all 39/91/235/444 audit source scopes remain
unchanged.

## Verified conclusion

For every actual trace-preserving finite complex Kraus channel with positive
partial-transpose conjugate, every actual input density rho on a-by-b, every
initial global unitary U, and normalized Bell output target of dimension K,

    Tr[Phi_K Lambda(U rho U*)]
       <= min { 1, a/K, sqrt(ab Tr(rho^2))/K }.

The final Lean declaration is

    ExtractionLocalCap.kraus_target_overlap_full_envelope

The physical assumptions are the actual Kraus completeness identity and
positivity of Gamma_out Lambda Gamma_in on every actual positive input matrix.
Every completely PPT Kraus channel satisfies the latter necessary condition.
The conclusion is therefore valid for this larger class; no effect-level
local cap is supplied as a hypothesis.

The key stronger matrix theorem is

    ExtractionLocalCap.local_order_cap

It proves that an actual Hermitian M satisfying -cI <= M^Gamma <= cI obeys
(ca)I-M positive semidefinite, for every nonnegative real c. This uses the
original coordinate partial transpose. The input index has a linear order
solely to index the existing signed Schmidt decomposition; all physical
integer dimensions use Fin and are covered.

## Proof mechanism

LocalCap/Compression.lean preserves the real interval [-cI,cI] under every
actual contraction and bounds its actual compressed diagonal pairing against
the full absolute mass of any signed real diagonal.

LocalCap/SchmidtBudget.lean obtains Schmidt data internally for every original
complex test vector, including zero and all rank deficiencies. It proves

    sum |SchmidtSigned(s)| = (sum s)^2 <= a sum s^2.

LocalCap/ActualCap.lean transfers that pure-state partial-transpose trace bound
back to all original quadratic forms, proves the PSD local cap, then connects
actual Rains effects, physical channels, density states, and all initial
global unitaries. The already verified unit and purity bounds are combined
without modifying their earlier source or audit.

## Verification

Pinned Lean 4.34.1 and Mathlib
d13f23b723b8a846827a245b89c10fc7d3f11612.

Run:

    lake exe cache get
    python3 reproduce.py --check-only
    python3 reproduce.py --fresh

The new audit selects exactly 11 roots and checks six proof-body forgeries
while keeping their theorem types unchanged. Check.lean prints all theorem
types and axioms. The dependency closure is replayed in an empty trust-zero
kernel. Mathematical sources contain no new axioms, admitted proofs, native
decisions, or unsafe definitions.

The fresh run rebuilds new modules and all imported repository modules in this
independent checkout's own output directories. Cached pinned external
dependency artifacts are permitted, and their relevant proof closures are
kernel-replayed. It does not claim a full Mathlib source recompilation.

Haar/symmetric-power identities, the symmetric rank, Schur--Weyl theory,
protocol asymptotics, circuit costs, and the abstract CP-map/Kraus representation
equivalence are outside this new finite matrix scope.
