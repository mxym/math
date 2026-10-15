# Actual finite-dimensional common-subspace extraction core

This is a **new, separate Lean package** for a submission manuscript in preparation.
It uses Lean 4.34.1 and Mathlib commit
d13f23b723b8a846827a245b89c10fc7d3f11612.
It does not alter or enlarge any earlier 39/91/235/444 audit.

## End-to-end finite theorem

The principal lower theorem is
Extraction.finite_projection_fidelity_extractor.

For every integer input pair a,b, target K, and integer 0 < d <= K, let P be
an actual complex Hermitian idempotent on C^a tensor C^b. If

    rank(P) <= floor(a/d) floor(b/d),

then there exist **one global unitary on the original input** and **two complete
local finite Kraus families**, fixed before the input state, such that every
actual positive trace-one density matrix X with P X P = X has output target
overlap exactly d/K with the normalized maximally entangled K-by-K projector.

The d=K statement gives exact deterministic extraction. The output is a
normalized embedded Bell_d state, not a postselected branch.

The proof verifies all of the following internally:

* actual projection factorization by an orthonormal column matrix of exactly
  the matrix rank;
* integer floor dimensions and coordinate embeddings;
* extension between actual isometries by a unitary on the original space;
* explicitly completed local Kraus families on all unused coordinates;
* complete positivity on every finite auxiliary system, with an entrywise
  identification of the amplified original map;
* trace preservation on every complex matrix;
* a coherent coding identity for every logical matrix, including its
  off-diagonal entries;
* Bell normalization and the exact embedded overlap d/K.

Thus neither the desired packing inequality nor a fidelity bound is a hypothesis
of this theorem. The only capacity premise is the displayed actual integer rank
condition.

## Physical converse

Extraction.targetEffect_rains starts with a finite Kraus family A satisfying
sum A_j^* A_j = I and positivity of Gamma_out Lambda Gamma_in on every actual
positive input. This condition is weaker than complete PPT positivity, so is
a necessary property of a completely PPT channel. The proof derives positivity
of the actual Heisenberg dual by trace duality; it does not assume Rains effect
bounds for the caller.

It then proves, on the original product space:

    0 <= M <= I,   -I/K <= M^Gamma <= I/K,
    Tr(M^2) <= ab/K^2.

Extraction.kraus_target_overlap_unitary_le consequently proves, uniformly for
every initial global unitary U and every actual Hermitian Omega,

    Tr[Phi_K Lambda(U Omega U^*)]
      <= sqrt( Tr(Omega^2) ab / K^2 ).

Extraction.kraus_target_overlap_le_one supplies the unit upper bound for actual
density matrices. The intermediate projection-average theorem verifies the
special upper bound sqrt(ab/(K^2 Tr(P))) for any nonzero actual orthogonal
projection P.

The channel formulation here quantifies finite Kraus representations. Their
complete positivity and trace preservation are proved, rather than supplied as
an effect-level abstraction. The converse equivalence between arbitrary abstract
finite-dimensional completely positive linear maps and Kraus representations
is not a theorem of this package.

## Exact remaining boundaries

The following claims are **not** formalized by this package:

* the additional sharp local-dimensional upper bound a/K;
* Haar integration, orbit-ensemble averages, symmetric-power projectors, their
  binomial rank, or Schur--Weyl decomposition and dimensions;
* all-copy minimax asymptotics, capacity, large-deviation exponents, reliability,
  Gaussian thresholds, or universal mixed-state extraction;
* efficient circuit complexity, numerical optimality, or optimal finite
  packing sizes outside the explicit feasible integer condition.

The package can be used by an ordinary mathematical proof of these results,
but its finite matrix theorems must not be relabeled as a full Lean proof of
the manuscript's asymptotic or representation-theoretic statements.

## Verification and provenance

The density semantics and partial transpose are imported unchanged from
APPT.Quantum.Basic and APPT.Core in the pinned repository source.
The bilinear trace-pairing reindexing and positive-product argument reuse the
earlier repository's mathematical proof patterns; the reusable audit helper is
copied into a separate ExtractionVerification namespace. Original files are
unchanged.

ROOTS.txt lists the exact new audit roots. Check.lean prints the central theorem
types and their axioms. Audit.lean rebuilds their full dependency closure in an
empty trust-zero kernel, then tests same-type forged proofs in fresh empty
kernels. These controls alter only proof bodies, never theorem types.

Run from this directory:

    lake exe cache get
    python3 reproduce.py --check-only
    python3 reproduce.py --fresh

The fresh run rebuilds all new modules and the two imported APPT modules in this
checkout's own output directories. Pinned external dependency artifacts can be
cached; their proof closures are independently replayed in the empty kernel.
This is not a claim to recompile all Mathlib source from scratch.

All actual failed attempts remain under evidence/. The first kernel audit
attempt failed because an automatic root collector parsed the words
'theorem below' in a comment as a root name. The root list was corrected; no
mathematical source was changed for that correction.
