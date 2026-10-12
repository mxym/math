# Exact remaining proof obligations — partial formalization

The full target is the Jacobian of the ACTUAL characteristic/cofactor coefficient
map of every finite bidirected tree with one leak, together with its exact
factor multiplicities and complete positive realization/fiber classification.
No missing main conclusion is supplied as an axiom or a hidden premise.

## Completed mathematical components

The actual conservative matrix, Bochner-free finite state/rate definitions,
characteristic/cofactor encoding, root resolvent, rate-coordinate Jacobian,
child partition, genuine smaller child models, independent rate permutations,
all-child characteristic/cofactor recursions, and actual local cancellation
and all-tree sibling-common-root classification are proved.

For every endpoint path length, the canonical all-rate Jacobian formula,
zero-boundary singular locus, and global real-rate coefficient uniqueness at
regular reference points are proved. For a noncancelling reference path, actual
nonpole root-resolvent equality also identifies every competing real rate vector.

For arbitrary finite child families, all numerator scaling, polynomial gluing,
root update and actual Frechet chain-rule factors are now combined in
`branchStep_actual_jacobian`, including zero scales and common roots.

For positive physical tree rates, detailed balance and grounded positive energy
are constructed, exact diagonal symmetrization and strict negative-real spectrum
are proved, and both actual characteristic and cofactor polynomials receive a
finite normalized Stieltjes representation. Full distinct positive-weight modes
are equivalent to the absence of actual sibling spectral collisions anywhere
in the tree; this is not yet claimed as a Jacobian or ODE-observability equivalence.

Global all-tree uniqueness per prescribed recursive assignment of actual subtree
characteristic polynomials is proved for nonzero-edge, coprime-sibling references.
For positive full-mode references these conditions are derived from the spectrum.
The competing rate vector needs no positivity, regularity or minimality premise.

## 1. Arbitrary branching-tree coefficient-Jacobian induction

Still join the now-proved full local coefficient transformation with the
independent physical child coefficient maps and root-coupling map across the
whole tree. Complete the global Frechet chain rule, coordinate orientations,
and induction identifying the exact actual standard-coordinate Jacobian with

    ± product_v f_v^(n_v-1) a_v^n_v
      * product_(sibling pairs at every node) Res(P_v,P_w)^2.

Do not substitute the already proved physical rate-to-matrix coordinate
Jacobian for this different coefficient-map Jacobian. The endpoint path case
is complete; arbitrary branching is not. Original observation-root versus
leak-root changes and arbitrary external graph reindexing also need their
explicit transport statements.

## 2. Exact multiplicities and full singular-locus equivalences

After the full branching factorization, show that sibling resultants contain
no additional individual-rate factors, and derive the exact tree edge
multiplicities in the manuscript's parameter convention. Derive the global
resultant identity relating the actual characteristic/root-cofactor pair to
the actual coefficient Jacobian and the claimed positive singular-locus
equivalences. The common-root and full-mode classification is complete but
must not be relabelled as the unproved Jacobian equivalence.

## 3. Positive realization existence and exhaustive fiber count

Uniqueness for each prescribed recursive factor assignment is now proved.
Remaining: Stieltjes reciprocal pole/zero interlacing and positive residues;
construct a positive physical model for every admissible recursive partition;
prove that all positive realizations arise from those assignments; prove the
exact factorial count and any claimed global branch/component topology.

The fixed-assignment uniqueness theorem is not an assertion that every
assignment exists, nor that one can identify a tree's rates from the root
response alone. Different assignments may still yield different realizations.

## 4. ODE/system interpretation beyond the algebraic resolvent

Any claim phrased as controllability, observability or all-input equality of
ODE solutions still needs its corresponding actual state-space/ODE definitions
and bridge. The proved resolvent and characteristic identities are not silently
presented as an unproved dynamic-system equivalence.

Every completed checkpoint has its own source-bound clean build, axiom audit,
empty trust-zero replay and deliberately false mutation checks. Old receipts
certify only their own source bytes. No complete-formalization Release or DOI
is justified until the remaining main theorems close.
