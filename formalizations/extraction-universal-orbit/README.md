# Actual polynomial orbit spaces for universal extraction

Lean 4.34.1; pinned Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.

This new package verifies actual tensor-coordinate foundations for the standard
universal-compression orbit-span method. That compression mechanism is prior work
(Jozsa et al., *Universal quantum information compression*, 1998), credited in the
submission manuscript. This is not a new discovery of universal compression.

For every actual complex D-by-D matrix M and original tensor vector v,
`tensorAction M v` lies in a fixed space of dimension at most
`choose(D*D+k-1,k)`. The proof realizes matrix tensor powers as contractions of
actual symmetric tensor powers of the D² matrix entries, whose projector and rank
are proved in the separate symmetric-support package.

For every known finite set S of computational words, one fixed `universalSpace S`
contains every matrix tensor orbit of every basis word in S. The spaces are
nested with S and have dimension at most `card S * choose(D*D+k-1,k)`.

`exists_subspace_projection` constructs an actual Hermitian idempotent of exactly
the finrank of any submodule of the original complex coordinate space. It fixes
every vector in that submodule. Its proof uses the internal Gram matrix of a
basis; invertibility, Hermiticity, idempotence, range and rank are derived.
`universalSpace_actual_projection` combines that construction with the actual
orbit-space rank bound. No rank, spanning or performance certificate is assumed
for the caller.

The projector is also proved invariant under every one-copy matrix tensor
power, nested under inclusion of word sets, and positive semidefinite. Its actual
trace pairing with every iid density dominates the selected classical word mass
of that density's eigenvalue law. The downstream minimax-profile package combines
these facts with proved type counts and actual product-local extraction channels
to obtain fixed-dimension subcritical and Gaussian limits. This does not identify
the manuscript's particular Schur blocks or its sharper finite-block constants.

The separate extraction-connections scope binds and reviews these additions.
The existing 39/91/235/444 and 83/11 root scopes remain unchanged.
