# Preserve enumerated triples through the actual compiler

This followup only adds new modules. All earlier sealed sources and metadata are
unchanged. It improves the actual evaluation path rather than adding a supplied
fee field or computing an extra tally solely for an annotation.

`carriedOccupationTable` executes `triplesBuild` once and constructs the same
literal occupations while retaining their original triples in the actual table
records. The proof field relating the literal to the triple is erased.

`carriedTripleRankProgram` directly executes the constructive rank table and
triple-index scan on an already stored triple. No count, quotient traversal, or
occupation construction occurs in this rank program. Its complete returned
`ConstructiveRankRun` equals the preceding rank program for the same occupation.

For branch endpoints, `erasedTriple` subtracts one from the stored coordinate
for letters 0,1,2 and leaves the triple unchanged for letter 3. An internal
`count_erase` proof establishes that this is precisely the erased occupation's
triple. The child occupation erase appears only in the correctness proof/type,
not as runtime input to the new endpoint program. Next-stage endpoints read the
same original stored triple directly. `carriedMass` reads the three stored
coordinates or `k-total triple`, proved equal to the old multiset count.

Each branch preserves the entire preceding returned word/annotation record.
The packed swap-stack alignment traverses the carried record table directly,
and its entire record equals the preceding alignment over the occupations.
The new stage, compression, descriptor and final `carriedRankExtractionRun`
therefore preserve the entire returned record. The finite-label word is exactly
the preceding compiled word, with the same all-input fidelity theorem.

The real returned rank-work annotations keep the established bounds
`168*k*(k+2)^6`, `6*k*(k+2)^6`, `18*k*(k+2)^6` for construction events, filter
predicate requests and coordinate Nat-equality requests. This change removes
the need to charge a new `toTriple`/count traversal for each rank input.

Explicit remaining boundary: occupied-letter subtype enumeration, its membership
checks and pivot selection still use the literal occupation API. The literal
occupation table is still constructed; carrying the triple does not erase its
construction cost. Other record/map/traversal work, finite coordinate dispatch,
Nat arithmetic/comparison/bit fees, packed vectors and their equality, Gray/swap
and word-list compilation, counter maintenance, library-provider computation,
serialization and other execution costs remain outside these annotations.
No total primitive-cost or Turing-time conclusion is made.

Validation: all four new mathematical modules plus every new theorem/model root
pass the authorized single-owned-module checker. This is OWNED-only evidence
pending standard aggregate and independent replay while the independent audit
holds the global lock. Exact roots and source/log hashes are recorded separately.
