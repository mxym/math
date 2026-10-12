# Proof, source, and derivative map

## Mathematical map

- paper.md Section 1 / Theorem 1: rank-one closed-walk-voltage completion and
  CRT slabs, from the completed rank-one note, with full proof retained and
  the equality between edge-generated and closed-walk voltage subgroups made
  explicit. The actual integral subgroup generator is required.
- Section 1, arithmetic supply: the order-level ray class/Chebotarev argument
  from the arithmetic progress note and independent audit, written out here
  with norm, index, residue-kernel equality and nonmaximal-order hypotheses.
- Sections 2-3: cubic multiplication/norm arithmetic, three principal kernels,
  index-30 product ideal, full eight-state F6 quotient, exact lift sections,
  and structural zigzag proof.
- Section 4 / Proposition 2: impossibility of any single additional proper
  principal ideal on the fixed two-ideal F8chain gate, and the exact nonzero-
  period obstruction walk for the three-ideal sieve. This is an avoiding-walk
  witness, not an irreducible-walk witness.
- Section 5: norm-11 kernel, two-prime CRT slabs, index-330 product ideal, and
  the complete 80-state / 216-directed-edge zero-voltage F8chain certificate.
- Section 6 / Theorem 3 and Corollary 4: the second frozen revision's stronger
  k^2 * 2^{16(r+1)} associate-class interface and improved restored bounds.
  The independent audit supplies the finite-index proof that every order's
  unit rank is r_1+r_2-1.
- Section 7 / Theorem 5, Lemma 6 and Theorem 7: bounded-norm intersection and
  arbitrary-order restoration from the arithmetic progress note. The counting
  proof keeps the correct distance D(B+1), counts finite paths without assuming
  finite original components, and treats empty steps/generators separately.
- Sections 8-9, README.md and AUDIT.md: scope and reproducibility boundaries from
  the independent audit and its caveats. The unrelated geometry/entropy material
  in the progress note is outside this supplement's audit verdict and is not
  silently imported.

## Imported primary arithmetic inputs

1. F. Beukers and H. P. Schlickewei, *The equation x+y=1 in finitely generated
   groups*, Theorem 1.1 and Section 3. The theorem applies to the Q-closure of
   a finitely generated subgroup of (C*)^2 of torsion-free rank R and gives
   at most 2^{8R+8} solutions. The subgroup itself is contained in that closure.
   [Authors' full paper](https://www.researchgate.net/profile/F-Beukers/publication/27708784_The_equation_xy1_in_finitely_generated_groups/links/53e731ea0cf25d674ea587e4/The-equation-x-y1-in-finitely-generated-groups.pdf)
2. J. S. Milne, *Algebraic Number Theory*, version 3.08 (2020), Proposition 4.2
   (ideal norms), Theorem 5.1 (unit rank), and Theorem 5.11 (S-unit rank).
   [Official notes](https://www.jmilne.org/math/CourseNotes/ANT.pdf)
3. J. S. Milne, *Class Field Theory*, Chapter V, Theorem 3.6 (ray-class existence
   and Artin isomorphism) and Theorem 3.23 (Chebotarev). Applied in the normal
   closure over Q, these imply the stated supply of principal norm-prime ideals
   in every order.
   [Official notes](https://www.jmilne.org/math/CourseNotes/CFT.pdf)

These deep inputs are explicitly imported; their proofs are not claimed in this
supplement. The graph, normalization, lattice-index and restoration arguments
are supplied here. The quoted numerical bounds and named theorem scopes were
checked against the primary papers/official notes on 7 October 2026.

## Frozen scientific provenance

SOURCE_HASHES.json records byte lengths and SHA-256 hashes of the two separately
frozen completed-note revisions, the arithmetic progress note, the rigorous
independent audit, its caveats, unchanged certificates, original verifiers, and
the frozen independent output. The first completed-note revision has hash
36dc640f748c128100d0aa8565cc45f1785c7499b3a6ba6a9547474c1889ae88; the second,
which adds the stronger associate-class interface, has hash
a2b56e3cecba94c932367fd47bc57ae19984a6df90c54bda63a3d10dee226bc9.
The first was not overwritten. Both certificates and author verifiers are
unchanged across that revision. This public paper is an editorially self-contained
derivative, rather than a byte-identical republication of either manuscript.

The original manuscripts and audit records contain research-environment context
that is not part of the public proof. They are identified by hash rather than
bundled. The certificates and verifier originals are included verbatim.

## Exact checker changes

The following unified diff files are complete and mechanically checked:

- verification/check_cubic_certificate.py.patch
- verification/check_rank_one_f8_certificate.py.patch
- verification/independent_check.py.patch

In the F6 public derivative, the docstring identifies it as author-derived;
exact_integer_metadata checks the certificate object, exact-integer lists,
modulus, component IDs and statistics; metadata_negative_cases adds ten targeted
controls; verify calls the validator; negative_tests adds those ten controls.
No arithmetic, quotient reconstruction, membership test or edge identity is
changed.

In the F8chain public derivative, the docstring likewise identifies its origin;
the shared strict-metadata validator and controls are imported from the F6
derivative and invoked. No arithmetic or graph code is changed.

The independent checker changes exactly one lookup line:

    path = HERE/'frozen'/name

becomes:

    path = HERE/name

Its proof checks and controls are unchanged. The resulting output is
byte-identical to the frozen independent result. The label frozen_sha256 remains
to make the frozen certificate provenance explicit.

The original verifiers in original-verifiers/ have their exact audited bytes.
They are archival sources. Run the public-root checkers for strict interchange;
the reproduction script runs the historical schema controls on isolated copies
without changing the archival originals or supplying misleading results.

## Public integrity boundary

MANIFEST.json and SHA256SUMS cover the exact whitelisted public files. They
are checked before any mathematical rerun or deterministic archive creation.
Their scope is this supplement alone: no result here certifies a broader
catalog, other step sets, new manuscript revisions, or unreviewed artifacts.
