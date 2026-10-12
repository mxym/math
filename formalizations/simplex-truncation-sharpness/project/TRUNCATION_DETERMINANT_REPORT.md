# Exact facet determinants and scalar cancellation

The two new mathematical modules prove the dimension-independent determinant
calculation required by the actual simplex truncation. They contain 17 public
theorem declarations. Both mathematical sources are frozen after successful
zero-warning compilation with Lean 4.34.1 and the pinned project dependencies.
They do not modify the previously certified finite-pyramid/B source bundle.

## Literal algebraic coverage

`Entry005.TruncationFacetDeterminants` uses genuine real matrix determinants.
The packed generator order is top, bottom, followed by all coordinate facets.
Its horizontal vectors are

    c*1, -c*q*1, -c*r*e_i.

Its lifted vectors use height-first coordinates:

    (c,c*1), (-c*s,-c*q*1), (0,-c*r*e_i).

`truncationPackedTupleSum` sums absolute determinants over every ordered tuple,
including repeated-index tuples. Repeated-index terms vanish by an actual
column-equality theorem before the sum is converted to an embedding sum.
No unordered-volume normalization is supplied as a hypothesis.

For every integer d>=2 and c,r,q>=0,
`truncation_packed_horizontal_tuple_sum` proves

    H_tuple = d! c^d [r^d + d(1+q)r^(d-1)].

For every integer d>=1, c,r,s>=0, and s<=q,
`truncation_packed_lifted_tuple_sum` proves

    L_tuple = (d+1)! c^(d+1)
              [r^d(1+s)+d r^(d-1)(q-s)].

The proof expands the alternating embedding sum twice, for the two genuine
special generators. Completing a partial coordinate embedding to a
permutation and replacing its missing row by the sum of all coordinate rows
proves that every relevant ones/coordinate minor has absolute determinant
one. In the lifted two-special minor, adding q times the top row to the
bottom row leaves `(q-s,0)`. Swapping those two rows and expanding the
determinant proves the exact remaining minor. All dimensions and embedding
cardinalities are proved symbolically; there is no fixed-dimension enumeration
or trusted numerical evaluation.

`Entry005.TruncationScalarCancellation` defines the two scalar ordered sums
with c=1/(d-1)!, q=t^(d-1), s=t^d, r=1-q. Its exported theorem
`truncation_scalar_cancellation`, for d>=2 and 0<t<1, proves

    L_tuple / [(d+1)d ((1-t^d)/d!) H_tuple] - 1/(d+1)
      = truncationRationalDefect d t.

The factorial identity, all canceled-factor positivity, and s=t*q are derived.
The right-hand side is exactly the published equation (D), with numerator

    t^(d-1) [d(d-1)-(d+1)(d-2)t-2t^d].

## Geometric boundary and root assembly

These two modules are exact algebraic lemmas. Their standalone scalar
theorem is not itself a theorem about `entryDefect`. The root worker separately
consumes the actual facet areas, actual volume, actual positive-height
translation, actual determinant shear, frozen pyramid/B bridge, and facet
reindexing. The root reports successful kernel compilation of
`Entry005.truncation_entryDefect_exact` and the unmodified
`Entry005.truncationSharpness : truncationSharpnessGoal` using these lemmas.
Certification of that complete closure belongs to the root's full clean
release rebuild and audit. No Main upper-bound claim is made by this report.

## Trust and validation

Every one of the 17 public theorem declarations includes `#print axioms` in
its mathematical source. Their reported axiom sets are exactly
`propext`, `Classical.choice`, and `Quot.sound`. They contain no `sorry`,
`admit`, custom axiom, `native_decide`, unsafe proof replacement, or disabled
kernel checking. No mathematical-source linter is suppressed.

`scripts/audit_truncation_determinants.py` additionally rebuilds both new
mathematical sources into an initially empty owned output directory. Pinned,
previously verified dependencies are reused through read-only artifact
symlinks; this local check is distinct from the root's full source rebuild.
`formal/audit/truncation-determinants-owned.lean` enumerates every actual
declaration belonging to these two modules, including private and generated
ones, and recursively collects its axioms. Unexpected axioms are rejected.
This diagnostic executes no mathematical proof by an evaluation shortcut.

The local receipts are
`logs/truncation-determinant-clean-build.log`,
`logs/truncation-determinant-owned-axioms.log`, and
`logs/truncation-determinant-verification.json`.

Frozen source SHA256 values:

- TruncationFacetDeterminants.lean:
  `688c8774a3b0b1224988901e6c55e717e982c148860d682ee24776adb2cf5f0b`.
- TruncationScalarCancellation.lean:
  `94ff9a9236b04a88183d42bcb6ff0d2488b2df43479f21f3772cbabede1950d1`.
