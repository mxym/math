# Signed arithmetic and geometry: upstream-to-interface map

Source: `upstream-028/GaussianMoat`, OpenAI family 028, commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`; Entry 002 v3 §§2–3.
Implementation: `Entry002/GenericSignedArithmetic.lean`.

The domain is an arbitrary additive group `L` with an actual
`Basis (Fin 2) ℤ L`. Geometry is the existing `planarEmbedding b e`, where
`e : CoeffSpace ≃ₗ[ℝ] Plane`. Residues are actual additive maps into `ZMod p`.
The definitions of `IsPrimitive`, `ArithmeticInterface`, `FiniteSieveTarget`,
and `MainTarget` are unchanged.

| Upstream dependency | Generic replacement | Inputs used |
| --- | --- | --- |
| `SignedArithmetic.PrimitiveDirection` | `primitive_coefficients_coprime`, `primitive_of_coefficients_coprime` | Actual manuscript `IsPrimitive`; integral basis |
| `exists_primitive_direction` | `exists_primitive_lattice_direction` | Nonzero integral vector; integer gcd |
| `int_multiple_of_determinant_zero` | `integer_multiple_of_latticeDet_zero` | Genuine primitive direction; genuine coefficient determinant zero; Bézout |
| `not_both_factors_dvd_primitive` | `primitive_not_both_signed_kernels` | A2 paired kernels; actual prime `p>1` |
| `factor_dvd_integer_iff` | `residue_zsmul_zero_iff` | Prime residue field; the map does not kill the direction |
| `uneligible_product_dvd_coefficient` | `uneligible_product_dvd_coefficient` | Distinct prime selection; selected maps kill the integer multiple |
| `line_witness_norm_lower` | `line_witness_length_lower` | The previous lemma, primitive line, genuine planar norm and scalar homogeneity |
| A1 common-kernel index | `selectedResidueMap`, `selected_kernel_index` | Actual joint surjectivity from CRT; first isomorphism theorem; exact residue cardinalities |
| `LatticeComponents.norm_dvd_determinant` | `residue_kernel_dvd_latticeDet`, `selected_kernel_product_dvd_latticeDet` | Surjective additive maps, prime fields, two integral basis coordinates |
| `SignedGeometry.period_le_common_norm` | `period_le_common_product` | Exact common prime product; actual Hamming changes on the selected primes |
| `near_witnesses_collinear` | `common_product_le_abs_det`, `near_kernel_witnesses_collinear` | Exact determinant divisibility and determinant window |
| `determinant_rotated`, `rectangle_determinant_bound` | `planarEmbedding_determinant`, `latticeRectangle_determinant_bound` | Arbitrary real lattice isomorphism, any orientation isometry, actual nonzero fundamental-cell determinant |
| `rectangle_norm_bound` | `latticeRectangle_norm_bound` | Actual Euclidean norm; orientation isometry; `0 ≤ W ≤ R` |
| Deterministic part of the thin-rectangle lemma | `nearby_rectangle_kernel_witnesses_collinear` | Rectangle half-widths, common selected kernels, numerical determinant/prime-product inequality |
| Short-displacement residue injectivity | `residue_injective_at_collision_scale` | A3 nonzero-kernel length lower bound; genuine planar differences |

The Gaussian common-factor argument is replaced by elementary residue-row
linear algebra. If a surjective additive residue map kills `x` and `y`, one
of its basis-coordinate coefficients is nonzero, forcing their coefficient
determinant to vanish modulo `p`. Coprimality combines these into the exact
product divisibility. No factorization or primality property of lattice
elements is used.

## Many-differences extraction assessment

`WalkGeometry.lean` lines 1–370 are already generic complex-plane geometry:
the discrete Sperner lemma and `path_difference_cover_general` do not depend
on Gaussian integers. They can be transported to the actual plane with
`Complex.orthonormalBasisOneI.repr.symm : Plane ≃ₗᵢ[ℝ] ℂ`, preserving the
user-selected planar metric exactly.

The Gaussian-dependent section begins at `latticeCoords` (line 372).
Replace this equivalence with `b.repr` composed with finite Finsupp/function
coordinates. `twoVectorMap` becomes the integer matrix with columns
`b.repr a` and `b.repr b`; its determinant is `latticeDet`.
`twoVectorMap_quotient_card` uses `Submodule.natAbs_det_equiv` and therefore
generalizes directly. `lattice_path_difference_card` (lines 463–501) then
uses only that quotient cardinality, generic complex-plane path coverage,
and finiteness of genuine planar balls (already proved in `Embedding.lean`).

`DifferenceSampling.walk_many_differences` additionally needs a quantitative
rectangle-packing bound. Its hard-coded unit lattice spacing should be replaced
by a positive separation constant obtained from the inverse operator norm of
the supplied full planar embedding, or by a fixed scalar normalization.

## Remaining proof dependencies

This module proves deterministic signed arithmetic and thin-rectangle
collinearity. It does not assert the probabilistic thin-rectangle theorem,
the many-differences estimate, entropy enrichment, scale scheduling, or
`FiniteSieveTarget`. The next probability step combines the proved line-witness
lower bound and A4 eligible-product upper bound with generic fair-sign
Hoeffding and Boolean-cube separation. A3 supplies short-displacement residue
injectivity independently; A5 supplies the asymptotic prime count.
