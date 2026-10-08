/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.CyclotomicAbstractFixedFieldArtinFiniteLayer


set_option autoImplicit false


open scoped IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open KummerTheory

attribute [local instance]
  cyclotomicAbstractFixedFieldArtin_separableClosureAlgebra
  cyclotomicAbstractFixedFieldArtin_cyclotomicZHatFieldAlgebra
  cyclotomicAbstractFixedFieldArtin_cyclotomicZHatFieldNormal
  abstractFixedFieldCyclotomic_numberField

/-- The explicit base algebra on a finite cyclotomic layer is the canonical
intermediate-field inclusion used by the finite Galois inverse system. -/
theorem abstractFixedFieldCyclotomicFiniteLayer_baseAlgebra_eq_algebra'
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    abstractFixedFieldCyclotomicFiniteLayer_baseAlgebra H E =
      (abstractFixedFieldCyclotomicFiniteGaloisLayer H E).algebra' := by
  apply Algebra.algebra_ext
  intro x
  apply Subtype.ext
  rfl

/-- The finite Galois layer uses its canonical inclusion into the full
relative fixed field for the upper scalar action. -/
instance
    abstractFixedFieldCyclotomicFiniteGaloisLayer_scalarTower
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IsScalarTower
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (abstractFixedFieldCyclotomicFiniteGaloisLayer H E).toIntermediateField
      (LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (rationalCyclotomicFieldInertia_le H.field)) := by
  let i :
      (abstractFixedFieldCyclotomicFiniteGaloisLayer
          H E).toIntermediateField →ₐ[
        LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field]
        LocalClassFieldTheory.abstractRelativeFixedField
          ℚ (SeparableClosure ℚ)
          (rationalCyclotomicFieldInertia_le H.field) :=
    { (abstractFixedFieldCyclotomicFiniteGaloisLayer
          H E).toIntermediateField.val.toRingHom with
      commutes' := by
        intro x
        rfl }
  exact
    IsScalarTower.of_algebraMap_eq'
      (AlgHom.comp_algebraMap i).symm

/-- The canonical inclusion of the finite cyclotomic layer into the
full abstract-fixed-field compositum. -/
private noncomputable def
    abstractFixedFieldCyclotomicFiniteLayerInclusion
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    abstractFixedFieldCyclotomicFiniteLayer H E →ₐ[
      LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field]
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (rationalCyclotomicFieldInertia_le H.field) :=
  IntermediateField.val
    (abstractFixedFieldCyclotomicFiniteLayer H E)

/-- The two embeddings of a finite rational cyclotomic layer into the
full abstract-fixed-field compositum agree. -/
private theorem
    abstractFixedFieldCyclotomicFiniteLayerEmbedding_inclusion
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField)
    (z : E) :
    abstractFixedFieldCyclotomicFiniteLayerInclusion H E
        (abstractFixedFieldCyclotomicFiniteLayerEmbedding H E z) =
      rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum H
        (z : rationalCyclotomicZHatField) := by
  exact Subtype.ext rfl

/-- Restriction to `E` commutes pointwise with the restriction from the
full rational cyclotomic tower. -/
private theorem
    restrictNormalHom_abstractFixedFieldCyclotomicRestriction_apply
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField)
    [Normal ℚ E]
    (σ :
      Gal(
        LocalClassFieldTheory.abstractRelativeFixedField
          ℚ (SeparableClosure ℚ)
          (rationalCyclotomicFieldInertia_le H.field) /
        LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field))
    (z : E) :
    ((AlgEquiv.restrictNormalHom E
      (abstractFixedFieldCyclotomicRestriction H σ)) z :
        rationalCyclotomicZHatField) =
      (abstractFixedFieldCyclotomicRestriction H σ)
        (z : rationalCyclotomicZHatField) := by
  exact
    AlgEquiv.restrictNormal_commutes
      (abstractFixedFieldCyclotomicRestriction H σ) E z

/-- The raw cyclotomic restriction commutes with the canonical embedding
of the full rational cyclotomic tower. -/
private theorem
    abstractFixedFieldCyclotomicRestriction_embedding_apply
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (σ :
      Gal(
        LocalClassFieldTheory.abstractRelativeFixedField
          ℚ (SeparableClosure ℚ)
          (rationalCyclotomicFieldInertia_le H.field) /
        LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field))
    (z : rationalCyclotomicZHatField) :
    rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum H
        (abstractFixedFieldCyclotomicRestriction H σ z) =
      σ
        (rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum
          H z) := by
  let U :=
    LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ)
      (rationalCyclotomicFieldInertia_le H.field)
  exact
    AlgEquiv.restrictNormal_commutes
      (MulSemiringAction.toAlgEquiv ℚ U σ)
      rationalCyclotomicZHatField z

/-- Restriction to the finite compositum layer commutes with its
canonical inclusion into the full compositum. -/
private theorem
    restrictNormalHom_abstractFixedFieldCyclotomicFiniteLayer_apply
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField)
    [Normal
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (abstractFixedFieldCyclotomicFiniteLayer H E)]
    (σ :
      Gal(
        LocalClassFieldTheory.abstractRelativeFixedField
          ℚ (SeparableClosure ℚ)
          (rationalCyclotomicFieldInertia_le H.field) /
        LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field))
    (z : abstractFixedFieldCyclotomicFiniteLayer H E) :
    abstractFixedFieldCyclotomicFiniteLayerInclusion H E
        (AlgEquiv.restrictNormalHom
          (abstractFixedFieldCyclotomicFiniteLayer H E) σ z) =
      σ (abstractFixedFieldCyclotomicFiniteLayerInclusion H E z) := by
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H.field
  let U :=
    LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ)
      (rationalCyclotomicFieldInertia_le H.field)
  let P : IntermediateField F U :=
    abstractFixedFieldCyclotomicFiniteLayer H E
  exact
    AlgEquiv.restrictNormal_commutes
      (MulSemiringAction.toAlgEquiv F U σ) P z

/-- Restricting the finite-compositum action further to `E` commutes
with the explicit embedding of `E` into that finite layer. -/
private theorem
    abstractFixedFieldCyclotomicFiniteLayerEmbedding_restrict_apply
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField)
    [Normal ℚ E]
    [Normal
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (abstractFixedFieldCyclotomicFiniteLayer H E)]
    (σ :
      Gal(
        LocalClassFieldTheory.abstractRelativeFixedField
          ℚ (SeparableClosure ℚ)
          (rationalCyclotomicFieldInertia_le H.field) /
        LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field))
    (z : E) :
    abstractFixedFieldCyclotomicFiniteLayerEmbedding H E
        (IntermediateField.restrictRestrictAlgEquivMapHom
          ℚ E
          (LocalClassFieldTheory.abstractFixedField
            ℚ (SeparableClosure ℚ) H.field)
          (abstractFixedFieldCyclotomicFiniteLayer H E)
          (AlgEquiv.restrictNormalHom
            (abstractFixedFieldCyclotomicFiniteLayer H E) σ) z) =
      (AlgEquiv.restrictNormalHom
        (abstractFixedFieldCyclotomicFiniteLayer H E) σ)
        (abstractFixedFieldCyclotomicFiniteLayerEmbedding H E z) := by
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H.field
  let U :=
    LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ)
      (rationalCyclotomicFieldInertia_le H.field)
  let P : IntermediateField F U :=
    abstractFixedFieldCyclotomicFiniteLayer H E
  exact
    AlgEquiv.restrictNormal_commutes
      (MulSemiringAction.toAlgEquiv ℚ P
        (AlgEquiv.restrictNormalHom P σ)) E z

/-- The left finite-level restriction, after both canonical embeddings into
the full compositum, is the action of `σ` on the cyclotomic embedding. -/
private theorem
    restrictNormalHom_abstractFixedFieldCyclotomicRestriction_left_embedded
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField)
    [Normal ℚ E]
    (σ :
      Gal(
        LocalClassFieldTheory.abstractRelativeFixedField
          ℚ (SeparableClosure ℚ)
          (rationalCyclotomicFieldInertia_le H.field) /
        LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field))
    (x : E) :
    abstractFixedFieldCyclotomicFiniteLayerInclusion H E
        (abstractFixedFieldCyclotomicFiniteLayerEmbedding H E
          (AlgEquiv.restrictNormalHom E
            (abstractFixedFieldCyclotomicRestriction H σ) x)) =
      σ
        (rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum H
          (x : rationalCyclotomicZHatField)) := by
  calc
    abstractFixedFieldCyclotomicFiniteLayerInclusion H E
          (abstractFixedFieldCyclotomicFiniteLayerEmbedding H E
            (AlgEquiv.restrictNormalHom E
              (abstractFixedFieldCyclotomicRestriction H σ) x)) =
        rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum H
          (((AlgEquiv.restrictNormalHom E
            (abstractFixedFieldCyclotomicRestriction H σ) x) :
              rationalCyclotomicZHatField)) :=
      abstractFixedFieldCyclotomicFiniteLayerEmbedding_inclusion H E _
    _ = rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum H
          (abstractFixedFieldCyclotomicRestriction H σ
            (x : rationalCyclotomicZHatField)) :=
      congrArg
        (rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum H)
        (restrictNormalHom_abstractFixedFieldCyclotomicRestriction_apply
          H E σ x)
    _ = σ
          (rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum
            H (x : rationalCyclotomicZHatField)) :=
      abstractFixedFieldCyclotomicRestriction_embedding_apply
        H σ (x : rationalCyclotomicZHatField)

/-- The right finite-level restriction, after both canonical embeddings into
the full compositum, is the same action of `σ`. -/
private theorem
    restrictNormalHom_abstractFixedFieldCyclotomicRestriction_right_embedded
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField)
    [Normal ℚ E]
    [Normal
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (abstractFixedFieldCyclotomicFiniteLayer H E)]
    (σ :
      Gal(
        LocalClassFieldTheory.abstractRelativeFixedField
          ℚ (SeparableClosure ℚ)
          (rationalCyclotomicFieldInertia_le H.field) /
        LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field))
    (x : E) :
    abstractFixedFieldCyclotomicFiniteLayerInclusion H E
        (abstractFixedFieldCyclotomicFiniteLayerEmbedding H E
          (IntermediateField.restrictRestrictAlgEquivMapHom
            ℚ E
            (LocalClassFieldTheory.abstractFixedField
              ℚ (SeparableClosure ℚ) H.field)
            (abstractFixedFieldCyclotomicFiniteLayer H E)
            (AlgEquiv.restrictNormalHom
              (abstractFixedFieldCyclotomicFiniteLayer H E) σ) x)) =
      σ
        (rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum H
          (x : rationalCyclotomicZHatField)) := by
  calc
    abstractFixedFieldCyclotomicFiniteLayerInclusion H E
          (abstractFixedFieldCyclotomicFiniteLayerEmbedding H E
            (IntermediateField.restrictRestrictAlgEquivMapHom
              ℚ E
              (LocalClassFieldTheory.abstractFixedField
                ℚ (SeparableClosure ℚ) H.field)
              (abstractFixedFieldCyclotomicFiniteLayer H E)
              (AlgEquiv.restrictNormalHom
                (abstractFixedFieldCyclotomicFiniteLayer H E) σ) x)) =
        abstractFixedFieldCyclotomicFiniteLayerInclusion H E
          ((AlgEquiv.restrictNormalHom
            (abstractFixedFieldCyclotomicFiniteLayer H E) σ)
            (abstractFixedFieldCyclotomicFiniteLayerEmbedding H E x)) :=
      congrArg
        (abstractFixedFieldCyclotomicFiniteLayerInclusion H E)
        (abstractFixedFieldCyclotomicFiniteLayerEmbedding_restrict_apply
          H E σ x)
    _ = σ
          (abstractFixedFieldCyclotomicFiniteLayerInclusion H E
            (abstractFixedFieldCyclotomicFiniteLayerEmbedding H E x)) :=
      restrictNormalHom_abstractFixedFieldCyclotomicFiniteLayer_apply
        H E σ (abstractFixedFieldCyclotomicFiniteLayerEmbedding H E x)
    _ = σ
          (rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum
            H (x : rationalCyclotomicZHatField)) :=
      congrArg σ
        (abstractFixedFieldCyclotomicFiniteLayerEmbedding_inclusion H E x)

/-- Pointwise form of finite-layer restriction compatibility. -/
private theorem
    restrictNormalHom_abstractFixedFieldCyclotomicRestriction_pointwise
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField)
    [Normal ℚ E]
    [Normal
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (abstractFixedFieldCyclotomicFiniteLayer H E)]
    (σ :
      Gal(
        LocalClassFieldTheory.abstractRelativeFixedField
          ℚ (SeparableClosure ℚ)
          (rationalCyclotomicFieldInertia_le H.field) /
        LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field))
    (x : E) :
    AlgEquiv.restrictNormalHom E
        (abstractFixedFieldCyclotomicRestriction H σ) x =
      IntermediateField.restrictRestrictAlgEquivMapHom
          ℚ E
          (LocalClassFieldTheory.abstractFixedField
            ℚ (SeparableClosure ℚ) H.field)
          (abstractFixedFieldCyclotomicFiniteLayer H E)
        (AlgEquiv.restrictNormalHom
          (abstractFixedFieldCyclotomicFiniteLayer H E) σ) x := by
  apply
    (abstractFixedFieldCyclotomicFiniteLayerEmbedding H E).injective
  apply
    (abstractFixedFieldCyclotomicFiniteLayerInclusion H E).injective
  exact
    (restrictNormalHom_abstractFixedFieldCyclotomicRestriction_left_embedded
      H E σ x).trans
      (restrictNormalHom_abstractFixedFieldCyclotomicRestriction_right_embedded
        H E σ x).symm

/-- Restricting through a finite layer commutes with restriction from
the full abstract-fixed-field compositum. -/
theorem
    restrictNormalHom_abstractFixedFieldCyclotomicRestriction
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField)
    (σ :
      Gal(
        LocalClassFieldTheory.abstractRelativeFixedField
          ℚ (SeparableClosure ℚ)
          (rationalCyclotomicFieldInertia_le H.field) /
        LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field)) :
    letI : Normal ℚ E := E.isGalois.to_normal
    AlgEquiv.restrictNormalHom E
        (abstractFixedFieldCyclotomicRestriction H σ) =
      IntermediateField.restrictRestrictAlgEquivMapHom
          ℚ E
          (LocalClassFieldTheory.abstractFixedField
            ℚ (SeparableClosure ℚ) H.field)
          (abstractFixedFieldCyclotomicFiniteLayer H E)
        (AlgEquiv.restrictNormalHom
          (abstractFixedFieldCyclotomicFiniteGaloisLayer H E)
          σ) := by
  let : Normal ℚ E := E.isGalois.to_normal
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H.field
  let U :=
    LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ)
      (rationalCyclotomicFieldInertia_le H.field)
  let T := rationalCyclotomicZHatField
  let P : IntermediateField F U :=
    abstractFixedFieldCyclotomicFiniteLayer H E
  let : Algebra T U :=
    abstractFixedFieldCyclotomicCompositum_algebra H
  let : IsScalarTower ℚ T U :=
    abstractFixedFieldCyclotomicCompositum_scalarTower H
  let : Algebra E P :=
    abstractFixedFieldCyclotomicFiniteLayer_layerAlgebra H E
  let : IsScalarTower ℚ E P :=
    abstractFixedFieldCyclotomicFiniteLayer_layerScalarTower H E
  let : IsAbelianGalois F P := by
    change IsAbelianGalois F
      (abstractFixedFieldCyclotomicFiniteLayer H E)
    exact
      abstractFixedFieldCyclotomicFiniteLayer_isAbelianGalois H E
  let : Normal F P := IsGalois.to_normal
  apply AlgEquiv.ext
  intro x
  exact
    restrictNormalHom_abstractFixedFieldCyclotomicRestriction_pointwise
      H E σ x


end Reciprocity
end GlobalClassFieldTheory
