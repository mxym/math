/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.CyclotomicAbstractFixedFieldArtinBase


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

/-- The canonical compositum of an abstract fixed field with a finite
layer of the rational cyclotomic `ZHat`-extension. -/
def abstractFixedFieldCyclotomicFiniteCompositum
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IntermediateField ℚ (SeparableClosure ℚ) :=
  LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H.field ⊔
    IntermediateField.lift E.toIntermediateField

noncomputable instance
    abstractFixedFieldCyclotomicFiniteCompositum_finiteDimensional
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    FiniteDimensional ℚ
      (abstractFixedFieldCyclotomicFiniteCompositum H E) := by
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H.field
  let : FiniteDimensional ℚ F :=
    LocalClassFieldTheory.abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) H.field H.finite
  let : FiniteDimensional ℚ
      (IntermediateField.lift E.toIntermediateField) :=
    ((IntermediateField.liftAlgEquiv
      E.toIntermediateField).toLinearEquiv).finiteDimensional
  exact IntermediateField.finiteDimensional_sup
    F (IntermediateField.lift E.toIntermediateField)

noncomputable instance
    abstractFixedFieldCyclotomicFiniteCompositum_numberField
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    NumberField
      (abstractFixedFieldCyclotomicFiniteCompositum H E) :=
  NumberField.of_module_finite ℚ
    (abstractFixedFieldCyclotomicFiniteCompositum H E)

/-- The lower abstract fixed field embedded into its finite
cyclotomic compositum. -/
noncomputable def
    abstractFixedFieldCyclotomicFiniteCompositumBaseEmbedding
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field →ₐ[ℚ]
      abstractFixedFieldCyclotomicFiniteCompositum H E :=
  IntermediateField.inclusion
    (show
      LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field ≤
        abstractFixedFieldCyclotomicFiniteCompositum H E from
      le_sup_left)


noncomputable local instance
    abstractFixedFieldCyclotomic_numberField
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    NumberField
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field) := by
  let : FiniteDimensional ℚ
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field) :=
    LocalClassFieldTheory.abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) H.field H.finite
  exact
    NumberField.of_module_finite ℚ
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)

/-- A finite rational cyclotomic layer embedded into its compositum
with the abstract fixed field. -/
noncomputable def
    abstractFixedFieldCyclotomicFiniteCompositumLayerEmbedding
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    E →ₐ[ℚ]
      abstractFixedFieldCyclotomicFiniteCompositum H E :=
  (IntermediateField.inclusion
      (show
        IntermediateField.lift E.toIntermediateField ≤
          abstractFixedFieldCyclotomicFiniteCompositum H E from
        le_sup_right)).comp
    (IntermediateField.liftAlgEquiv E.toIntermediateField).toAlgHom

noncomputable instance
    abstractFixedFieldCyclotomicFiniteCompositum_baseAlgebra
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    Algebra
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (abstractFixedFieldCyclotomicFiniteCompositum H E) :=
  RingHom.toAlgebra
    (AlgHom.toRingHom
      (abstractFixedFieldCyclotomicFiniteCompositumBaseEmbedding H E))

noncomputable instance
    abstractFixedFieldCyclotomicFiniteCompositum_layerAlgebra
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    Algebra E
      (abstractFixedFieldCyclotomicFiniteCompositum H E) :=
  RingHom.toAlgebra
    (AlgHom.toRingHom
      (abstractFixedFieldCyclotomicFiniteCompositumLayerEmbedding H E))

/-- The finite-layer action induced by its explicit embedding into the
finite compositum. -/
noncomputable instance
    abstractFixedFieldCyclotomicFiniteCompositum_layerSMul
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    SMul E
      (abstractFixedFieldCyclotomicFiniteCompositum H E) :=
  Algebra.toSMul
    (self :=
      abstractFixedFieldCyclotomicFiniteCompositum_layerAlgebra H E)

instance
    abstractFixedFieldCyclotomicFiniteCompositum_baseScalarTower
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IsScalarTower ℚ
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (abstractFixedFieldCyclotomicFiniteCompositum H E) :=
  IsScalarTower.of_algebraMap_eq'
    (AlgHom.comp_algebraMap
      (abstractFixedFieldCyclotomicFiniteCompositumBaseEmbedding H E)).symm

instance
    abstractFixedFieldCyclotomicFiniteCompositum_layerScalarTower
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IsScalarTower ℚ E
      (abstractFixedFieldCyclotomicFiniteCompositum H E) :=
  IsScalarTower.of_algebraMap_eq'
    (AlgHom.comp_algebraMap
      (abstractFixedFieldCyclotomicFiniteCompositumLayerEmbedding H E)).symm

/-- Inclusion of the finite cyclotomic compositum into the actual
maximal-unramified compositum. -/
noncomputable def
    abstractFixedFieldCyclotomicFiniteCompositumInclusion
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    let hI :=
      rationalCyclotomicFieldInertia_le H.field
    abstractFixedFieldCyclotomicFiniteCompositum H E →ₐ[ℚ]
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hI := by
  let hI :=
    rationalCyclotomicFieldInertia_le H.field
  let J :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ)
      (rationalCyclotomicDegreeData.fieldInertia H.field)
  have hle :
      abstractFixedFieldCyclotomicFiniteCompositum H E ≤ J := by
    dsimp only [J]
    rw [
      rationalCyclotomicDegreeData_fixedField_fieldInertia H.field]
    exact
      sup_le_sup le_rfl
        (IntermediateField.lift_le E.toIntermediateField)
  exact IntermediateField.inclusion hle

/-- The same finite-compositum inclusion over the lower abstract fixed
field. -/
noncomputable def
    abstractFixedFieldCyclotomicFiniteCompositumInclusionOverBase
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    let hI :=
      rationalCyclotomicFieldInertia_le H.field
    abstractFixedFieldCyclotomicFiniteCompositum H E →ₐ[
      LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field]
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hI := by
  let f :=
    abstractFixedFieldCyclotomicFiniteCompositumInclusion H E
  exact
    { f.toRingHom with
      commutes' := by
        intro x
        rfl }


end Reciprocity
end GlobalClassFieldTheory
