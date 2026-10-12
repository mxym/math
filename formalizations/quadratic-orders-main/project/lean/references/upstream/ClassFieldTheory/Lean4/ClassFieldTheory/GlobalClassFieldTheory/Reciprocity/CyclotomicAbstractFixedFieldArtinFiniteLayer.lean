/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.CyclotomicAbstractFixedFieldArtinCompositum


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

/-- The finite cyclotomic compositum as an intermediate field of the
actual maximal-unramified extension. -/
noncomputable def abstractFixedFieldCyclotomicFiniteLayer
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    let hI :=
      rationalCyclotomicFieldInertia_le H.field
    IntermediateField
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hI) :=
  (abstractFixedFieldCyclotomicFiniteCompositumInclusionOverBase H E).fieldRange

/-- The base algebra on the finite field range, obtained from the
explicit base embedding followed by the field-range equivalence. -/
noncomputable instance
    abstractFixedFieldCyclotomicFiniteLayer_baseAlgebra
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    Algebra
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (abstractFixedFieldCyclotomicFiniteLayer H E) :=
  RingHom.toAlgebra
    ((AlgHom.toRingHom
      (AlgEquiv.toAlgHom
        (AlgHom.equivFieldRange
          (abstractFixedFieldCyclotomicFiniteCompositumInclusionOverBase
            H E)))).comp
      (AlgHom.toRingHom
        (abstractFixedFieldCyclotomicFiniteCompositumBaseEmbedding H E)))

/-- The scalar action belonging to the canonical base algebra on the
finite field range. -/
noncomputable instance
    abstractFixedFieldCyclotomicFiniteLayer_baseSMul
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    SMul
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (abstractFixedFieldCyclotomicFiniteLayer H E) :=
  Algebra.toSMul
    (self := abstractFixedFieldCyclotomicFiniteLayer_baseAlgebra H E)


noncomputable instance
    abstractFixedFieldCyclotomicFiniteLayer_baseModule
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    Module
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (abstractFixedFieldCyclotomicFiniteLayer H E) :=
  @Algebra.toModule
    (LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H.field)
    (abstractFixedFieldCyclotomicFiniteLayer H E)
    _ _
    (abstractFixedFieldCyclotomicFiniteLayer_baseAlgebra H E)

/-- The field-range equivalence rebuilt over the explicit base
algebras.  Its underlying ring equivalence is the canonical one. -/
noncomputable def
    abstractFixedFieldCyclotomicFiniteCompositumEquivFiniteLayer
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    abstractFixedFieldCyclotomicFiniteCompositum H E ≃ₐ[
      LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field]
      abstractFixedFieldCyclotomicFiniteLayer H E :=
  AlgEquiv.ofRingEquiv
    (f :=
      (AlgHom.equivFieldRange
        (abstractFixedFieldCyclotomicFiniteCompositumInclusionOverBase
          H E)).toRingEquiv)
    (fun _ => rfl)

noncomputable instance
    abstractFixedFieldCyclotomicFiniteLayer_finiteDimensional
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    FiniteDimensional
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (abstractFixedFieldCyclotomicFiniteLayer H E) :=
  (abstractFixedFieldCyclotomicFiniteCompositumEquivFiniteLayer
    H E).toLinearEquiv.finiteDimensional

noncomputable instance
    abstractFixedFieldCyclotomicFiniteLayer_numberField
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    NumberField
      (abstractFixedFieldCyclotomicFiniteLayer H E) :=
  NumberField.of_module_finite
    (LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H.field)
    (abstractFixedFieldCyclotomicFiniteLayer H E)

noncomputable instance
    abstractFixedFieldCyclotomicFiniteLayer_isAbelianGalois
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IsAbelianGalois
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (abstractFixedFieldCyclotomicFiniteLayer H E) := by
  let hI :=
    rationalCyclotomicFieldInertia_le H.field
  let : IsAbelianGalois
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hI) :=
    abstractFixedFieldCyclotomic_isAbelianGalois H
  exact
    IsAbelianGalois.of_algHom
      ((abstractFixedFieldCyclotomicFiniteCompositumInclusionOverBase
          H E).comp
        (AlgEquiv.toAlgHom
          (AlgEquiv.symm
            (abstractFixedFieldCyclotomicFiniteCompositumEquivFiniteLayer
              H E))))

instance
    abstractFixedFieldCyclotomicFiniteLayer_baseScalarTower
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IsScalarTower ℚ
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (abstractFixedFieldCyclotomicFiniteLayer H E) := by
  let hI :=
    rationalCyclotomicFieldInertia_le H.field
  apply IsScalarTower.of_algebraMap_eq
  intro x
  apply Subtype.ext
  change
    algebraMap ℚ
        (LocalClassFieldTheory.abstractRelativeFixedField
          ℚ (SeparableClosure ℚ) hI) x =
      algebraMap
        (LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field)
        (LocalClassFieldTheory.abstractRelativeFixedField
          ℚ (SeparableClosure ℚ) hI)
        (algebraMap ℚ
          (LocalClassFieldTheory.abstractFixedField
            ℚ (SeparableClosure ℚ) H.field) x)
  exact
    IsScalarTower.algebraMap_apply
      ℚ
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hI) x

/-- The finite rational layer embedded into its corresponding
intermediate field over the abstract fixed field. -/
noncomputable def
    abstractFixedFieldCyclotomicFiniteLayerEmbedding
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    E →ₐ[ℚ]
      abstractFixedFieldCyclotomicFiniteLayer H E := by
  exact
    (AlgEquiv.toAlgHom
      (AlgEquiv.restrictScalars ℚ
        (abstractFixedFieldCyclotomicFiniteCompositumEquivFiniteLayer
          H E))).comp
      (abstractFixedFieldCyclotomicFiniteCompositumLayerEmbedding H E)

noncomputable instance
    abstractFixedFieldCyclotomicFiniteLayer_layerAlgebra
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    Algebra E
      (abstractFixedFieldCyclotomicFiniteLayer H E) :=
  RingHom.toAlgebra
    (AlgHom.toRingHom
      (abstractFixedFieldCyclotomicFiniteLayerEmbedding H E))

/-- The finite-layer action on its actual image in the relative fixed
field. -/
noncomputable instance
    abstractFixedFieldCyclotomicFiniteLayer_layerSMul
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    SMul E
      (abstractFixedFieldCyclotomicFiniteLayer H E) :=
  Algebra.toSMul
    (self := abstractFixedFieldCyclotomicFiniteLayer_layerAlgebra H E)

instance
    abstractFixedFieldCyclotomicFiniteLayer_layerScalarTower
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    IsScalarTower ℚ E
      (abstractFixedFieldCyclotomicFiniteLayer H E) :=
  IsScalarTower.of_algebraMap_eq'
    (AlgHom.comp_algebraMap
      (abstractFixedFieldCyclotomicFiniteLayerEmbedding H E)).symm

/-- The finite cyclotomic layer as an object of the finite-Galois
inverse system of the actual maximal-unramified extension. -/
@[reducible]
noncomputable def
    abstractFixedFieldCyclotomicFiniteGaloisLayer
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (E :
      FiniteGaloisIntermediateField
        ℚ rationalCyclotomicZHatField) :
    FiniteGaloisIntermediateField
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (rationalCyclotomicFieldInertia_le H.field)) where
  toIntermediateField :=
    abstractFixedFieldCyclotomicFiniteLayer H E
  finiteDimensional :=
    abstractFixedFieldCyclotomicFiniteLayer_finiteDimensional H E
  isGalois :=
    (abstractFixedFieldCyclotomicFiniteLayer_isAbelianGalois H E).toIsGalois


end Reciprocity
end GlobalClassFieldTheory
