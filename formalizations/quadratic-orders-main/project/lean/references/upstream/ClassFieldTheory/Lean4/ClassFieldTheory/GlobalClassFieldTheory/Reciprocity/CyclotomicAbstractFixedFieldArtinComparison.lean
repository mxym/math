/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.CyclotomicAbstractFixedFieldArtinCoordinates


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

/-- The actual infinite global Artin map on an abstract fixed field
restricts to the rational cyclotomic Artin map of the ordinary idele
norm. -/
@[simp]
theorem
    abstractFixedFieldCyclotomicRestriction_infiniteGlobalArtinMonoidHom
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (a :
      IdeleGroup
        (LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field)) :
    let F :=
      LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field
    letI : FiniteDimensional ℚ F :=
      LocalClassFieldTheory.abstractFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) H.field H.finite
    letI : NumberField F :=
      NumberField.of_module_finite ℚ F
    let hI :=
      rationalCyclotomicFieldInertia_le H.field
    let U :=
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hI
    letI : IsAbelianGalois F U :=
      abstractFixedFieldCyclotomic_isAbelianGalois H
    abstractFixedFieldCyclotomicRestriction H
        (infiniteGlobalArtinMonoidHom F U a) =
      rationalCyclotomicZHatGlobalArtin
        (IdeleGroup.norm ℚ F a) := by
  exact
    abstractFixedFieldCyclotomicRestriction_infiniteGlobalArtin_inverseLimit
      H a

/-- In the normalized actual Galois coordinate, the infinite global
Artin symbol is exactly the normalized cyclotomic idele value. -/
theorem
    abstractFixedFieldCyclotomicGalEquivZHat_infiniteGlobalArtinMonoidHom
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (a :
      IdeleGroup
        (LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field)) :
    let F :=
      LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field
    letI : FiniteDimensional ℚ F :=
      LocalClassFieldTheory.abstractFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) H.field H.finite
    letI : NumberField F :=
      NumberField.of_module_finite ℚ F
    let hI :=
      rationalCyclotomicFieldInertia_le H.field
    let U :=
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hI
    letI : IsAbelianGalois F U :=
      abstractFixedFieldCyclotomic_isAbelianGalois H
    Multiplicative.toAdd
        (abstractFixedFieldCyclotomicGalEquivZHat H
          (infiniteGlobalArtinMonoidHom F U a)) =
      normalizedCyclotomicZHatIdeleValue F
        (Additive.ofMul a) := by
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H.field
  let : FiniteDimensional ℚ F :=
    LocalClassFieldTheory.abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) H.field H.finite
  let : NumberField F :=
    NumberField.of_module_finite ℚ F
  let hI :=
    rationalCyclotomicFieldInertia_le H.field
  let U :=
    LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) hI
  let : IsAbelianGalois F U :=
    abstractFixedFieldCyclotomic_isAbelianGalois H
  apply
    zHatMulNat_injective
      (H.residueDegree rationalCyclotomicDegreeData).pos
  calc
    (H.residueDegree rationalCyclotomicDegreeData : ℕ) •
          Multiplicative.toAdd
            (abstractFixedFieldCyclotomicGalEquivZHat H
              (infiniteGlobalArtinMonoidHom F U a)) =
        Multiplicative.toAdd
          (rationalCyclotomicZHatFieldGalEquivZHat
            (abstractFixedFieldCyclotomicRestriction H
              (infiniteGlobalArtinMonoidHom F U a))) := by
      exact
        (abstractFixedFieldCyclotomicRestriction_coordinate H
          (infiniteGlobalArtinMonoidHom F U a)).symm
    _ =
        Multiplicative.toAdd
          (rationalCyclotomicZHatFieldGalEquivZHat
            (rationalCyclotomicZHatGlobalArtin
              (IdeleGroup.norm ℚ F a))) := by
      rw [
        abstractFixedFieldCyclotomicRestriction_infiniteGlobalArtinMonoidHom]
    _ =
        cyclotomicZHatNormComposite F
          (Additive.ofMul a) := by
      rfl
    _ =
        cyclotomicZHatIntersectionDegree F •
          normalizedCyclotomicZHatIdeleValue F
            (Additive.ofMul a) := by
      exact
        (cyclotomicZHatIntersectionDegree_nsmul_normalizedIdeleValue
          F (Additive.ofMul a)).symm
    _ =
        (H.residueDegree rationalCyclotomicDegreeData : ℕ) •
          normalizedCyclotomicZHatIdeleValue F
            (Additive.ofMul a) := by
      rw [
        cyclotomicZHatIntersectionDegree_abstractFixedField_eq_residueDegree
          H]

/-- Representative form of the actual cyclotomic Artin-coordinate
identity after descent of the normalized value to the idele class
group. -/
theorem
    abstractFixedFieldCyclotomicGalEquivZHat_infiniteGlobalArtinMonoidHom_mk
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (a :
      IdeleGroup
        (LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field)) :
    let F :=
      LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field
    letI : FiniteDimensional ℚ F :=
      LocalClassFieldTheory.abstractFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) H.field H.finite
    letI : NumberField F :=
      NumberField.of_module_finite ℚ F
    let hI :=
      rationalCyclotomicFieldInertia_le H.field
    let U :=
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hI
    letI : IsAbelianGalois F U :=
      abstractFixedFieldCyclotomic_isAbelianGalois H
    Multiplicative.toAdd
        (abstractFixedFieldCyclotomicGalEquivZHat H
          (infiniteGlobalArtinMonoidHom F U a)) =
      normalizedCyclotomicZHatIdeleClassValueContinuous F
        (Additive.ofMul
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup F) a)) := by
  have hSeparableClosureAlgebra :
      cyclotomicAbstractFixedFieldArtin_separableClosureAlgebra =
        rationalSeparableClosureAlgebra :=
    Subsingleton.elim _ _
  cases hSeparableClosureAlgebra
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H.field
  let hI :=
    rationalCyclotomicFieldInertia_le H.field
  let U :=
    LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) hI
  let : IsAbelianGalois F U :=
    abstractFixedFieldCyclotomic_isAbelianGalois H
  calc
    Multiplicative.toAdd
        (abstractFixedFieldCyclotomicGalEquivZHat H
          (infiniteGlobalArtinMonoidHom F U a)) =
        normalizedCyclotomicZHatIdeleValue F
          (Additive.ofMul a) :=
      abstractFixedFieldCyclotomicGalEquivZHat_infiniteGlobalArtinMonoidHom
        H a
    _ =
        normalizedCyclotomicZHatIdeleClassValueContinuous F
          (Additive.ofMul
            (QuotientGroup.mk'
              (IdeleGroup.principalSubgroup F) a)) :=
      (normalizedCyclotomicZHatIdeleClassValueContinuous_mk
        (K := F) a).symm

/-- The genuine infinite global Artin symbol of the cyclotomic
maximal-unramified extension kills every principal idele of the
abstract fixed field. -/
@[simp]
theorem
    infiniteGlobalArtinMonoidHom_abstractFixedFieldCyclotomic_principalIdele
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (x :
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)ˣ) :
    let F :=
      LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field
    letI : FiniteDimensional ℚ F :=
      LocalClassFieldTheory.abstractFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) H.field H.finite
    letI : NumberField F :=
      NumberField.of_module_finite ℚ F
    let hI :=
      rationalCyclotomicFieldInertia_le H.field
    let U :=
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hI
    letI : IsAbelianGalois F U :=
      abstractFixedFieldCyclotomic_isAbelianGalois H
    infiniteGlobalArtinMonoidHom F U
        (IdeleGroup.principalIdele F x) =
      1 := by
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H.field
  let : FiniteDimensional ℚ F :=
    LocalClassFieldTheory.abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) H.field H.finite
  let : NumberField F :=
    NumberField.of_module_finite ℚ F
  let hI :=
    rationalCyclotomicFieldInertia_le H.field
  let U :=
    LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) hI
  let : IsAbelianGalois F U :=
    abstractFixedFieldCyclotomic_isAbelianGalois H
  have hcoord :
      Multiplicative.toAdd
        (abstractFixedFieldCyclotomicGalEquivZHat H
          (infiniteGlobalArtinMonoidHom F U
            (IdeleGroup.principalIdele F x))) = 0 :=
    (abstractFixedFieldCyclotomicGalEquivZHat_infiniteGlobalArtinMonoidHom
      H (IdeleGroup.principalIdele F x)).trans
      (normalizedCyclotomicZHatIdeleValue_principalIdele_eq_zero F x)
  apply (abstractFixedFieldCyclotomicGalEquivZHat H).injective
  rw [map_one]
  apply Multiplicative.ext
  exact hcoord.trans toAdd_one.symm


end Reciprocity
end GlobalClassFieldTheory
