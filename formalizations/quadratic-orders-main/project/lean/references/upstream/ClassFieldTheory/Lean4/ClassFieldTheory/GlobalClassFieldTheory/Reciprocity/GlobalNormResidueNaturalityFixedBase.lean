/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalNormResidueNaturalityTransports


set_option autoImplicit false


open scoped IsMulCommutative

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open GlobalClassFields
open KummerTheory
open AlgebraicNumberTheory
open LocalClassFieldTheory
open RamificationTheory

universe u


attribute [local instance]
  naturalityIdeleClassCommGroup
  ideleClassGroupIsMulCommutative
  ideleClassSubgroupNormal

section AbstractFixedFieldInclusion

variable
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)

local instance naturalityAbstractFixedFieldBaseQuotientFinite :
    Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          H.field (le_baseField H.field)) :=
  H.finite

local instance naturalityAbstractFixedFieldRelativeQuotientFinite :
    Finite
      (H.field.toSubgroup ⧸
        CyclicCohomology.extensionSubgroup H.field P.field P.below) :=
  P.finite

noncomputable local instance
    naturalityAbstractFixedFieldFiniteDimensional :
    FiniteDimensional ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field) :=
  abstractFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ) H.field H.finite

noncomputable local instance
    naturalityAbstractRelativeFixedFieldFiniteDimensional :
    FiniteDimensional
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below) :=
  abstractRelativeFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ)
    H.field P.field P.below H.finite P.finite

local instance naturalityAbstractFixedFieldRelativeScalarTower :
    IsScalarTower ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

noncomputable local instance
    naturalityAbstractRelativeFixedFieldAbsoluteFiniteDimensional :
    FiniteDimensional ℚ
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below) :=
  FiniteDimensional.trans ℚ
    (abstractFixedField ℚ (SeparableClosure ℚ) H.field)
    (abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below)

noncomputable local instance naturalityAbstractFixedFieldNumberField :
    NumberField
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field) :=
  NumberField.of_module_finite ℚ
    (abstractFixedField ℚ (SeparableClosure ℚ) H.field)

noncomputable local instance
    naturalityAbstractRelativeFixedFieldNumberField :
    NumberField
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below) :=
  NumberField.of_module_finite ℚ
    (abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below)

/-- Use the same direct fixed-field Galois witness as the intrinsic
norm-residue construction.  This prevents the dependent Galois-group type
from being synthesized through a second `IsAbelianGalois` instance path. -/
noncomputable local instance
    naturalityAbstractRelativeFixedFieldIsGalois :
    IsGalois
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below) :=
  abstractRelativeFixedField_isGalois
    ℚ (SeparableClosure ℚ)
    H.field P.field P.below P.normal

noncomputable local instance
    naturalityAbstractRelativeFixedFieldIsAbelianGalois :
    IsAbelianGalois
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field)
      (abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below) :=
  finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois P

/-- The lower subgroup obtained from the canonical inclusion of an abstract
fixed-field tower is the original lower closed subgroup. -/
theorem
    numberFieldEmbeddedBaseSubgroup_abstractFixedFieldInclusion
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field) :
    let F :=
      abstractFixedField ℚ (SeparableClosure ℚ) H.field
    let E :=
      abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below
    let j : E →ₐ[ℚ] SeparableClosure ℚ :=
      E.val.restrictScalars ℚ
    numberFieldEmbeddedBaseSubgroup F E j = H.field := by
  dsimp only
  have hi :
      numberFieldEmbeddedLowerEmbedding
          (abstractFixedField ℚ (SeparableClosure ℚ) H.field)
          (abstractRelativeFixedField
            ℚ (SeparableClosure ℚ) P.below)
          ((abstractRelativeFixedField
            ℚ (SeparableClosure ℚ) P.below).val.restrictScalars ℚ) =
        (abstractFixedField
          ℚ (SeparableClosure ℚ) H.field).val := by
    ext x
    rfl
  have hRange :
      (numberFieldEmbeddedLowerEmbedding
        (abstractFixedField ℚ (SeparableClosure ℚ) H.field)
        (abstractRelativeFixedField
          ℚ (SeparableClosure ℚ) P.below)
        ((abstractRelativeFixedField
          ℚ (SeparableClosure ℚ) P.below).val.restrictScalars ℚ)).fieldRange =
        abstractFixedField ℚ (SeparableClosure ℚ) H.field := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      change
        numberFieldEmbeddedLowerEmbedding
            (abstractFixedField ℚ (SeparableClosure ℚ) H.field)
            (abstractRelativeFixedField
              ℚ (SeparableClosure ℚ) P.below)
            ((abstractRelativeFixedField
              ℚ (SeparableClosure ℚ) P.below).val.restrictScalars ℚ) y ∈
          abstractFixedField ℚ (SeparableClosure ℚ) H.field
      rw [hi]
      exact y.property
    · intro hx
      refine ⟨⟨x, hx⟩, ?_⟩
      rw [hi]
      rfl
  rw [numberFieldEmbeddedBaseSubgroup, hRange]
  exact
    closedFixingSubgroup_abstractFixedField_eq
      ℚ (SeparableClosure ℚ) H.field

/-- The upper subgroup obtained from the canonical inclusion of an abstract
fixed-field tower is the original upper closed subgroup. -/
theorem
    numberFieldEmbeddedTopSubgroup_abstractFixedFieldInclusion
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field) :
    let F :=
      abstractFixedField ℚ (SeparableClosure ℚ) H.field
    let E :=
      abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below
    let j : E →ₐ[ℚ] SeparableClosure ℚ :=
      E.val.restrictScalars ℚ
    numberFieldEmbeddedTopSubgroup F E j = P.field := by
  dsimp only
  rw [numberFieldEmbeddedTopSubgroup]
  have hjRangeSelf :
      ((abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below).val.restrictScalars ℚ).fieldRange =
        (abstractRelativeFixedField
          ℚ (SeparableClosure ℚ) P.below).restrictScalars ℚ := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hjRange :
      ((abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below).val.restrictScalars ℚ).fieldRange =
        abstractFixedField ℚ (SeparableClosure ℚ) P.field := by
    exact hjRangeSelf.trans
      (IntermediateField.extendScalars_restrictScalars
        (abstractFixedField_le
          ℚ (SeparableClosure ℚ) P.below))
  rw [hjRange]
  exact
    closedFixingSubgroup_abstractFixedField_eq
      ℚ (SeparableClosure ℚ) P.field

/-- Transport a packaged rational norm-residue value directly from an equal
abstract base to the finite Galois extension underlying `P`.  Keeping the two
dependent transports in their own declaration prevents their elaboration cost
from accumulating in the main fixed-field comparison theorem. -/
theorem rationalFiniteNormResidueValue_transportToAbstractExtension
    {A : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)}
    (hAH : A = H)
    (L : FiniteGaloisSubextension A.field)
    (hLP :
      Eq.mp
          (congrArg
            (fun Y : FiniteAbstractField
                (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) =>
              FiniteGaloisSubextension Y.field)
            hAH)
          L =
        P.toFiniteGaloisExtension)
    {C X : Type} [AddGroup C] [AddGroup X]
    (eIdele : C ≃+
      ambientFixedAddSubgroup rationalIdeleClassRepresentation A.field)
    (eGalois : Additive (Abelianization L.extensionQuotient) ≃+ X)
    (c : C) :
    rationalFiniteNormResidueValue A L eIdele eGalois c =
      rationalFiniteNormResidueValue H P.toFiniteGaloisExtension
        (Eq.mp
          (congrArg
            (fun Y : FiniteAbstractField
                (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) =>
              C ≃+ ambientFixedAddSubgroup
                rationalIdeleClassRepresentation Y.field)
            hAH)
          eIdele)
        (abelianizedExtensionQuotientAddEquiv_transportExtension hLP
          (abelianizedExtensionQuotientAddEquiv_transportBase
            hAH L eGalois))
        c := by
  calc
    _ = rationalFiniteNormResidueValue H
        (Eq.mp
          (congrArg
            (fun Y : FiniteAbstractField
                (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) =>
              FiniteGaloisSubextension Y.field)
            hAH)
          L)
        (Eq.mp
          (congrArg
            (fun Y : FiniteAbstractField
                (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) =>
              C ≃+ ambientFixedAddSubgroup
                rationalIdeleClassRepresentation Y.field)
            hAH)
          eIdele)
        (abelianizedExtensionQuotientAddEquiv_transportBase hAH L eGalois)
        c :=
      rationalFiniteNormResidueValue_transportBase
        (A := A) (B := H) (C := C) (X := X)
        hAH L eIdele eGalois c
    _ = _ :=
      rationalFiniteNormResidueValue_transportExtension
        (K := H)
        (P := Eq.mp
          (congrArg
            (fun Y : FiniteAbstractField
                (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) =>
              FiniteGaloisSubextension Y.field)
            hAH)
          L)
        (Q := P.toFiniteGaloisExtension) (C := C) (X := X)
        hLP
        (Eq.mp
          (congrArg
            (fun Y : FiniteAbstractField
                (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) =>
              C ≃+ ambientFixedAddSubgroup
                rationalIdeleClassRepresentation Y.field)
            hAH)
          eIdele)
        (abelianizedExtensionQuotientAddEquiv_transportBase hAH L eGalois)
        c

/-- The packaged value at the literal fixed-field realization is the ambient
fixed-part norm-residue homomorphism evaluated at the same idele class. -/
private theorem rationalFiniteNormResidueValue_abstractFixedField_eq_ambient
    (c : IdeleClassGroup
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field)) :
    rationalFiniteNormResidueValue H P.toFiniteGaloisExtension
        (rationalAbstractFixedFieldIdeleClassEquivFixed H.field)
        (abstractFixedFieldAbelianizedExtensionQuotientEquivGaloisGroup H P)
        (Additive.ofMul c) =
      ambientFixedGlobalNormResidueAddMonoidHom H P
        (rationalAbstractFixedFieldIdeleClassEquivFixed
          H.field (Additive.ofMul c)) := by
  let eRec :=
    rationalCyclotomicDegreeData.normResidueSymbol
      rationalIdeleClassRepresentation
      rationalCyclotomicIdeleClassValuationData
      rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
      H P.toFiniteGaloisExtension
  let eGal :=
    abstractFixedFieldAbelianizedExtensionQuotientEquivGaloisGroup H P
  change
    eGal
        (eRec
          (finiteNormClass rationalIdeleClassRepresentation
            H.field P.field P.below
            (rationalAbstractFixedFieldIdeleClassEquivFixed
              H.field (Additive.ofMul c)))) =
      eGal
        (eRec
          (finiteNormClass rationalIdeleClassRepresentation
            H.field P.field P.below
            (rationalAbstractFixedFieldIdeleClassEquivFixed
              H.field (Additive.ofMul c))))
  rfl

/-- The packaged norm-residue value for the literal fixed-field realization
is the intrinsic abstract fixed-field norm-residue value. -/
theorem rationalFiniteNormResidueValue_abstractFixedField_apply
    (c : IdeleClassGroup
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field)) :
    Additive.toMul
        (rationalFiniteNormResidueValue H P.toFiniteGaloisExtension
          (rationalAbstractFixedFieldIdeleClassEquivFixed H.field)
          (abstractFixedFieldAbelianizedExtensionQuotientEquivGaloisGroup
            H P)
          (Additive.ofMul c)) =
      abstractFixedFieldGlobalNormResidueMonoidHom H P c := by
  let a :=
    rationalAbstractFixedFieldIdeleClassEquivFixed
      H.field (Additive.ofMul c)
  have hAbstract :=
    abstractFixedFieldGlobalNormResidueMonoidHom_fixed_apply H P a
  calc
    _ = Additive.toMul
        (ambientFixedGlobalNormResidueAddMonoidHom H P
          (rationalAbstractFixedFieldIdeleClassEquivFixed
            H.field (Additive.ofMul c))) := by
      exact congrArg Additive.toMul
        (rationalFiniteNormResidueValue_abstractFixedField_eq_ambient
          (H := H) (P := P) c)
    _ = _ := by
      simpa only [a, AddEquiv.symm_apply_apply, toMul_ofMul] using
        hAbstract.symm


end AbstractFixedFieldInclusion

end Reciprocity
end GlobalClassFieldTheory
