/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.AbstractFixedFieldGlobalNormResidueFixedFields


set_option autoImplicit false


open scoped IsMulCommutative NumberField
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open GlobalClassFields
open KummerTheory
open AlgebraicNumberTheory
open LocalClassFieldTheory
open RamificationTheory

variable
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field)


attribute [local instance]
  abstractFixedFieldBaseQuotientFinite
  abstractFixedFieldRelativeQuotientFinite
  abstractFixedFieldRelativeQuotientIsMulCommutative
  abstractFixedFieldFiniteDimensional
  abstractRelativeFixedFieldFiniteDimensional
  abstractFixedFieldRelativeScalarTower
  abstractRelativeFixedFieldAbsoluteFiniteDimensional
  abstractFixedFieldNumberField
  abstractFixedFieldIdeleClassGroupIsMulCommutative
  abstractRelativeFixedFieldNumberField
  abstractRelativeFixedFieldIsGalois
  abstractRelativeFixedFieldIsAbelianGalois
  abstractFixedFieldIdeleClassNormRangeNormal

/-- The ambient fixed-part reciprocity value vanishes precisely when its
finite norm class vanishes. -/
private theorem ambientFixedGlobalNormResidueAddMonoidHom_eq_zero_iff
    (a :
      ambientFixedAddSubgroup
        rationalIdeleClassRepresentation K.field) :
    ambientFixedGlobalNormResidueAddMonoidHom K L a = 0 ↔
      finiteNormClass rationalIdeleClassRepresentation
        K.field L.field L.below a = 0 := by
  rw [ambientFixedGlobalNormResidueAddMonoidHom_apply]
  change
    abstractFixedFieldFiniteNormResidueGaloisEquiv K L
        (finiteNormClass rationalIdeleClassRepresentation
        K.field L.field L.below a) = 0 ↔
      finiteNormClass rationalIdeleClassRepresentation
        K.field L.field L.below a = 0
  exact
    (abstractFixedFieldFiniteNormResidueGaloisEquiv K L).map_eq_zero_iff

/-- The fixed-field idele-class comparison carries the abstract finite norm
subgroup exactly to the ordinary norm range. -/
private theorem
    rationalAbstractFixedFieldIdeleClassEquivFixed_mem_finiteNormSubgroup_iff
    (c : IdeleClassGroup
      (abstractFixedField ℚ (SeparableClosure ℚ) K.field)) :
    (rationalAbstractFixedFieldIdeleClassEquivFixed K.field)
          (Additive.ofMul c) ∈
        finiteNormSubgroup rationalIdeleClassRepresentation
          K.field L.field L.below ↔
      c ∈
        (_root_.ideleClassNorm
          (abstractFixedField ℚ (SeparableClosure ℚ) K.field)
          (abstractRelativeFixedField
            ℚ (SeparableClosure ℚ) L.below)).range := by
  let eK := rationalAbstractFixedFieldIdeleClassEquivFixed K.field
  let S :=
    finiteNormSubgroup rationalIdeleClassRepresentation
      K.field L.field L.below
  let N :=
    (_root_.ideleClassNorm
      (abstractFixedField ℚ (SeparableClosure ℚ) K.field)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below)).range
  have hmap :=
    map_rationalFiniteNormSubgroup_eq_ordinaryIdeleClassNormRange_concrete
      K.field L.field L.below L.normal
  have hmem :
      Additive.ofMul c ∈ S.map eK.symm.toAddMonoidHom ↔
        Additive.ofMul c ∈ N.toAddSubgroup :=
    Iff.of_eq (congrArg
      (fun T : AddSubgroup (Additive (IdeleClassGroup
        (abstractFixedField ℚ (SeparableClosure ℚ) K.field))) =>
        Additive.ofMul c ∈ T) hmap)
  change eK (Additive.ofMul c) ∈ S ↔ Additive.ofMul c ∈ N.toAddSubgroup
  constructor
  · intro hc
    have hmapped :
        Additive.ofMul c ∈ S.map eK.symm.toAddMonoidHom :=
      ⟨eK (Additive.ofMul c), hc, eK.symm_apply_apply _⟩
    exact hmem.mp hmapped
  · intro hc
    have hmapped :
        Additive.ofMul c ∈ S.map eK.symm.toAddMonoidHom := by
      exact hmem.mpr hc
    rcases hmapped with ⟨a, ha, hac⟩
    have hea : a = eK (Additive.ofMul c) :=
      (eK.apply_symm_apply a).symm.trans (congrArg eK hac)
    exact hea ▸ ha

/-- Triviality of the fixed-field norm-residue symbol is exactly
membership in the actual ordinary idele-class norm range. -/
@[simp]
theorem abstractFixedFieldGlobalNormResidueMonoidHom_eq_one_iff
    (c : IdeleClassGroup
      (abstractFixedField ℚ (SeparableClosure ℚ) K.field)) :
      abstractFixedFieldGlobalNormResidueMonoidHom K L c = 1 ↔
        c ∈
          (_root_.ideleClassNorm
            (abstractFixedField ℚ (SeparableClosure ℚ) K.field)
            (abstractRelativeFixedField
              ℚ (SeparableClosure ℚ) L.below)).range := by
  calc
    abstractFixedFieldGlobalNormResidueMonoidHom K L c = 1
        ↔ abstractFixedFieldGlobalNormResidueMonoidHom K L
            (Additive.toMul
              ((rationalAbstractFixedFieldIdeleClassEquivFixed K.field).symm
                ((rationalAbstractFixedFieldIdeleClassEquivFixed K.field)
                  (Additive.ofMul c)))) = 1 := by
          rw [(rationalAbstractFixedFieldIdeleClassEquivFixed
            K.field).symm_apply_apply]
          rfl
    _ ↔ Additive.toMul
          (ambientFixedGlobalNormResidueAddMonoidHom K L
            ((rationalAbstractFixedFieldIdeleClassEquivFixed K.field)
              (Additive.ofMul c))) = 1 := by
          exact Iff.of_eq (congrArg (fun g => g = 1)
            (abstractFixedFieldGlobalNormResidueMonoidHom_fixed_apply K L
              ((rationalAbstractFixedFieldIdeleClassEquivFixed K.field)
                (Additive.ofMul c))))
    _ ↔ ambientFixedGlobalNormResidueAddMonoidHom K L
          ((rationalAbstractFixedFieldIdeleClassEquivFixed K.field)
            (Additive.ofMul c)) = 0 :=
      toMul_eq_one
    _ ↔ finiteNormClass rationalIdeleClassRepresentation
          K.field L.field L.below
          ((rationalAbstractFixedFieldIdeleClassEquivFixed K.field)
            (Additive.ofMul c)) = 0 :=
      ambientFixedGlobalNormResidueAddMonoidHom_eq_zero_iff K L _
    _ ↔ (rationalAbstractFixedFieldIdeleClassEquivFixed K.field)
          (Additive.ofMul c) ∈
          finiteNormSubgroup rationalIdeleClassRepresentation
            K.field L.field L.below :=
      finiteNormClass_eq_zero_iff rationalIdeleClassRepresentation
        K.field L.field L.below _
    _ ↔ c ∈
          (_root_.ideleClassNorm
            (abstractFixedField ℚ (SeparableClosure ℚ) K.field)
            (abstractRelativeFixedField
              ℚ (SeparableClosure ℚ) L.below)).range :=
      rationalAbstractFixedFieldIdeleClassEquivFixed_mem_finiteNormSubgroup_iff
        K L c

/-- The ambient fixed-part reciprocity homomorphism is surjective. -/
private theorem ambientFixedGlobalNormResidueAddMonoidHom_surjective :
    Function.Surjective
      (ambientFixedGlobalNormResidueAddMonoidHom K L) := by
  intro y
  obtain ⟨z, hz⟩ :=
    (abstractFixedFieldFiniteNormResidueGaloisEquiv K L).surjective y
  obtain ⟨a, ha⟩ :=
    finiteNormClass_surjective rationalIdeleClassRepresentation
      K.field L.field L.below z
  refine ⟨a, ?_⟩
  rw [ambientFixedGlobalNormResidueAddMonoidHom_apply, ha]
  exact hz

/-- The fixed-field global norm-residue homomorphism is surjective
onto the actual Galois group. -/
theorem abstractFixedFieldGlobalNormResidueMonoidHom_surjective :
    Function.Surjective
      (abstractFixedFieldGlobalNormResidueMonoidHom K L) := by
  intro y
  obtain ⟨a, ha⟩ :=
    ambientFixedGlobalNormResidueAddMonoidHom_surjective K L
      (Additive.ofMul y)
  refine
    ⟨Additive.toMul
      ((rationalAbstractFixedFieldIdeleClassEquivFixed K.field).symm a), ?_⟩
  rw [abstractFixedFieldGlobalNormResidueMonoidHom_fixed_apply, ha]
  rfl


@[simp]
theorem abstractFixedFieldGlobalNormResidueMonoidHom_ker :
    (abstractFixedFieldGlobalNormResidueMonoidHom K L).ker =
      (_root_.ideleClassNorm
        (abstractFixedField ℚ (SeparableClosure ℚ) K.field)
        (abstractRelativeFixedField
          ℚ (SeparableClosure ℚ) L.below)).range := by
  ext c
  change
    abstractFixedFieldGlobalNormResidueMonoidHom K L c = 1 ↔
      c ∈
        (_root_.ideleClassNorm
          (abstractFixedField ℚ (SeparableClosure ℚ) K.field)
          (abstractRelativeFixedField
            ℚ (SeparableClosure ℚ) L.below)).range
  exact
    abstractFixedFieldGlobalNormResidueMonoidHom_eq_one_iff
      K L c

end Reciprocity
end GlobalClassFieldTheory
