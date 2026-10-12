/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.CyclotomicAbstractFixedFieldArtinComparison


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

/-- The genuine cyclotomic maximal-unramified Artin map descended to
the idele class group of an abstract fixed field. -/
noncomputable def abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    IdeleClassGroup
        (LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field) →*
      Gal(
        LocalClassFieldTheory.abstractRelativeFixedField
          ℚ (SeparableClosure ℚ)
          (rationalCyclotomicFieldInertia_le H.field) /
        LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field) := by
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
  exact
    QuotientGroup.lift
      (IdeleGroup.principalSubgroup F)
      (infiniteGlobalArtinMonoidHom F U).toMonoidHom
      (by
        rintro _ ⟨x, rfl⟩
        exact
          infiniteGlobalArtinMonoidHom_abstractFixedFieldCyclotomic_principalIdele
            H x)

/-- Evaluation of the descended maximal-unramified Artin map on an
idele representative. -/
@[simp]
theorem abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom_mk
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
    abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom H
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup F) a) =
      infiniteGlobalArtinMonoidHom F U a := by
  rw [abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom]
  exact QuotientGroup.lift_mk _ _ _

/-- The descended genuine maximal-unramified Artin map is precisely
the normalized cyclotomic idele-class value in the actual Galois
coordinate. -/
theorem
    abstractFixedFieldCyclotomicGalEquivZHat_ideleClassArtinMonoidHom
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (c :
      IdeleClassGroup
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
    abstractFixedFieldCyclotomicGalEquivZHat H
        (abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom H c) =
      normalizedCyclotomicZHatIdeleClassValueContinuousMul F c := by
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H.field
  let : FiniteDimensional ℚ F :=
    LocalClassFieldTheory.abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) H.field H.finite
  let : NumberField F :=
    NumberField.of_module_finite ℚ F
  have hSeparableClosureAlgebra :
      cyclotomicAbstractFixedFieldArtin_separableClosureAlgebra =
        rationalSeparableClosureAlgebra :=
    Subsingleton.elim _ _
  cases hSeparableClosureAlgebra
  refine Quotient.inductionOn' c ?_
  intro a
  let hI :=
    rationalCyclotomicFieldInertia_le H.field
  let U :=
    LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) hI
  let : IsAbelianGalois F U :=
    abstractFixedFieldCyclotomic_isAbelianGalois H
  calc
    abstractFixedFieldCyclotomicGalEquivZHat H
        (abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom H
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup F) a)) =
        abstractFixedFieldCyclotomicGalEquivZHat H
          (infiniteGlobalArtinMonoidHom F U a) :=
      congrArg (abstractFixedFieldCyclotomicGalEquivZHat H)
        (abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom_mk H a)
    _ =
        normalizedCyclotomicZHatIdeleClassValueContinuousMul F
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup F) a) := by
      apply Multiplicative.ext
      exact
        abstractFixedFieldCyclotomicGalEquivZHat_infiniteGlobalArtinMonoidHom_mk
          H a

/-- The genuine chosen-local-factor Artin map to the cyclotomic
maximal-unramified extension is the abstract maximal-unramified
norm-residue symbol.  Both sides are characterized here by their
common normalized valuation coordinate, so no finite reciprocity
comparison is assumed. -/
theorem
    abstractFixedFieldCyclotomicIdeleClassArtin_eq_maximalUnramifiedNormResidue
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (a :
      ambientFixedAddSubgroup
        rationalIdeleClassRepresentation H.field) :
    let hI :=
      rationalCyclotomicFieldInertia_le H.field
    let hnormal :
        (CyclicCohomology.extensionSubgroup H.field
          (rationalCyclotomicDegreeData.fieldInertia H.field)
          hI).Normal := by
      rw [extensionSubgroup_rationalCyclotomicFieldInertia]
      infer_instance
    let qInertia :
        H.field.toSubgroup ⧸
            CyclicCohomology.extensionSubgroup H.field
              (rationalCyclotomicDegreeData.fieldInertia H.field)
              hI ≃*
          H.field.toSubgroup ⧸
            rationalCyclotomicDegreeData.fieldInertiaWithin H.field :=
      QuotientGroup.quotientMulEquivOfEq
        (extensionSubgroup_rationalCyclotomicFieldInertia H.field)
    abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom H
        (Additive.toMul
          ((rationalAbstractFixedFieldIdeleClassEquivFixed H.field
              (hfinite := H.finite)).symm
            a)) =
      LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
        ℚ (SeparableClosure ℚ) H.field
        (rationalCyclotomicDegreeData.fieldInertia H.field)
        hI hnormal
        (qInertia.symm
          (ValuationData.maximalUnramifiedNormResidueSymbol
            rationalCyclotomicIdeleClassValuationData H a).toMul) := by
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
  let hnormal :
      (CyclicCohomology.extensionSubgroup H.field
        (rationalCyclotomicDegreeData.fieldInertia H.field)
        hI).Normal := by
    rw [extensionSubgroup_rationalCyclotomicFieldInertia]
    infer_instance
  let qInertia :
      H.field.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup H.field
            (rationalCyclotomicDegreeData.fieldInertia H.field)
            hI ≃*
        H.field.toSubgroup ⧸
          rationalCyclotomicDegreeData.fieldInertiaWithin H.field :=
    QuotientGroup.quotientMulEquivOfEq
      (extensionSubgroup_rationalCyclotomicFieldInertia H.field)
  let c : IdeleClassGroup F :=
    Additive.toMul
      ((rationalAbstractFixedFieldIdeleClassEquivFixed H.field
          (hfinite := H.finite)).symm a)
  have hvaluation :
      ((rationalCyclotomicIdeleClassValuationData.valuationAt H a :
          rationalCyclotomicIdeleClassValuationData.valueGroup) : ZHat) =
        normalizedCyclotomicZHatIdeleClassValueContinuous F
          (Additive.ofMul c) := by
    simpa only [c, ofMul_toMul,
      (rationalAbstractFixedFieldIdeleClassEquivFixed H.field
        (hfinite := H.finite)).apply_symm_apply] using
      (rationalCyclotomicIdeleClassValuationData_valuationAt_fixed_apply
        H
        ((rationalAbstractFixedFieldIdeleClassEquivFixed H.field
          (hfinite := H.finite)).symm a))
  have hleft :
      Multiplicative.toAdd
        (abstractFixedFieldCyclotomicGalEquivZHat H
          (abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom H c)) =
        normalizedCyclotomicZHatIdeleClassValueContinuous F
          (Additive.ofMul c) :=
    congrArg Multiplicative.toAdd
      (abstractFixedFieldCyclotomicGalEquivZHat_ideleClassArtinMonoidHom H c)
  have hright :
      ((rationalCyclotomicIdeleClassValuationData.valuationAt H a :
          rationalCyclotomicIdeleClassValuationData.valueGroup) : ZHat) =
        Multiplicative.toAdd
          (abstractFixedFieldCyclotomicGalEquivZHat H
            (LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
              ℚ (SeparableClosure ℚ) H.field
              (rationalCyclotomicDegreeData.fieldInertia H.field)
              hI hnormal
              (qInertia.symm
                (ValuationData.maximalUnramifiedNormResidueSymbol
                  rationalCyclotomicIdeleClassValuationData H a).toMul))) := by
    rw [abstractFixedFieldCyclotomicGalEquivZHat_quotientClass]
    exact
      (ValuationData.maximalUnramifiedNormResidue_degree
        rationalCyclotomicIdeleClassValuationData H a).symm
  apply (abstractFixedFieldCyclotomicGalEquivZHat H).injective
  apply Multiplicative.ext
  exact hleft.trans (hvaluation.symm.trans hright)

/-- A prime idele class has genuine maximal-unramified Artin symbol
equal to the arithmetic Frobenius of its abstract fixed field. -/
theorem
    abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom_prime
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (π :
      ambientFixedAddSubgroup
        rationalIdeleClassRepresentation H.field)
    (hπ :
      rationalCyclotomicIdeleClassValuationData.IsPrimeElement H π) :
    let hI :=
      rationalCyclotomicFieldInertia_le H.field
    let hnormal :
        (CyclicCohomology.extensionSubgroup H.field
          (rationalCyclotomicDegreeData.fieldInertia H.field)
          hI).Normal := by
      rw [extensionSubgroup_rationalCyclotomicFieldInertia]
      infer_instance
    let qInertia :
        H.field.toSubgroup ⧸
            CyclicCohomology.extensionSubgroup H.field
              (rationalCyclotomicDegreeData.fieldInertia H.field)
              hI ≃*
          H.field.toSubgroup ⧸
            rationalCyclotomicDegreeData.fieldInertiaWithin H.field :=
      QuotientGroup.quotientMulEquivOfEq
        (extensionSubgroup_rationalCyclotomicFieldInertia H.field)
    abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom H
        (Additive.toMul
          ((rationalAbstractFixedFieldIdeleClassEquivFixed H.field
              (hfinite := H.finite)).symm
            π)) =
      LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
        ℚ (SeparableClosure ℚ) H.field
        (rationalCyclotomicDegreeData.fieldInertia H.field)
        hI hnormal
        (qInertia.symm
          (rationalCyclotomicDegreeData.frobenius
            (H.toFiniteResidueAbstractField
              rationalCyclotomicDegreeData))) := by
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
  let hnormal :
      (CyclicCohomology.extensionSubgroup H.field
        (rationalCyclotomicDegreeData.fieldInertia H.field)
        hI).Normal := by
    rw [extensionSubgroup_rationalCyclotomicFieldInertia]
    infer_instance
  let qInertia :
      H.field.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup H.field
            (rationalCyclotomicDegreeData.fieldInertia H.field)
            hI ≃*
        H.field.toSubgroup ⧸
          rationalCyclotomicDegreeData.fieldInertiaWithin H.field :=
    QuotientGroup.quotientMulEquivOfEq
      (extensionSubgroup_rationalCyclotomicFieldInertia H.field)
  let c :
      IdeleClassGroup F :=
    Additive.toMul
      ((rationalAbstractFixedFieldIdeleClassEquivFixed H.field
          (hfinite := H.finite)).symm π)
  have hvalue :
      normalizedCyclotomicZHatIdeleClassValueContinuous F
          ((rationalAbstractFixedFieldIdeleClassEquivFixed H.field
              (hfinite := H.finite)).symm
            π) =
        1 := by
    calc
      normalizedCyclotomicZHatIdeleClassValueContinuous F
          ((rationalAbstractFixedFieldIdeleClassEquivFixed H.field
              (hfinite := H.finite)).symm
            π) =
          ((rationalCyclotomicIdeleClassValuationData.valuationAt H
              (rationalAbstractFixedFieldIdeleClassEquivFixed H.field
                (hfinite := H.finite)
                ((rationalAbstractFixedFieldIdeleClassEquivFixed H.field
                    (hfinite := H.finite)).symm
                  π)) :
              rationalCyclotomicIdeleClassValuationData.valueGroup) :
            ZHat) := by
        exact
          (rationalCyclotomicIdeleClassValuationData_valuationAt_fixed_apply
            H
            ((rationalAbstractFixedFieldIdeleClassEquivFixed H.field
                (hfinite := H.finite)).symm
              π)).symm
      _ =
          ((rationalCyclotomicIdeleClassValuationData.oneValue :
              rationalCyclotomicIdeleClassValuationData.valueGroup) :
            ZHat) := by
        rw [(rationalAbstractFixedFieldIdeleClassEquivFixed H.field
          (hfinite := H.finite)).apply_symm_apply]
        exact congrArg Subtype.val hπ
      _ = 1 :=
        rationalCyclotomicIdeleClassValuationData.oneValue_coe
  apply (abstractFixedFieldCyclotomicGalEquivZHat H).injective
  calc
    abstractFixedFieldCyclotomicGalEquivZHat H
        (abstractFixedFieldCyclotomicIdeleClassArtinMonoidHom H c) =
        normalizedCyclotomicZHatIdeleClassValueContinuousMul F c :=
      abstractFixedFieldCyclotomicGalEquivZHat_ideleClassArtinMonoidHom
        H c
    _ = Multiplicative.ofAdd (1 : ZHat) := by
      apply Multiplicative.ext
      exact hvalue
    _ =
        abstractFixedFieldCyclotomicGalEquivZHat H
          (LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
            ℚ (SeparableClosure ℚ) H.field
            (rationalCyclotomicDegreeData.fieldInertia H.field)
            hI hnormal
            (qInertia.symm
              (rationalCyclotomicDegreeData.frobenius
                (H.toFiniteResidueAbstractField
                  rationalCyclotomicDegreeData)))) := by
      rw [
        abstractFixedFieldCyclotomicGalEquivZHat_quotientClass,
        rationalCyclotomicDegreeData.maximalUnramifiedDegreeEquiv_frobenius]

end Reciprocity
end GlobalClassFieldTheory
