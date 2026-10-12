/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.AbstractFixedFieldGlobalNormResidueEmbeddings


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

section EmbeddedNumberFieldRealization

variable
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]


attribute [local instance]
  numberFieldEmbeddedIdeleClassGroupIsMulCommutative
  numberFieldEmbeddedIdeleClassSubgroupNormal
  numberFieldEmbeddedExtensionSubgroupNormal
  numberFieldEmbeddedExtensionQuotientFinite
  numberFieldEmbeddedAbsoluteQuotientFinite
  numberFieldEmbeddedAbstractFixedFieldFiniteDimensional
  numberFieldEmbeddedAbstractRelativeFixedFieldFiniteDimensional
  numberFieldEmbeddedAbstractFixedFieldScalarTower
  numberFieldEmbeddedAbstractRelativeFixedFieldAbsoluteFiniteDimensional
  numberFieldEmbeddedAbstractFixedFieldNumberField
  numberFieldEmbeddedAbstractRelativeFixedFieldNumberField
  numberFieldEmbeddedAbstractRelativeFixedFieldRestrictScalarsFiniteDimensional
  numberFieldEmbeddedAbstractRelativeFixedFieldRestrictScalarsNumberField
  numberFieldEmbeddedAbstractRelativeFixedFieldRestrictScalarsAlgebra
  numberFieldEmbeddedAbstractRelativeFixedFieldIsGalois

private theorem numberFieldEmbeddedOrdinaryNormQuotientCongr_symm_mk
    {K₀ L₀ K₁ L₁ : Type}
    [Field K₀] [NumberField K₀]
    [Field L₀] [NumberField L₀] [Algebra K₀ L₀]
    [Field K₁] [NumberField K₁]
    [Field L₁] [NumberField L₁] [Algebra K₁ L₁]
    (eK : K₀ ≃ₐ[ℚ] K₁)
    (eL : L₀ ≃ₐ[ℚ] L₁)
    (h : ∀ x : K₀,
      eL (algebraMap K₀ L₀ x) =
        algebraMap K₁ L₁ (eK x))
    (c : IdeleClassGroup K₁) :
    (ordinaryIdeleClassNormQuotientCongrOfAlgEquiv eK eL h).symm
        (QuotientGroup.mk'
          (_root_.ideleClassNorm K₁ L₁).range c) =
      QuotientGroup.mk'
        (_root_.ideleClassNorm K₀ L₀).range
        ((ideleClassCongr eK).symm c) := by
  let e := ordinaryIdeleClassNormQuotientCongrOfAlgEquiv eK eL h
  apply e.injective
  rw [e.apply_symm_apply,
    ordinaryIdeleClassNormQuotientCongrOfAlgEquiv_mk,
    MulEquiv.apply_symm_apply]

private noncomputable def numberFieldEmbeddedFiniteNormClassPublicValue
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ)
    (a : ambientFixedAddSubgroup rationalIdeleClassRepresentation
      (numberFieldEmbeddedBaseSubgroup K L j)) :
    Additive
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) :=
    numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient
        K L j
        (finiteNormClass rationalIdeleClassRepresentation
          (numberFieldEmbeddedBaseSubgroup K L j)
          (numberFieldEmbeddedTopSubgroup K L j)
          (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j)
          a)

private noncomputable def numberFieldEmbeddedFiniteNormClassExpectedValue
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ)
    (a : ambientFixedAddSubgroup rationalIdeleClassRepresentation
      (numberFieldEmbeddedBaseSubgroup K L j)) :
    Additive
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) :=
  Additive.ofMul
    (QuotientGroup.mk'
      (_root_.ideleClassNorm K L).range
      (Additive.toMul
        ((numberFieldEmbeddedIdeleClassEquivAmbientFixed K L j).symm a)))

private noncomputable def
    numberFieldEmbeddedFiniteNormClassDirectComparisonValue
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ)
    (a : ambientFixedAddSubgroup rationalIdeleClassRepresentation
      (numberFieldEmbeddedBaseSubgroup K L j)) :
    Additive
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) := by
  let hnormal :=
    numberFieldEmbeddedExtensionSubgroupNormal K L j
  let H := numberFieldEmbeddedBaseSubgroup K L j
  let J := numberFieldEmbeddedTopSubgroup K L j
  let hJH :=
    numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j
  let fixedFieldEquiv :=
    rationalFiniteNormQuotientEquivIdeleClassNormQuotient
      H J hJH hnormal
  let actualFieldEquiv :=
    ordinaryIdeleClassNormQuotientCongrOfAlgEquiv
      (numberFieldEmbeddedAbstractBaseFieldEquiv K L j)
      (numberFieldEmbeddedAbstractTopFieldEquiv K L j)
      (numberFieldEmbeddedAbstractFieldEquiv_algebraMap K L j)
  exact
    MulEquiv.toAdditive actualFieldEquiv.symm
      (fixedFieldEquiv
        (finiteNormClass rationalIdeleClassRepresentation
          H J hJH a))

private theorem
    numberFieldEmbeddedFiniteNormClassPublicValue_eq_directComparison
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ)
    (a : ambientFixedAddSubgroup rationalIdeleClassRepresentation
      (numberFieldEmbeddedBaseSubgroup K L j)) :
    numberFieldEmbeddedFiniteNormClassPublicValue K L j a =
      numberFieldEmbeddedFiniteNormClassDirectComparisonValue K L j a := by
  unfold numberFieldEmbeddedFiniteNormClassPublicValue
  unfold numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient
  unfold numberFieldEmbeddedFiniteNormClassDirectComparisonValue
  rfl

private noncomputable def numberFieldEmbeddedActualNormClassRepresentativeValue
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ)
    (a : ambientFixedAddSubgroup rationalIdeleClassRepresentation
      (numberFieldEmbeddedBaseSubgroup K L j)) :
    Additive
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) := by
  let H := numberFieldEmbeddedBaseSubgroup K L j
  let hJH := numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j
  let F := abstractFixedField ℚ (SeparableClosure ℚ) H
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hJH
  let actualFieldEquiv :=
    ordinaryIdeleClassNormQuotientCongrOfAlgEquiv
      (numberFieldEmbeddedAbstractBaseFieldEquiv K L j)
      (numberFieldEmbeddedAbstractTopFieldEquiv K L j)
      (numberFieldEmbeddedAbstractFieldEquiv_algebraMap K L j)
  exact
    Additive.ofMul
      (actualFieldEquiv.symm
        (QuotientGroup.mk'
          (_root_.ideleClassNorm F E).range
          (Additive.toMul
            ((rationalAbstractFixedFieldIdeleClassEquivFixed H).symm a))))

private theorem
    numberFieldEmbeddedFiniteNormClassDirectComparison_eq_actualValue
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ)
    (a : ambientFixedAddSubgroup rationalIdeleClassRepresentation
      (numberFieldEmbeddedBaseSubgroup K L j)) :
    numberFieldEmbeddedFiniteNormClassDirectComparisonValue K L j a =
      numberFieldEmbeddedActualNormClassRepresentativeValue K L j a := by
  let hnormal := numberFieldEmbeddedExtensionSubgroupNormal K L j
  let H := numberFieldEmbeddedBaseSubgroup K L j
  let J := numberFieldEmbeddedTopSubgroup K L j
  let hJH := numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j
  let actualFieldEquiv :=
    ordinaryIdeleClassNormQuotientCongrOfAlgEquiv
      (numberFieldEmbeddedAbstractBaseFieldEquiv K L j)
      (numberFieldEmbeddedAbstractTopFieldEquiv K L j)
      (numberFieldEmbeddedAbstractFieldEquiv_algebraMap K L j)
  have hfixed :=
    rationalFiniteNormQuotientEquivIdeleClassNormQuotient_finiteNormClass
      H J hJH hnormal a
  unfold numberFieldEmbeddedFiniteNormClassDirectComparisonValue
  unfold numberFieldEmbeddedActualNormClassRepresentativeValue
  exact congrArg (MulEquiv.toAdditive actualFieldEquiv.symm) hfixed

private theorem numberFieldEmbeddedActualNormClassRepresentativeValue_eq_expected
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ)
    (a : ambientFixedAddSubgroup rationalIdeleClassRepresentation
      (numberFieldEmbeddedBaseSubgroup K L j)) :
    numberFieldEmbeddedActualNormClassRepresentativeValue K L j a =
      numberFieldEmbeddedFiniteNormClassExpectedValue K L j a := by
  let H := numberFieldEmbeddedBaseSubgroup K L j
  let hJH := numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j
  let F := abstractFixedField ℚ (SeparableClosure ℚ) H
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hJH
  let actualFieldEquiv :=
    ordinaryIdeleClassNormQuotientCongrOfAlgEquiv
      (numberFieldEmbeddedAbstractBaseFieldEquiv K L j)
      (numberFieldEmbeddedAbstractTopFieldEquiv K L j)
      (numberFieldEmbeddedAbstractFieldEquiv_algebraMap K L j)
  let c : IdeleClassGroup F :=
    Additive.toMul
      ((rationalAbstractFixedFieldIdeleClassEquivFixed H).symm a)
  unfold numberFieldEmbeddedActualNormClassRepresentativeValue
  unfold numberFieldEmbeddedFiniteNormClassExpectedValue
  change
    Additive.ofMul
        (actualFieldEquiv.symm
          (QuotientGroup.mk'
            (_root_.ideleClassNorm F E).range c)) =
      Additive.ofMul
        (QuotientGroup.mk'
          (_root_.ideleClassNorm K L).range
          ((ideleClassCongr
            (numberFieldEmbeddedAbstractBaseFieldEquiv K L j)).symm c))
  exact
    congrArg Additive.ofMul
      (numberFieldEmbeddedOrdinaryNormQuotientCongr_symm_mk
        (numberFieldEmbeddedAbstractBaseFieldEquiv K L j)
        (numberFieldEmbeddedAbstractTopFieldEquiv K L j)
        (numberFieldEmbeddedAbstractFieldEquiv_algebraMap K L j) c)

/-- On a finite norm-class representative, the explicit fixed-field
comparison is the genuine ordinary idele-class quotient. -/
@[simp]
theorem
    numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient_finiteNormClass
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ)
    (a : ambientFixedAddSubgroup rationalIdeleClassRepresentation
      (numberFieldEmbeddedBaseSubgroup K L j)) :
    numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient K L j
        (finiteNormClass rationalIdeleClassRepresentation
          (numberFieldEmbeddedBaseSubgroup K L j)
          (numberFieldEmbeddedTopSubgroup K L j)
          (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j) a) =
      Additive.ofMul
        (QuotientGroup.mk'
          (_root_.ideleClassNorm K L).range
          (Additive.toMul
            ((numberFieldEmbeddedIdeleClassEquivAmbientFixed K L j).symm a))) := by
  change
    numberFieldEmbeddedFiniteNormClassPublicValue K L j a =
      numberFieldEmbeddedFiniteNormClassExpectedValue K L j a
  exact
    (numberFieldEmbeddedFiniteNormClassPublicValue_eq_directComparison
      K L j a).trans
      ((numberFieldEmbeddedFiniteNormClassDirectComparison_eq_actualValue
        K L j a).trans
        (numberFieldEmbeddedActualNormClassRepresentativeValue_eq_expected
          K L j a))

/-- On an ordinary idele class, the explicit fixed-part realization
followed by the abstract finite norm-class map is the genuine quotient
class modulo the ordinary idele-class norm. -/
@[simp]
theorem
    numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient_ideleClass
    [FiniteDimensional K L] [IsGalois K L]
    (j : L →ₐ[ℚ] SeparableClosure ℚ)
    (c : IdeleClassGroup K) :
    numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient K L j
        (finiteNormClass rationalIdeleClassRepresentation
          (numberFieldEmbeddedBaseSubgroup K L j)
          (numberFieldEmbeddedTopSubgroup K L j)
          (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L j)
          (numberFieldEmbeddedIdeleClassEquivAmbientFixed
            K L j (Additive.ofMul c))) =
      Additive.ofMul
        (QuotientGroup.mk'
          (_root_.ideleClassNorm K L).range c) := by
  simpa only [AddEquiv.symm_apply_apply, toMul_ofMul] using
    (numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient_finiteNormClass
      K L j
      (numberFieldEmbeddedIdeleClassEquivAmbientFixed
        K L j (Additive.ofMul c)))


end EmbeddedNumberFieldRealization

end Reciprocity
end GlobalClassFieldTheory
