/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.CyclotomicIdeleClassValuation
import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.InfiniteGlobalArtin
import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.MaximalUnramifiedReciprocity


set_option autoImplicit false


open scoped IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open KummerTheory


noncomputable local instance
    cyclotomicAbstractFixedFieldArtin_separableClosureAlgebra :
    Algebra ℚ (SeparableClosure ℚ) :=
  DivisionRing.toRatAlgebra

noncomputable local instance
    cyclotomicAbstractFixedFieldArtin_cyclotomicZHatFieldAlgebra :
    Algebra ℚ rationalCyclotomicZHatField :=
  DivisionRing.toRatAlgebra

/-- Cyclotomic field inertia is contained in the original abstract
field subgroup. -/
theorem rationalCyclotomicFieldInertia_le
    (H : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    (rationalCyclotomicDegreeData.fieldInertia H).toSubgroup ≤
      H.toSubgroup := by
  intro σ hσ
  exact hσ.1


theorem extensionSubgroup_rationalCyclotomicFieldInertia
    (H : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    CyclicCohomology.extensionSubgroup H
        (rationalCyclotomicDegreeData.fieldInertia H)
        (rationalCyclotomicFieldInertia_le H) =
      rationalCyclotomicDegreeData.fieldInertiaWithin H := by
  ext σ
  rw [
    mem_extensionSubgroup_iff,
    rationalCyclotomicDegreeData.mem_fieldInertiaWithin_iff,
    rationalCyclotomicDegreeData.mem_fieldInertia_iff]
  exact and_iff_right σ.2

/-- The actual Galois group of the cyclotomic maximal-unramified
extension of an abstract fixed field, in its normalized `ZHat`
coordinate. -/
noncomputable def abstractFixedFieldCyclotomicGalEquivZHat
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    let hI :=
      rationalCyclotomicFieldInertia_le H.field
    Gal(
        LocalClassFieldTheory.abstractRelativeFixedField
          ℚ (SeparableClosure ℚ) hI /
        LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field) ≃*
      Multiplicative ZHat := by
  let hI :=
    rationalCyclotomicFieldInertia_le H.field
  let hnormal :
      (CyclicCohomology.extensionSubgroup H.field
        (rationalCyclotomicDegreeData.fieldInertia H.field)
        hI).Normal := by
    rw [extensionSubgroup_rationalCyclotomicFieldInertia]
    infer_instance
  let qField :
      H.field.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup H.field
            (rationalCyclotomicDegreeData.fieldInertia H.field)
            hI ≃*
        Gal(
          LocalClassFieldTheory.abstractRelativeFixedField
            ℚ (SeparableClosure ℚ) hI /
          LocalClassFieldTheory.abstractFixedField
            ℚ (SeparableClosure ℚ) H.field) :=
    LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
      ℚ (SeparableClosure ℚ) H.field
      (rationalCyclotomicDegreeData.fieldInertia H.field)
      hI hnormal
  let qInertia :
      H.field.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup H.field
            (rationalCyclotomicDegreeData.fieldInertia H.field)
            hI ≃*
        H.field.toSubgroup ⧸
          rationalCyclotomicDegreeData.fieldInertiaWithin H.field :=
    QuotientGroup.quotientMulEquivOfEq
      (extensionSubgroup_rationalCyclotomicFieldInertia H.field)
  exact
    qField.symm.trans
      (qInertia.trans
        (rationalCyclotomicDegreeData.maximalUnramifiedDegreeEquiv
          (H.toFiniteResidueAbstractField
            rationalCyclotomicDegreeData)))

/-- On an absolute-Galois representative fixing the lower field, the
actual cyclotomic Galois coordinate is its normalized degree. -/
@[simp]
theorem abstractFixedFieldCyclotomicGalEquivZHat_extensionClass
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (σ : H.field.toSubgroup) :
    let hI :=
      rationalCyclotomicFieldInertia_le H.field
    let hnormal :
        (CyclicCohomology.extensionSubgroup H.field
          (rationalCyclotomicDegreeData.fieldInertia H.field)
          hI).Normal := by
      rw [extensionSubgroup_rationalCyclotomicFieldInertia]
      infer_instance
    abstractFixedFieldCyclotomicGalEquivZHat H
        (LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
          ℚ (SeparableClosure ℚ) H.field
          (rationalCyclotomicDegreeData.fieldInertia H.field)
          hI hnormal
          (QuotientGroup.mk σ)) =
      rationalCyclotomicDegreeData.normalizedDegree
        (H.toFiniteResidueAbstractField
          rationalCyclotomicDegreeData) σ := by
  let hI :=
    rationalCyclotomicFieldInertia_le H.field
  let hnormal :
      (CyclicCohomology.extensionSubgroup H.field
        (rationalCyclotomicDegreeData.fieldInertia H.field)
        hI).Normal := by
    rw [extensionSubgroup_rationalCyclotomicFieldInertia]
    infer_instance
  let qField :=
    LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
      ℚ (SeparableClosure ℚ) H.field
      (rationalCyclotomicDegreeData.fieldInertia H.field)
      hI hnormal
  change
    (rationalCyclotomicDegreeData.maximalUnramifiedDegreeEquiv
      (H.toFiniteResidueAbstractField
        rationalCyclotomicDegreeData))
      (QuotientGroup.quotientMulEquivOfEq
        (extensionSubgroup_rationalCyclotomicFieldInertia H.field)
        (qField.symm (qField (QuotientGroup.mk σ)))) =
      rationalCyclotomicDegreeData.normalizedDegree
        (H.toFiniteResidueAbstractField
          rationalCyclotomicDegreeData) σ
  rw [qField.symm_apply_apply]
  rfl

/-- Quotient-level evaluation of the actual cyclotomic Galois
coordinate. -/
@[simp]
theorem abstractFixedFieldCyclotomicGalEquivZHat_quotientClass
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (q :
      H.field.toSubgroup ⧸
        rationalCyclotomicDegreeData.fieldInertiaWithin H.field) :
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
    abstractFixedFieldCyclotomicGalEquivZHat H
        (LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
          ℚ (SeparableClosure ℚ) H.field
          (rationalCyclotomicDegreeData.fieldInertia H.field)
          hI hnormal
          (qInertia.symm q)) =
      rationalCyclotomicDegreeData.maximalUnramifiedDegreeEquiv
        (H.toFiniteResidueAbstractField
          rationalCyclotomicDegreeData) q := by
  let hI :=
    rationalCyclotomicFieldInertia_le H.field
  let hnormal :
      (CyclicCohomology.extensionSubgroup H.field
        (rationalCyclotomicDegreeData.fieldInertia H.field)
        hI).Normal := by
    rw [extensionSubgroup_rationalCyclotomicFieldInertia]
    infer_instance
  let qField :=
    LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
      ℚ (SeparableClosure ℚ) H.field
      (rationalCyclotomicDegreeData.fieldInertia H.field)
      hI hnormal
  let qInertia :
      H.field.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup H.field
            (rationalCyclotomicDegreeData.fieldInertia H.field)
            hI ≃*
        H.field.toSubgroup ⧸
          rationalCyclotomicDegreeData.fieldInertiaWithin H.field :=
    QuotientGroup.quotientMulEquivOfEq
      (extensionSubgroup_rationalCyclotomicFieldInertia H.field)
  change
    (rationalCyclotomicDegreeData.maximalUnramifiedDegreeEquiv
      (H.toFiniteResidueAbstractField
        rationalCyclotomicDegreeData))
      (qInertia
        (qField.symm
          (qField (qInertia.symm q)))) =
      rationalCyclotomicDegreeData.maximalUnramifiedDegreeEquiv
        (H.toFiniteResidueAbstractField
          rationalCyclotomicDegreeData) q
  rw [qField.symm_apply_apply, qInertia.apply_symm_apply]

/-- The extension fixed by cyclotomic field inertia is an actual
abelian Galois extension of the lower abstract fixed field. -/
theorem abstractFixedFieldCyclotomic_isAbelianGalois
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    let hI :=
      rationalCyclotomicFieldInertia_le H.field
    IsAbelianGalois
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hI) := by
  let hI :=
    rationalCyclotomicFieldInertia_le H.field
  let hnormal :
      (CyclicCohomology.extensionSubgroup H.field
        (rationalCyclotomicDegreeData.fieldInertia H.field)
        hI).Normal := by
    rw [extensionSubgroup_rationalCyclotomicFieldInertia]
    infer_instance
  let : IsGalois
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hI) :=
    LocalClassFieldTheory.abstractRelativeFixedField_isGalois
      ℚ (SeparableClosure ℚ) H.field
      (rationalCyclotomicDegreeData.fieldInertia H.field)
      hI hnormal
  let e :=
    abstractFixedFieldCyclotomicGalEquivZHat H
  exact
    { is_comm.comm := by
        intro σ τ
        apply e.injective
        simpa only [map_mul] using mul_comm (e σ) (e τ) }

/-- The rational cyclotomic `ZHat`-field embedded in the actual
maximal-unramified compositum of an abstract fixed field. -/
noncomputable def
    rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    let hI :=
      rationalCyclotomicFieldInertia_le H.field
    rationalCyclotomicZHatField →ₐ[ℚ]
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hI := by
  let hI :=
    rationalCyclotomicFieldInertia_le H.field
  let J :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ)
      (rationalCyclotomicDegreeData.fieldInertia H.field)
  have hTJ :
      rationalCyclotomicZHatField ≤ J := by
    change
      rationalCyclotomicZHatField ≤
        LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ)
          (rationalCyclotomicDegreeData.fieldInertia H.field)
    rw [
      rationalCyclotomicDegreeData_fixedField_fieldInertia]
    exact le_sup_right
  exact IntermediateField.inclusion hTJ

noncomputable instance
    abstractFixedFieldCyclotomicCompositum_algebra
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    let hI :=
      rationalCyclotomicFieldInertia_le H.field
    Algebra rationalCyclotomicZHatField
      (LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hI) :=
  ((rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum
    H).toRingHom).toAlgebra

instance abstractFixedFieldCyclotomicCompositum_scalarTower
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    let hI :=
      rationalCyclotomicFieldInertia_le H.field
    IsScalarTower ℚ rationalCyclotomicZHatField
      (LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hI) :=
  IsScalarTower.of_algebraMap_eq'
    ((rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum
      H).comp_algebraMap).symm

instance abstractFixedFieldCyclotomicCompositum_baseScalarTower
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    let hI :=
      rationalCyclotomicFieldInertia_le H.field
    IsScalarTower ℚ
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hI) := by
  let hI :=
    rationalCyclotomicFieldInertia_le H.field
  apply IsScalarTower.of_algebraMap_eq
  intro x
  apply Subtype.ext
  rfl

/-- Restriction from the actual maximal-unramified compositum of an
abstract fixed field to the rational cyclotomic factor. -/
noncomputable def abstractFixedFieldCyclotomicRestriction
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    let hI :=
      rationalCyclotomicFieldInertia_le H.field
    Gal(
        LocalClassFieldTheory.abstractRelativeFixedField
          ℚ (SeparableClosure ℚ) hI /
        LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field) →*
      Gal(rationalCyclotomicZHatField / ℚ) := by
  let hI :=
    rationalCyclotomicFieldInertia_le H.field
  exact
    IntermediateField.restrictRestrictAlgEquivMapHom
      ℚ rationalCyclotomicZHatField
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H.field)
      (LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hI)

/-- On a quotient representative, cyclotomic restriction of the
actual relative automorphism is ordinary restriction of the same
ambient absolute-Galois automorphism. -/
noncomputable local instance
    cyclotomicAbstractFixedFieldArtin_cyclotomicZHatFieldNormal :
    Normal ℚ rationalCyclotomicZHatField :=
  rationalCyclotomicZHatField_isNormal

@[simp]
theorem abstractFixedFieldCyclotomicRestriction_extensionClass
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (σ : H.field.toSubgroup) :
    let hI :=
      rationalCyclotomicFieldInertia_le H.field
    let hnormal :
        (CyclicCohomology.extensionSubgroup H.field
          (rationalCyclotomicDegreeData.fieldInertia H.field)
          hI).Normal := by
      rw [extensionSubgroup_rationalCyclotomicFieldInertia]
      infer_instance
    abstractFixedFieldCyclotomicRestriction H
        (LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
          ℚ (SeparableClosure ℚ) H.field
          (rationalCyclotomicDegreeData.fieldInertia H.field)
          hI hnormal
          (QuotientGroup.mk σ)) =
      AlgEquiv.restrictNormalHom
        rationalCyclotomicZHatField σ.1 := by
  let hI :=
    rationalCyclotomicFieldInertia_le H.field
  let hnormal :
      (CyclicCohomology.extensionSubgroup H.field
        (rationalCyclotomicDegreeData.fieldInertia H.field)
        hI).Normal := by
    rw [extensionSubgroup_rationalCyclotomicFieldInertia]
    infer_instance
  let τ :=
    LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
      ℚ (SeparableClosure ℚ) H.field
      (rationalCyclotomicDegreeData.fieldInertia H.field)
      hI hnormal
      (QuotientGroup.mk'
        (CyclicCohomology.extensionSubgroup H.field
          (rationalCyclotomicDegreeData.fieldInertia H.field) hI)
        σ)
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  let U :=
    LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) hI
  have hrestrict :
      algebraMap rationalCyclotomicZHatField U
          ((abstractFixedFieldCyclotomicRestriction H τ) x) =
        τ (algebraMap rationalCyclotomicZHatField U x) := by
    change
      algebraMap rationalCyclotomicZHatField U
          ((AlgEquiv.restrictNormal
            (MulSemiringAction.toAlgEquiv ℚ U τ)
            rationalCyclotomicZHatField) x) =
        (MulSemiringAction.toAlgEquiv ℚ U τ)
          (algebraMap rationalCyclotomicZHatField U x)
    exact
      AlgEquiv.restrictNormal_commutes
        (MulSemiringAction.toAlgEquiv ℚ U τ)
        rationalCyclotomicZHatField x
  have halgebraMap_eq_embedding
      (z : rationalCyclotomicZHatField) :
      algebraMap rationalCyclotomicZHatField U z =
        (rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum
          H z : U) := by
    rfl
  have hembedding_coe
      (z : rationalCyclotomicZHatField) :
      (((rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum
          H z : U) : SeparableClosure ℚ)) =
        (z : SeparableClosure ℚ) := by
    rfl
  have halgebraMap_coe
      (z : rationalCyclotomicZHatField) :
      ((algebraMap rationalCyclotomicZHatField U z : U) :
          SeparableClosure ℚ) =
        (z : SeparableClosure ℚ) := by
    rw [halgebraMap_eq_embedding]
    exact hembedding_coe z
  have hambient :=
    LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup_mk_apply_val
        ℚ (SeparableClosure ℚ) H.field
        (rationalCyclotomicDegreeData.fieldInertia H.field)
        hI hnormal σ
        (rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum
          H x)
  calc
    (((abstractFixedFieldCyclotomicRestriction H τ) x :
        rationalCyclotomicZHatField) :
        SeparableClosure ℚ) =
        ((τ
          (rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum
            H x) :
          LocalClassFieldTheory.abstractRelativeFixedField
            ℚ (SeparableClosure ℚ) hI) :
          SeparableClosure ℚ) := by
      calc
        (((abstractFixedFieldCyclotomicRestriction H τ) x :
            rationalCyclotomicZHatField) : SeparableClosure ℚ) =
            ((algebraMap rationalCyclotomicZHatField U
              ((abstractFixedFieldCyclotomicRestriction H τ) x) : U) :
              SeparableClosure ℚ) :=
          (halgebraMap_coe
            ((abstractFixedFieldCyclotomicRestriction H τ) x)).symm
        _ = ((τ (algebraMap rationalCyclotomicZHatField U x) : U) :
            SeparableClosure ℚ) :=
          congrArg (fun y : U => (y : SeparableClosure ℚ)) hrestrict
        _ = ((τ
            (rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum
              H x) : U) : SeparableClosure ℚ) := by
          rw [halgebraMap_eq_embedding]
    _ = σ.1 (x : SeparableClosure ℚ) := by
      calc
        ((τ
            (rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum
              H x) : U) : SeparableClosure ℚ) =
            σ.1
              ((rationalCyclotomicZHatFieldEmbeddingInAbstractFixedFieldCompositum
                H x : U) : SeparableClosure ℚ) := by
          simpa only [τ, U] using hambient.symm
        _ = σ.1 (x : SeparableClosure ℚ) := by
          rw [hembedding_coe]
    _ =
        (((AlgEquiv.restrictNormalHom
          rationalCyclotomicZHatField σ.1) x :
          rationalCyclotomicZHatField) :
          SeparableClosure ℚ) := by
      exact
        (AlgEquiv.restrictNormal_commutes
          σ.1 rationalCyclotomicZHatField x).symm

/-- Raw cyclotomic restriction is residue-degree multiplication of
the normalized actual Galois coordinate. -/
theorem
    abstractFixedFieldCyclotomicRestriction_coordinate
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (τ :
      Gal(
        LocalClassFieldTheory.abstractRelativeFixedField
          ℚ (SeparableClosure ℚ)
          (rationalCyclotomicFieldInertia_le H.field) /
        LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field)) :
    Multiplicative.toAdd
        (rationalCyclotomicZHatFieldGalEquivZHat
          (abstractFixedFieldCyclotomicRestriction H τ)) =
      (H.residueDegree rationalCyclotomicDegreeData : ℕ) •
        Multiplicative.toAdd
          (abstractFixedFieldCyclotomicGalEquivZHat H τ) := by
  let hI :=
    rationalCyclotomicFieldInertia_le H.field
  let hnormal :
      (CyclicCohomology.extensionSubgroup H.field
        (rationalCyclotomicDegreeData.fieldInertia H.field)
        hI).Normal := by
    rw [extensionSubgroup_rationalCyclotomicFieldInertia]
    infer_instance
  let qField :=
    LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
      ℚ (SeparableClosure ℚ) H.field
      (rationalCyclotomicDegreeData.fieldInertia H.field)
      hI hnormal
  obtain ⟨q, rfl⟩ := qField.surjective τ
  refine Quotient.inductionOn' q ?_
  intro σ
  rw [
    abstractFixedFieldCyclotomicRestriction_extensionClass,
    abstractFixedFieldCyclotomicGalEquivZHat_extensionClass]
  exact
    (rationalCyclotomicDegreeData.residueDegree_nsmul_normalizedDegree
        (H.toFiniteResidueAbstractField
          rationalCyclotomicDegreeData) σ).symm


end Reciprocity
end GlobalClassFieldTheory
