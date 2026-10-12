/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalNormResidueNaturalityEmbeddedValues


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


section AbstractFixedFieldInclusion

variable
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)

attribute [local instance]
  naturalityIdeleClassCommGroup
  ideleClassGroupIsMulCommutative
  ideleClassSubgroupNormal
  naturalityAbstractFixedFieldBaseQuotientFinite
  naturalityAbstractFixedFieldRelativeQuotientFinite
  naturalityAbstractFixedFieldFiniteDimensional
  naturalityAbstractRelativeFixedFieldFiniteDimensional
  naturalityAbstractFixedFieldRelativeScalarTower
  naturalityAbstractRelativeFixedFieldAbsoluteFiniteDimensional
  naturalityAbstractFixedFieldNumberField
  naturalityAbstractRelativeFixedFieldNumberField
  naturalityAbstractRelativeFixedFieldIsGalois
  naturalityAbstractRelativeFixedFieldIsAbelianGalois

/-- The embedded quotient endpoint sends a canonical representative to the
packaged ambient value above. -/
private theorem
    abstractFixedFieldInclusionEmbeddedExtensionQuotientValue_mk
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (σ : H.field.toSubgroup) :
    abstractFixedFieldInclusionEmbeddedExtensionQuotientValue H P
        (P.toFiniteGaloisExtension.extensionQuotientMk σ) =
      abstractFixedFieldInclusionAmbientEmbeddedQuotientMkValue H P σ := by
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) H.field
  let E :=
    abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below
  let j : E →ₐ[ℚ] SeparableClosure ℚ :=
    E.val.restrictScalars ℚ
  have hBase :
      numberFieldEmbeddedBaseSubgroup F E j = H.field :=
    numberFieldEmbeddedBaseSubgroup_abstractFixedFieldInclusion H P
  have hTop :
      numberFieldEmbeddedTopSubgroup F E j = P.field :=
    numberFieldEmbeddedTopSubgroup_abstractFixedFieldInclusion H P
  let hAlgebra : Algebra F (SeparableClosure ℚ) :=
    numberFieldEmbeddedSeparableClosureAlgebra F E j
  let eSep :=
    numberFieldEmbeddedSeparableClosureEquiv F E j
  let hEmbeddedExtensionNormal :
      (CyclicCohomology.extensionSubgroup
        (numberFieldEmbeddedBaseSubgroup F E j)
        (numberFieldEmbeddedTopSubgroup F E j)
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup F E j)).Normal :=
    numberFieldEmbeddedExtensionSubgroup_normal F E j
  simp only [
    abstractFixedFieldInclusionEmbeddedExtensionQuotientValue,
    abstractFixedFieldInclusionEmbeddedExtensionQuotientEquiv,
    abstractFixedFieldInclusionAmbientEmbeddedQuotientMkValue,
    MulEquiv.trans_apply,
    FiniteGaloisSubextension.extensionQuotientMk_apply]
  exact congrArg
    (ambientEmbeddedExtensionQuotientEquivGaloisGroup ℚ F E j eSep)
    (extensionQuotientMulEquivOfEq_mk
      hBase.symm hTop.symm P.below
      (numberFieldEmbeddedTopSubgroup_le_baseSubgroup F E j) σ)

/-- The packaged ambient endpoint evaluates to the action of the rebundled
representative. -/
private theorem
    abstractFixedFieldInclusionAmbientEmbeddedQuotientMkApplyVal_eq_rebased
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (σ : H.field.toSubgroup)
    (x : abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below) :
    abstractFixedFieldInclusionAmbientEmbeddedQuotientMkApplyVal H P σ x =
      abstractFixedFieldInclusionRebasedAutomorphismApplyVal H P σ x := by
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) H.field
  let E :=
    abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below
  let j : E →ₐ[ℚ] SeparableClosure ℚ :=
    E.val.restrictScalars ℚ
  have hBase :
      numberFieldEmbeddedBaseSubgroup F E j = H.field :=
    numberFieldEmbeddedBaseSubgroup_abstractFixedFieldInclusion H P
  let hAlgebra : Algebra F (SeparableClosure ℚ) :=
    numberFieldEmbeddedSeparableClosureAlgebra F E j
  let eSep :=
    numberFieldEmbeddedSeparableClosureEquiv F E j
  let hEmbeddedExtensionNormal :
      (CyclicCohomology.extensionSubgroup
        (numberFieldEmbeddedBaseSubgroup F E j)
        (numberFieldEmbeddedTopSubgroup F E j)
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup F E j)).Normal :=
    numberFieldEmbeddedExtensionSubgroup_normal F E j
  let σEmbedded :
      (numberFieldEmbeddedBaseSubgroup F E j).toSubgroup :=
    (MulEquiv.subgroupCongr
      (congrArg ClosedSubgroup.toSubgroup hBase.symm)) σ
  have hmk :=
    ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk_apply
      ℚ F E j eSep σEmbedded x
  change
    (ambientEmbeddedExtensionQuotientEquivGaloisGroup
        ℚ F E j eSep (QuotientGroup.mk σEmbedded) x :
        SeparableClosure ℚ) =
      σEmbedded.1.1 (x : SeparableClosure ℚ) at hmk
  simpa only [
    abstractFixedFieldInclusionAmbientEmbeddedQuotientMkApplyVal,
    abstractFixedFieldInclusionAmbientEmbeddedQuotientMkValue,
    abstractFixedFieldInclusionRebasedAutomorphismApplyVal] using hmk

/-- Rebundling the representative does not change its action in the ambient
separable closure. -/
private theorem
    abstractFixedFieldInclusionRebasedAutomorphismApplyVal_eq
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (σ : H.field.toSubgroup)
    (x : abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below) :
    abstractFixedFieldInclusionRebasedAutomorphismApplyVal H P σ x =
      σ.1.1 (x : SeparableClosure ℚ) := by
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) H.field
  let E :=
    abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below
  let j : E →ₐ[ℚ] SeparableClosure ℚ :=
    E.val.restrictScalars ℚ
  have hBase :
      numberFieldEmbeddedBaseSubgroup F E j = H.field :=
    numberFieldEmbeddedBaseSubgroup_abstractFixedFieldInclusion H P
  let σEmbedded :
      (numberFieldEmbeddedBaseSubgroup F E j).toSubgroup :=
    (MulEquiv.subgroupCongr
      (congrArg ClosedSubgroup.toSubgroup hBase.symm)) σ
  have hσEmbedded :
      (σEmbedded.1 : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) = σ.1 :=
    closedSubgroupCongr_apply_val hBase.symm σ
  change σEmbedded.1.1 (x : SeparableClosure ℚ) = _
  rw [hσEmbedded]

/-- The packaged ambient representative acts by the original automorphism on
the underlying separable-closure value. -/
private theorem
    abstractFixedFieldInclusionAmbientEmbeddedQuotientMkValue_apply
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (σ : H.field.toSubgroup)
    (x : abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below) :
    abstractFixedFieldInclusionAmbientEmbeddedQuotientMkApplyVal H P σ x =
      σ.1.1 (x : SeparableClosure ℚ) := by
  exact
    (abstractFixedFieldInclusionAmbientEmbeddedQuotientMkApplyVal_eq_rebased
      H P σ x).trans
      (abstractFixedFieldInclusionRebasedAutomorphismApplyVal_eq H P σ x)

/-- Evaluation of the embedded quotient endpoint on a canonical quotient
representative, stated only in the ambient separable closure. -/
private theorem
    abstractFixedFieldInclusionEmbeddedExtensionQuotientEquiv_mk_val
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (σ : H.field.toSubgroup)
    (x : abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below) :
    abstractFixedFieldInclusionEmbeddedExtensionQuotientApplyVal H P
        (P.toFiniteGaloisExtension.extensionQuotientMk σ) x =
      σ.1.1 (x : SeparableClosure ℚ) := by
  calc
    _ = abstractFixedFieldInclusionAmbientEmbeddedQuotientMkApplyVal
        H P σ x := by
      exact congrArg
        (fun g => (g x : SeparableClosure ℚ))
        (abstractFixedFieldInclusionEmbeddedExtensionQuotientValue_mk
          H P σ)
    _ = _ :=
      abstractFixedFieldInclusionAmbientEmbeddedQuotientMkValue_apply
        H P σ x

/-- Evaluation of the canonical abstract quotient endpoint on a quotient
representative, again exposed only through its ambient value. -/
private theorem
    abstractFixedFieldInclusionCanonicalExtensionQuotientEquiv_mk_val
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (σ : H.field.toSubgroup)
    (x : abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below) :
    abstractFixedFieldInclusionCanonicalExtensionQuotientApplyVal H P
        (P.toFiniteGaloisExtension.extensionQuotientMk σ) x =
      σ.1.1 (x : SeparableClosure ℚ) := by
  simp only [
    abstractFixedFieldInclusionCanonicalExtensionQuotientApplyVal,
    abstractFixedFieldInclusionCanonicalExtensionQuotientValue,
    abstractFixedFieldInclusionCanonicalExtensionQuotientEquiv,
    MulEquiv.trans_apply,
    FiniteGaloisSubextension.extensionQuotientMk_apply]
  exact
    (abstractExtensionQuotientEquivGaloisGroup_mk_apply_val
      ℚ (SeparableClosure ℚ)
      H.field P.field P.below P.normal σ x).symm


theorem
    abstractFixedFieldInclusionExtensionQuotientEquiv_apply
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (q : P.toFiniteGaloisExtension.extensionQuotient) :
    abstractFixedFieldInclusionEmbeddedExtensionQuotientValue H P q =
      abstractFixedFieldInclusionCanonicalExtensionQuotientValue H P q := by
  refine P.toFiniteGaloisExtension.extensionQuotient_inductionOn
    (motive := fun q =>
      abstractFixedFieldInclusionEmbeddedExtensionQuotientValue H P q =
        abstractFixedFieldInclusionCanonicalExtensionQuotientValue H P q)
    q ?_
  intro σ
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  exact
    (abstractFixedFieldInclusionEmbeddedExtensionQuotientEquiv_mk_val
      H P σ x).trans
      (abstractFixedFieldInclusionCanonicalExtensionQuotientEquiv_mk_val
        H P σ x).symm


/-- The extension quotient identified with the Galois group of the corresponding
relative fixed field, after transporting the embedded field structures. -/
noncomputable def
    abstractFixedFieldInclusionTransportedExtensionQuotientEquiv
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field) :
    P.toFiniteGaloisExtension.extensionQuotient ≃*
      Gal(
        (abstractRelativeFixedField
          ℚ (SeparableClosure ℚ) P.below) /
        (abstractFixedField ℚ (SeparableClosure ℚ) H.field)) := by
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) H.field
  let E :=
    abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below
  let j : E →ₐ[ℚ] SeparableClosure ℚ :=
    E.val.restrictScalars ℚ
  let HEmbedded :=
    numberFieldEmbeddedFiniteAbstractField F E j
  let PEmbedded : FiniteGaloisSubextension HEmbedded.field :=
    numberFieldEmbeddedFiniteGaloisSubextension F E j
  have hHEmbedded : HEmbedded = H :=
    numberFieldEmbeddedFiniteAbstractField_abstractFixedFieldInclusion H P
  have hPEmbedded :
      Eq.mp
          (congrArg
            (fun X : FiniteAbstractField
                (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) =>
              FiniteGaloisSubextension X.field)
            hHEmbedded)
          PEmbedded =
        P.toFiniteGaloisExtension :=
    numberFieldEmbeddedFiniteGaloisSubextension_transport_eq H P
  exact
    (extensionQuotientMulEquiv_transportFiniteGalois
      hHEmbedded PEmbedded hPEmbedded).trans
      (numberFieldEmbeddedExtensionQuotientEquivGaloisGroup F E j)

/-- Pointwise opaque endpoint of the transported quotient equivalence. -/
noncomputable def
    abstractFixedFieldInclusionTransportedExtensionQuotientValue
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (q : P.toFiniteGaloisExtension.extensionQuotient) :
    Gal(
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below) /
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field)) :=
  abstractFixedFieldInclusionTransportedExtensionQuotientEquiv H P q


private theorem
    abstractFixedFieldInclusionTransportedExtensionQuotientValue_mk
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (σ : H.field.toSubgroup) :
    abstractFixedFieldInclusionTransportedExtensionQuotientValue H P
        (P.toFiniteGaloisExtension.extensionQuotientMk σ) =
      abstractFixedFieldInclusionEmbeddedExtensionQuotientValue H P
        (P.toFiniteGaloisExtension.extensionQuotientMk σ) := by
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) H.field
  let E :=
    abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below
  let j : E →ₐ[ℚ] SeparableClosure ℚ :=
    E.val.restrictScalars ℚ
  have hBase :
      numberFieldEmbeddedBaseSubgroup F E j = H.field :=
    numberFieldEmbeddedBaseSubgroup_abstractFixedFieldInclusion H P
  have hTop :
      numberFieldEmbeddedTopSubgroup F E j = P.field :=
    numberFieldEmbeddedTopSubgroup_abstractFixedFieldInclusion H P
  let HEmbedded :=
    numberFieldEmbeddedFiniteAbstractField F E j
  let PEmbedded : FiniteGaloisSubextension HEmbedded.field :=
    numberFieldEmbeddedFiniteGaloisSubextension F E j
  have hHEmbedded : HEmbedded = H :=
    numberFieldEmbeddedFiniteAbstractField_abstractFixedFieldInclusion H P
  have hPEmbedded :
      Eq.mp
          (congrArg
            (fun X : FiniteAbstractField
                (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) =>
              FiniteGaloisSubextension X.field)
            hHEmbedded)
          PEmbedded =
        P.toFiniteGaloisExtension :=
    numberFieldEmbeddedFiniteGaloisSubextension_transport_eq H P
  let hAlgebra : Algebra F (SeparableClosure ℚ) :=
    numberFieldEmbeddedSeparableClosureAlgebra F E j
  let eSep :=
    numberFieldEmbeddedSeparableClosureEquiv F E j
  let hEmbeddedExtensionNormal :
      (CyclicCohomology.extensionSubgroup
        (numberFieldEmbeddedBaseSubgroup F E j)
        (numberFieldEmbeddedTopSubgroup F E j)
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup F E j)).Normal :=
    numberFieldEmbeddedExtensionSubgroup_normal F E j
  have hFieldEq :
      (congrArg FiniteAbstractField.field hHEmbedded).symm = hBase.symm :=
    Subsingleton.elim _ _
  simp only [
    abstractFixedFieldInclusionTransportedExtensionQuotientValue,
    abstractFixedFieldInclusionEmbeddedExtensionQuotientValue,
    abstractFixedFieldInclusionTransportedExtensionQuotientEquiv,
    abstractFixedFieldInclusionEmbeddedExtensionQuotientEquiv,
    MulEquiv.trans_apply,
    extensionQuotientMulEquiv_transportFiniteGalois_mk,
    FiniteGaloisSubextension.extensionQuotientMk_apply,
    numberFieldEmbeddedExtensionQuotientEquivGaloisGroup]
  rw [hFieldEq]
  change
    ambientEmbeddedExtensionQuotientEquivGaloisGroup ℚ F E j eSep
        (QuotientGroup.mk
          ((MulEquiv.subgroupCongr
            (congrArg ClosedSubgroup.toSubgroup hBase.symm)) σ)) = _
  exact
    (congrArg
      (ambientEmbeddedExtensionQuotientEquivGaloisGroup ℚ F E j eSep)
      (extensionQuotientMulEquivOfEq_mk
        hBase.symm hTop.symm P.below
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup F E j) σ)).symm


theorem
    abstractFixedFieldInclusionTransportedExtensionQuotientEquiv_apply
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (q : P.toFiniteGaloisExtension.extensionQuotient) :
    abstractFixedFieldInclusionTransportedExtensionQuotientValue H P q =
      abstractFixedFieldInclusionEmbeddedExtensionQuotientValue H P q := by
  refine P.toFiniteGaloisExtension.extensionQuotient_inductionOn
    (motive := fun q =>
      abstractFixedFieldInclusionTransportedExtensionQuotientValue H P q =
        abstractFixedFieldInclusionEmbeddedExtensionQuotientValue H P q)
    q ?_
  intro σ
  exact abstractFixedFieldInclusionTransportedExtensionQuotientValue_mk
    H P σ


end AbstractFixedFieldInclusion

end Reciprocity
end GlobalClassFieldTheory
