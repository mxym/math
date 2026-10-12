/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalNormResidueNaturalityFixedBase


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

/-- The finite abstract field reconstructed from the literal fixed-field
inclusion is the original packaged abstract field.  Keeping this structure
equality separate avoids repeatedly rebuilding all of its proof fields. -/
theorem
    numberFieldEmbeddedFiniteAbstractField_abstractFixedFieldInclusion
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
    numberFieldEmbeddedFiniteAbstractField F E j = H := by
  dsimp only
  exact FiniteAbstractField.eq_of_field_eq _ _
    (numberFieldEmbeddedBaseSubgroup_abstractFixedFieldInclusion H P)


theorem
    numberFieldEmbeddedIdeleClassEquivAmbientFixed_transport_apply
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (c : Additive
      (IdeleClassGroup
        (abstractFixedField ℚ (SeparableClosure ℚ) H.field))) :
    let F :=
      abstractFixedField ℚ (SeparableClosure ℚ) H.field
    let E :=
      abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below
    let j : E →ₐ[ℚ] SeparableClosure ℚ :=
      E.val.restrictScalars ℚ
    let HEmbedded :=
      numberFieldEmbeddedFiniteAbstractField F E j
    let hHEmbedded : HEmbedded = H :=
      numberFieldEmbeddedFiniteAbstractField_abstractFixedFieldInclusion H P
    Eq.mp
        (congrArg
          (fun X : FiniteAbstractField
              (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) =>
            Additive (IdeleClassGroup F) ≃+
              ambientFixedAddSubgroup
                rationalIdeleClassRepresentation X.field)
          hHEmbedded)
        (numberFieldEmbeddedIdeleClassEquivAmbientFixed F E j) c =
      rationalAbstractFixedFieldIdeleClassEquivFixed H.field c := by
  dsimp only
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
  have hHEmbedded :
      numberFieldEmbeddedFiniteAbstractField F E j = H :=
    numberFieldEmbeddedFiniteAbstractField_abstractFixedFieldInclusion H P
  have hFixedBase :
      abstractFixedField ℚ (SeparableClosure ℚ)
          (numberFieldEmbeddedBaseSubgroup F E j) = F :=
    congrArg
      (abstractFixedField ℚ (SeparableClosure ℚ)) hBase
  let eBase : F ≃ₐ[ℚ] F :=
    (numberFieldEmbeddedAbstractBaseFieldEquiv F E j).trans
      (IntermediateField.equivOfEq hFixedBase)
  have heBase :
      eBase = (AlgEquiv.refl : F ≃ₐ[ℚ] F) := by
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    change x.1 = x.1
    rfl
  let hEmbeddedQuotientFinite :=
    numberFieldEmbeddedAbsoluteQuotientFinite F E j
  let hEmbeddedFixedFiniteDimensional :=
    numberFieldEmbeddedAbstractFixedFieldFiniteDimensional F E j
  apply Subtype.ext
  rw [rationalAmbientFixedAddEquiv_transport_apply_val
    hHEmbedded
    (numberFieldEmbeddedIdeleClassEquivAmbientFixed F E j) c]
  dsimp only [numberFieldEmbeddedIdeleClassEquivAmbientFixed]
  simp only [AddEquiv.trans_apply]
  change
    ((rationalIdeleClassEquivFixed
        (abstractFixedField ℚ (SeparableClosure ℚ)
          (numberFieldEmbeddedBaseSubgroup F E j)))
      (MulEquiv.toAdditive
        (ideleClassCongr
          (numberFieldEmbeddedAbstractBaseFieldEquiv F E j)) c)).1 =
      ((rationalIdeleClassEquivFixed F) c).1
  exact rationalIdeleClassEquivFixed_congr_apply_val
    hFixedBase
    (numberFieldEmbeddedAbstractBaseFieldEquiv F E j)
    heBase c

/-- Transporting the finite Galois subextension reconstructed from the literal
fixed-field inclusion recovers the canonical subextension packaged by `P`.
This is the sole dependent structure equality used by the later quotient
comparisons. -/
theorem
    numberFieldEmbeddedFiniteGaloisSubextension_transport_eq
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
    let HEmbedded :=
      numberFieldEmbeddedFiniteAbstractField F E j
    let PEmbedded : FiniteGaloisSubextension HEmbedded.field :=
      numberFieldEmbeddedFiniteGaloisSubextension F E j
    let hHEmbedded : HEmbedded = H :=
      numberFieldEmbeddedFiniteAbstractField_abstractFixedFieldInclusion H P
    Eq.mp
        (congrArg
          (fun X : FiniteAbstractField
              (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) =>
            FiniteGaloisSubextension X.field)
          hHEmbedded)
        PEmbedded =
      P.toFiniteGaloisExtension := by
  dsimp only
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
  exact finiteGaloisSubextension_transport_eq_of_field_eq
    hHEmbedded PEmbedded P.toFiniteGaloisExtension
    (numberFieldEmbeddedTopSubgroup_abstractFixedFieldInclusion H P)

/-- Opaque endpoint for the extension-quotient comparison supplied by the
literal embedding.  Its domain is already the canonical quotient of `P`, so
no client has to reconstruct the two subgroup transports. -/
noncomputable def
    abstractFixedFieldInclusionEmbeddedExtensionQuotientEquiv
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
  have hBase :
      numberFieldEmbeddedBaseSubgroup F E j = H.field :=
    numberFieldEmbeddedBaseSubgroup_abstractFixedFieldInclusion H P
  have hTop :
      numberFieldEmbeddedTopSubgroup F E j = P.field :=
    numberFieldEmbeddedTopSubgroup_abstractFixedFieldInclusion H P
  letI hAlgebra : Algebra F (SeparableClosure ℚ) :=
    numberFieldEmbeddedSeparableClosureAlgebra F E j
  let eSep :=
    numberFieldEmbeddedSeparableClosureEquiv F E j
  letI hEmbeddedExtensionNormal :
      (CyclicCohomology.extensionSubgroup
        (numberFieldEmbeddedBaseSubgroup F E j)
        (numberFieldEmbeddedTopSubgroup F E j)
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup F E j)).Normal :=
    numberFieldEmbeddedExtensionSubgroup_normal F E j
  exact
    P.toFiniteGaloisExtension.extensionQuotientMulEquiv.trans
      ((extensionQuotientMulEquivOfEq
        hBase.symm hTop.symm P.below
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup F E j)).trans
      (ambientEmbeddedExtensionQuotientEquivGaloisGroup
        ℚ F E j eSep))

/-- Opaque canonical endpoint for the same quotient, obtained directly from
the abstract fixed-field realization. -/
noncomputable def
    abstractFixedFieldInclusionCanonicalExtensionQuotientEquiv
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field) :
    P.toFiniteGaloisExtension.extensionQuotient ≃*
      Gal(
        (abstractRelativeFixedField
          ℚ (SeparableClosure ℚ) P.below) /
        (abstractFixedField ℚ (SeparableClosure ℚ) H.field)) := by
  exact
    P.toFiniteGaloisExtension.extensionQuotientMulEquiv.trans
      (abstractExtensionQuotientEquivGaloisGroup
        ℚ (SeparableClosure ℚ)
        H.field P.field P.below P.normal)

/-- Pointwise opaque endpoint of the embedded quotient equivalence. -/
noncomputable def
    abstractFixedFieldInclusionEmbeddedExtensionQuotientValue
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (q : P.toFiniteGaloisExtension.extensionQuotient) :
    Gal(
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below) /
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field)) :=
  abstractFixedFieldInclusionEmbeddedExtensionQuotientEquiv H P q

/-- Pointwise opaque endpoint of the canonical quotient equivalence. -/
noncomputable def
    abstractFixedFieldInclusionCanonicalExtensionQuotientValue
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (q : P.toFiniteGaloisExtension.extensionQuotient) :
    Gal(
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below) /
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field)) :=
  abstractFixedFieldInclusionCanonicalExtensionQuotientEquiv H P q

/-- Fully applied ambient value of the embedded quotient endpoint. -/
noncomputable def
    abstractFixedFieldInclusionEmbeddedExtensionQuotientApplyVal
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (q : P.toFiniteGaloisExtension.extensionQuotient)
    (x : abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below) : SeparableClosure ℚ :=
  (abstractFixedFieldInclusionEmbeddedExtensionQuotientValue H P q x :
    SeparableClosure ℚ)

/-- Fully applied ambient value of the canonical quotient endpoint. -/
noncomputable def
    abstractFixedFieldInclusionCanonicalExtensionQuotientApplyVal
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (q : P.toFiniteGaloisExtension.extensionQuotient)
    (x : abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below) : SeparableClosure ℚ :=
  (abstractFixedFieldInclusionCanonicalExtensionQuotientValue H P q x :
    SeparableClosure ℚ)

/-- The ambient Galois value attached to a representative of the canonical
quotient, packaged behind a literal result type. -/
noncomputable def
    abstractFixedFieldInclusionAmbientEmbeddedQuotientMkValue
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (σ : H.field.toSubgroup) :
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
  have hBase :
      numberFieldEmbeddedBaseSubgroup F E j = H.field :=
    numberFieldEmbeddedBaseSubgroup_abstractFixedFieldInclusion H P
  letI hAlgebra : Algebra F (SeparableClosure ℚ) :=
    numberFieldEmbeddedSeparableClosureAlgebra F E j
  let eSep :=
    numberFieldEmbeddedSeparableClosureEquiv F E j
  letI hEmbeddedExtensionNormal :
      (CyclicCohomology.extensionSubgroup
        (numberFieldEmbeddedBaseSubgroup F E j)
        (numberFieldEmbeddedTopSubgroup F E j)
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup F E j)).Normal :=
    numberFieldEmbeddedExtensionSubgroup_normal F E j
  let σEmbedded :
      (numberFieldEmbeddedBaseSubgroup F E j).toSubgroup :=
    (MulEquiv.subgroupCongr
      (congrArg ClosedSubgroup.toSubgroup hBase.symm)) σ
  exact
    ambientEmbeddedExtensionQuotientEquivGaloisGroup
      ℚ F E j eSep (QuotientGroup.mk σEmbedded)

/-- Fully applied ambient value of the packaged representative endpoint. -/
noncomputable def
    abstractFixedFieldInclusionAmbientEmbeddedQuotientMkApplyVal
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (σ : H.field.toSubgroup)
    (x : abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below) : SeparableClosure ℚ :=
  (abstractFixedFieldInclusionAmbientEmbeddedQuotientMkValue H P σ x :
    SeparableClosure ℚ)

/-- Ambient action of the representative after rebundling it in the embedded
base subgroup. -/
noncomputable def
    abstractFixedFieldInclusionRebasedAutomorphismApplyVal
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (σ : H.field.toSubgroup)
    (x : abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below) : SeparableClosure ℚ := by
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
  exact σEmbedded.1.1 (x : SeparableClosure ℚ)


end AbstractFixedFieldInclusion

end Reciprocity
end GlobalClassFieldTheory
