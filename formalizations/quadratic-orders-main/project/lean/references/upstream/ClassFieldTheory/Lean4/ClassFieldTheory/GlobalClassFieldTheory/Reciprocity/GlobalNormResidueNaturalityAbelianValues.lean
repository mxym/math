/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalNormResidueNaturalityExtensionValues


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


/-- The additive equivalence from the abelianized extension quotient to the
Galois group of the relative fixed field, transported through its embedding. -/
noncomputable def
    abstractFixedFieldInclusionTransportedAbelianizedEquiv
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field) :
    Additive
        (Abelianization
          P.toFiniteGaloisExtension.extensionQuotient) ≃+
      Additive
        (Gal(
          (abstractRelativeFixedField
            ℚ (SeparableClosure ℚ) P.below) /
          (abstractFixedField ℚ (SeparableClosure ℚ) H.field))) := by
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
    abelianizedExtensionQuotientAddEquiv_transportExtension hPEmbedded
      (abelianizedExtensionQuotientAddEquiv_transportBase
        hHEmbedded PEmbedded
        (numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup
          F E j))

/-- Canonical abelianization comparison built from the already transported
opaque extension-quotient endpoint. -/
private noncomputable def
    abstractFixedFieldInclusionTransportedCanonicalAbelianizedEquiv
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field) :
    Additive
        (Abelianization
          P.toFiniteGaloisExtension.extensionQuotient) ≃+
      Additive
        (Gal(
          (abstractRelativeFixedField
            ℚ (SeparableClosure ℚ) P.below) /
          (abstractFixedField ℚ (SeparableClosure ℚ) H.field))) := by
  let Q :=
    Gal(
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below) /
      (abstractFixedField ℚ (SeparableClosure ℚ) H.field))
  exact
    MulEquiv.toAdditive
      ((MulEquiv.abelianizationCongr
        (abstractFixedFieldInclusionTransportedExtensionQuotientEquiv H P)).trans
          (Abelianization.equivOfComm : Q ≃* Abelianization Q).symm)

/-- Pointwise opaque value of the transported abelianized equivalence. -/
private noncomputable def
    abstractFixedFieldInclusionTransportedAbelianizedValue
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (z : Additive
      (Abelianization P.toFiniteGaloisExtension.extensionQuotient)) :
    Additive
      (Gal(
        (abstractRelativeFixedField
          ℚ (SeparableClosure ℚ) P.below) /
        (abstractFixedField ℚ (SeparableClosure ℚ) H.field))) :=
  abstractFixedFieldInclusionTransportedAbelianizedEquiv H P z

/-- Pointwise opaque value of the canonical abelianization comparison built
from the transported quotient endpoint. -/
private noncomputable def
    abstractFixedFieldInclusionTransportedCanonicalAbelianizedValue
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (z : Additive
      (Abelianization P.toFiniteGaloisExtension.extensionQuotient)) :
    Additive
      (Gal(
        (abstractRelativeFixedField
          ℚ (SeparableClosure ℚ) P.below) /
        (abstractFixedField ℚ (SeparableClosure ℚ) H.field))) :=
  abstractFixedFieldInclusionTransportedCanonicalAbelianizedEquiv H P z

/-- Pointwise opaque value of the intrinsic abstract fixed-field
abelianization comparison. -/
private noncomputable def
    abstractFixedFieldInclusionCanonicalAbelianizedValue
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (z : Additive
      (Abelianization P.toFiniteGaloisExtension.extensionQuotient)) :
    Additive
      (Gal(
        (abstractRelativeFixedField
          ℚ (SeparableClosure ℚ) P.below) /
        (abstractFixedField ℚ (SeparableClosure ℚ) H.field))) :=
  abstractFixedFieldAbelianizedExtensionQuotientEquivGaloisGroup H P z

/-- The transported abelianized endpoint agrees pointwise with the canonical
abelianization comparison built from the transported quotient endpoint. -/
private theorem
    abstractFixedFieldInclusionTransportedAbelianizedValue_eq_canonical
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (z : Additive
      (Abelianization P.toFiniteGaloisExtension.extensionQuotient)) :
    abstractFixedFieldInclusionTransportedAbelianizedValue H P z =
      abstractFixedFieldInclusionTransportedCanonicalAbelianizedValue
        H P z := by
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
  let qEmbedded : PEmbedded.extensionQuotient ≃* Gal(E / F) :=
    numberFieldEmbeddedExtensionQuotientEquivGaloisGroup F E j
  have hCanonical :
      abstractFixedFieldInclusionTransportedAbelianizedEquiv H P =
        abstractFixedFieldInclusionTransportedCanonicalAbelianizedEquiv
          H P := by
    simpa only [
      abstractFixedFieldInclusionTransportedAbelianizedEquiv,
      abstractFixedFieldInclusionTransportedCanonicalAbelianizedEquiv,
      abstractFixedFieldInclusionTransportedExtensionQuotientEquiv,
      numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup,
      qEmbedded] using
      (abelianizedCanonicalEquiv_transportFiniteGalois
        hHEmbedded PEmbedded hPEmbedded qEmbedded)
  exact DFunLike.congr_fun hCanonical z

/-- On an abelianization representative, the transported canonical endpoint
is the additive value of the transported quotient endpoint. -/
private theorem
    abstractFixedFieldInclusionTransportedCanonicalAbelianizedValue_of
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (q : P.toFiniteGaloisExtension.extensionQuotient) :
    abstractFixedFieldInclusionTransportedCanonicalAbelianizedValue H P
        (Additive.ofMul (Abelianization.of q)) =
      Additive.ofMul
        (abstractFixedFieldInclusionTransportedExtensionQuotientValue
          H P q) := by
  simpa only [
    abstractFixedFieldInclusionTransportedCanonicalAbelianizedValue,
    abstractFixedFieldInclusionTransportedCanonicalAbelianizedEquiv,
    abstractFixedFieldInclusionTransportedExtensionQuotientValue] using
    (abelianizationCongrToComm_apply
      (abstractFixedFieldInclusionTransportedExtensionQuotientEquiv H P) q)

/-- On the same representative, the intrinsic fixed-field endpoint is the
additive value of the canonical quotient endpoint. -/
private theorem
    abstractFixedFieldInclusionCanonicalAbelianizedValue_of
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (q : P.toFiniteGaloisExtension.extensionQuotient) :
    abstractFixedFieldInclusionCanonicalAbelianizedValue H P
        (Additive.ofMul (Abelianization.of q)) =
      Additive.ofMul
        (abstractFixedFieldInclusionCanonicalExtensionQuotientValue
          H P q) := by
  let hRawQuotientCommGroup :
      CommGroup P.toFiniteGaloisExtension.extensionQuotient :=
    { (inferInstance :
        Group P.toFiniteGaloisExtension.extensionQuotient) with
      mul_comm := P.commutative.is_comm.comm }
  let qAbstractRaw :=
    abstractFixedFieldInclusionCanonicalExtensionQuotientEquiv H P
  change
    MulEquiv.toAdditive
        ((Abelianization.equivOfComm :
          P.toFiniteGaloisExtension.extensionQuotient ≃*
            Abelianization
              P.toFiniteGaloisExtension.extensionQuotient).symm.trans
          qAbstractRaw)
        (Additive.ofMul (Abelianization.of q)) =
      Additive.ofMul (qAbstractRaw q)
  exact commutativeAbelianizationEquiv_apply qAbstractRaw q

/-- The canonical abelianization comparison built after transport agrees
pointwise with the intrinsic abstract fixed-field comparison. -/
private theorem
    abstractFixedFieldInclusionTransportedCanonicalAbelianizedValue_eq
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (z : Additive
      (Abelianization P.toFiniteGaloisExtension.extensionQuotient)) :
    abstractFixedFieldInclusionTransportedCanonicalAbelianizedValue H P z =
      abstractFixedFieldInclusionCanonicalAbelianizedValue H P z := by
  let q : P.toFiniteGaloisExtension.extensionQuotient :=
    Quotient.out z.toMul
  have hz : Additive.ofMul (Abelianization.of q) = z := by
    apply Additive.ext
    exact Quotient.out_eq' z.toMul
  rw [← hz]
  calc
    _ = Additive.ofMul
        (abstractFixedFieldInclusionTransportedExtensionQuotientValue
          H P q) :=
      abstractFixedFieldInclusionTransportedCanonicalAbelianizedValue_of
        H P q
    _ = Additive.ofMul
        (abstractFixedFieldInclusionEmbeddedExtensionQuotientValue
          H P q) :=
      congrArg Additive.ofMul
        (abstractFixedFieldInclusionTransportedExtensionQuotientEquiv_apply
          H P q)
    _ = Additive.ofMul
        (abstractFixedFieldInclusionCanonicalExtensionQuotientValue
          H P q) :=
      congrArg Additive.ofMul
        (abstractFixedFieldInclusionExtensionQuotientEquiv_apply H P q)
    _ = _ :=
      (abstractFixedFieldInclusionCanonicalAbelianizedValue_of H P q).symm

/-- The transported abelianized equivalence agrees pointwise with the
intrinsic abstract fixed-field Galois comparison. -/
theorem
    abstractFixedFieldInclusionTransportedAbelianizedValue_eq
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (z : Additive
      (Abelianization P.toFiniteGaloisExtension.extensionQuotient)) :
    abstractFixedFieldInclusionTransportedAbelianizedValue H P z =
      abstractFixedFieldInclusionCanonicalAbelianizedValue H P z :=
  (abstractFixedFieldInclusionTransportedAbelianizedValue_eq_canonical
    H P z).trans
    (abstractFixedFieldInclusionTransportedCanonicalAbelianizedValue_eq
      H P z)


/-- The norm-residue value of an idele class in the Galois group of the
relative fixed field, computed through the embedded number-field realization. -/
noncomputable def
    abstractFixedFieldInclusionEmbeddedNormResidueValue
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (c : Additive
      (IdeleClassGroup
        (abstractFixedField ℚ (SeparableClosure ℚ) H.field))) :
    Additive
      (Gal(
        (abstractRelativeFixedField
          ℚ (SeparableClosure ℚ) P.below) /
        (abstractFixedField ℚ (SeparableClosure ℚ) H.field))) := by
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
  exact
    rationalFiniteNormResidueValue HEmbedded PEmbedded
      (numberFieldEmbeddedIdeleClassEquivAmbientFixed F E j)
      (numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup
        F E j)
      c

/-- Opaque packaged value after transporting both dependent structures to
the canonical `H` and `P` endpoints. -/
noncomputable def
    abstractFixedFieldInclusionTransportedNormResidueValue
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (c : Additive
      (IdeleClassGroup
        (abstractFixedField ℚ (SeparableClosure ℚ) H.field))) :
    Additive
      (Gal(
        (abstractRelativeFixedField
          ℚ (SeparableClosure ℚ) P.below) /
        (abstractFixedField ℚ (SeparableClosure ℚ) H.field))) := by
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) H.field
  let E :=
    abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below
  let j : E →ₐ[ℚ] SeparableClosure ℚ :=
    E.val.restrictScalars ℚ
  let HEmbedded :=
    numberFieldEmbeddedFiniteAbstractField F E j
  have hHEmbedded : HEmbedded = H :=
    numberFieldEmbeddedFiniteAbstractField_abstractFixedFieldInclusion H P
  let eIdeleEmbedded :=
    numberFieldEmbeddedIdeleClassEquivAmbientFixed F E j
  let eIdeleOverH :
      Additive (IdeleClassGroup F) ≃+
        ambientFixedAddSubgroup rationalIdeleClassRepresentation H.field :=
    Eq.mp
      (congrArg
        (fun X : FiniteAbstractField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) =>
          Additive (IdeleClassGroup F) ≃+
            ambientFixedAddSubgroup
              rationalIdeleClassRepresentation X.field)
        hHEmbedded)
      eIdeleEmbedded
  exact
    rationalFiniteNormResidueValue H P.toFiniteGaloisExtension
      eIdeleOverH
      (abstractFixedFieldInclusionTransportedAbelianizedEquiv H P)
      c

/-- Opaque intrinsic packaged norm-residue value at the canonical endpoints. -/
noncomputable def
    abstractFixedFieldInclusionCanonicalNormResidueValue
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (c : Additive
      (IdeleClassGroup
        (abstractFixedField ℚ (SeparableClosure ℚ) H.field))) :
    Additive
      (Gal(
        (abstractRelativeFixedField
          ℚ (SeparableClosure ℚ) P.below) /
        (abstractFixedField ℚ (SeparableClosure ℚ) H.field))) :=
  rationalFiniteNormResidueValue H P.toFiniteGaloisExtension
    (rationalAbstractFixedFieldIdeleClassEquivFixed H.field)
    (abstractFixedFieldAbelianizedExtensionQuotientEquivGaloisGroup H P)
    c


end AbstractFixedFieldInclusion

end Reciprocity
end GlobalClassFieldTheory
