/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalNormResidueNaturalityAbelianValues


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


private theorem
    abstractFixedFieldInclusionEmbeddedNormResidueValue_eq_transported
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (c : Additive
      (IdeleClassGroup
        (abstractFixedField ℚ (SeparableClosure ℚ) H.field))) :
    abstractFixedFieldInclusionEmbeddedNormResidueValue H P c =
      abstractFixedFieldInclusionTransportedNormResidueValue H P c := by
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
  let eIdeleEmbedded :=
    numberFieldEmbeddedIdeleClassEquivAmbientFixed F E j
  let eGaloisEmbedded :=
    numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup F E j
  simpa only [
    abstractFixedFieldInclusionEmbeddedNormResidueValue,
    abstractFixedFieldInclusionTransportedNormResidueValue,
    abstractFixedFieldInclusionTransportedAbelianizedEquiv,
    eIdeleEmbedded,
    eGaloisEmbedded] using
    (rationalFiniteNormResidueValue_transportToAbstractExtension
      (H := H) (P := P)
      (A := HEmbedded)
      (C := Additive (IdeleClassGroup F))
      (X := Additive Gal(E / F))
      hHEmbedded PEmbedded hPEmbedded
      eIdeleEmbedded eGaloisEmbedded c)

/-- A packaged finite norm-residue value depends only on the value of its
idele comparison at the chosen input and the value of its Galois comparison
at the resulting norm class. -/
private theorem rationalFiniteNormResidueValue_congr_apply
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteGaloisSubextension K.field)
    {C X : Type} [AddGroup C] [AddGroup X]
    (eIdele eIdele' : C ≃+
      ambientFixedAddSubgroup rationalIdeleClassRepresentation K.field)
    (eGalois eGalois' :
      Additive (Abelianization L.extensionQuotient) ≃+ X)
    (c : C)
    (heIdele : eIdele c = eIdele' c)
    (heGalois : ∀ z, eGalois z = eGalois' z) :
    rationalFiniteNormResidueValue K L eIdele eGalois c =
      rationalFiniteNormResidueValue K L eIdele' eGalois' c := by
  unfold rationalFiniteNormResidueValue
  rw [heIdele]
  exact heGalois _

/-- The transported packaged value is the intrinsic canonical packaged value;
only the idele input and the eventual abelianized value are compared. -/
private theorem
    abstractFixedFieldInclusionTransportedNormResidueValue_eq_canonical
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (c : Additive
      (IdeleClassGroup
        (abstractFixedField ℚ (SeparableClosure ℚ) H.field))) :
    abstractFixedFieldInclusionTransportedNormResidueValue H P c =
      abstractFixedFieldInclusionCanonicalNormResidueValue H P c := by
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
  simpa only [
    abstractFixedFieldInclusionTransportedNormResidueValue,
    abstractFixedFieldInclusionCanonicalNormResidueValue,
    eIdeleEmbedded,
    eIdeleOverH] using
    (rationalFiniteNormResidueValue_congr_apply
      H P.toFiniteGaloisExtension
      eIdeleOverH
      (rationalAbstractFixedFieldIdeleClassEquivFixed H.field)
      (abstractFixedFieldInclusionTransportedAbelianizedEquiv H P)
      (abstractFixedFieldAbelianizedExtensionQuotientEquivGaloisGroup H P)
      c
      (numberFieldEmbeddedIdeleClassEquivAmbientFixed_transport_apply H P c)
      (fun z => abstractFixedFieldInclusionTransportedAbelianizedValue_eq
        H P z))

/-- The explicitly embedded and intrinsic packaged norm-residue values agree. -/
private theorem
    abstractFixedFieldInclusionEmbeddedNormResidueValue_eq
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P : FiniteAbelianSubextension H.field)
    (c : Additive
      (IdeleClassGroup
        (abstractFixedField ℚ (SeparableClosure ℚ) H.field))) :
    abstractFixedFieldInclusionEmbeddedNormResidueValue H P c =
      abstractFixedFieldInclusionCanonicalNormResidueValue H P c :=
  (abstractFixedFieldInclusionEmbeddedNormResidueValue_eq_transported
    H P c).trans
    (abstractFixedFieldInclusionTransportedNormResidueValue_eq_canonical
      H P c)

/-- For the literal fixed fields attached to an abstract finite abelian
extension, the norm-residue map obtained from their canonical inclusion in
the rational separable closure is the intrinsic fixed-field norm-residue
map. -/
theorem
    globalNormResidueMonoidHomOfEmbedding_abstractFixedFieldInclusion
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
    globalNormResidueMonoidHomOfEmbedding F E j =
      abstractFixedFieldGlobalNormResidueMonoidHom H P := by
  dsimp only
  apply MonoidHom.ext
  intro c
  rw [globalNormResidueMonoidHomOfEmbedding_apply]
  change
    Additive.toMul
        (abstractFixedFieldInclusionEmbeddedNormResidueValue
          H P (Additive.ofMul c)) =
      abstractFixedFieldGlobalNormResidueMonoidHom H P c
  calc
    _ = Additive.toMul
        (abstractFixedFieldInclusionCanonicalNormResidueValue
          H P (Additive.ofMul c)) :=
      congrArg Additive.toMul
        (abstractFixedFieldInclusionEmbeddedNormResidueValue_eq
          H P (Additive.ofMul c))
    _ = _ := by
      simpa only [abstractFixedFieldInclusionCanonicalNormResidueValue] using
        (rationalFiniteNormResidueValue_abstractFixedField_apply
          (H := H) (P := P) c)

end AbstractFixedFieldInclusion


end Reciprocity
end GlobalClassFieldTheory
