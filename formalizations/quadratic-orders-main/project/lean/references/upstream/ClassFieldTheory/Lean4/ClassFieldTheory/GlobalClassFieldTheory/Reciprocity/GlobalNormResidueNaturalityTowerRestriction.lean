/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalNormResidueNaturalityTowerBase


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


section EmbeddedNumberFieldRestriction

variable
    (K K' L L' : Type)
    [Field K] [NumberField K]
    [Field K'] [NumberField K']
    [Field L] [NumberField L]
    [Field L'] [NumberField L']
    [Algebra K K'] [Algebra K L] [Algebra K L']
    [Algebra K' L'] [Algebra L L']
    [IsScalarTower K K' L'] [IsScalarTower K L L']

attribute [local instance]
  naturalityIdeleClassCommGroup
  ideleClassGroupIsMulCommutative
  ideleClassSubgroupNormal
  numberFieldEmbeddedBaseChangeExtensionSubgroupNormal
  numberFieldEmbeddedBaseChangeExtensionQuotientFinite
  numberFieldEmbeddedBaseChangeBaseFixedFieldFiniteDimensional
  numberFieldEmbeddedBaseChangeRelativeFixedFieldFiniteDimensional
  numberFieldEmbeddedBaseChangeRelativeFixedFieldScalarTower
  numberFieldEmbeddedBaseChangeRelativeFixedFieldAbsoluteFiniteDimensional
  numberFieldEmbeddedBaseChangeRelativeFixedFieldNumberField
  numberFieldEmbeddedBaseChangeRelativeFixedFieldIsGalois

/-- In one common rational-separable-closure realization, the canonical
quotient-to-Galois comparisons intertwine abstract restriction with
ordinary restriction of the actual number-field automorphisms. -/
theorem
    numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup_restriction
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [FiniteDimensional K' L'] [IsAbelianGalois K' L']
    (j : L' →ₐ[ℚ] SeparableClosure ℚ)
    (z :
      Abelianization
        (numberFieldEmbeddedFiniteGaloisSubextension
          K' L' j).extensionQuotient) :
    let jLower : L →ₐ[ℚ] SeparableClosure ℚ :=
      j.comp (IsScalarTower.toAlgHom ℚ L L')
    let H :=
      numberFieldEmbeddedBaseSubgroup K L jLower
    let H' :=
      numberFieldEmbeddedBaseSubgroup K' L' j
    let J :=
      numberFieldEmbeddedTopSubgroup K L jLower
    let J' :=
      numberFieldEmbeddedTopSubgroup K' L' j
    let hH'H :=
      numberFieldEmbeddedBaseSubgroup_le_of_tower K K' L L' j
    let hJ'J :=
      numberFieldEmbeddedTopSubgroup_le_of_tower K K' L L' j
    let hJH :=
      numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L jLower
    let hJ'H' :=
      numberFieldEmbeddedTopSubgroup_le_baseSubgroup K' L' j
    letI _ :
        (CyclicCohomology.extensionSubgroup H J hJH).Normal :=
      numberFieldEmbeddedExtensionSubgroup_normal K L jLower
    letI _ :
        (CyclicCohomology.extensionSubgroup H' J' hJ'H').Normal :=
      numberFieldEmbeddedExtensionSubgroup_normal K' L' j
    ((AlgEquiv.restrictNormalHom L).comp
        (AlgEquiv.restrictScalarsHom K))
        (Additive.toMul
          (numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup
            K' L' j (Additive.ofMul z))) =
      Additive.toMul
        (numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup
          K L jLower
          (MonoidHom.toAdditive
            (normResidueNaturalityAbelianizedRestriction
              H H' J J'
              hJH hJ'H'
              hH'H hJ'J)
            (Additive.ofMul z))) := by
  dsimp only
  let jLower : L →ₐ[ℚ] SeparableClosure ℚ :=
    j.comp (IsScalarTower.toAlgHom ℚ L L')
  let H :=
    numberFieldEmbeddedBaseSubgroup K L jLower
  let H' :=
    numberFieldEmbeddedBaseSubgroup K' L' j
  let J :=
    numberFieldEmbeddedTopSubgroup K L jLower
  let J' :=
    numberFieldEmbeddedTopSubgroup K' L' j
  let hH'H :=
    numberFieldEmbeddedBaseSubgroup_le_of_tower K K' L L' j
  let hJ'J :=
    numberFieldEmbeddedTopSubgroup_le_of_tower K K' L L' j
  let hJH :=
    numberFieldEmbeddedTopSubgroup_le_baseSubgroup
      K L jLower
  let hJ'H' :=
    numberFieldEmbeddedTopSubgroup_le_baseSubgroup
      K' L' j
  let hLowerNormal :
      (CyclicCohomology.extensionSubgroup H J hJH).Normal :=
    numberFieldEmbeddedExtensionSubgroup_normal K L jLower
  let hUpperNormal :
      (CyclicCohomology.extensionSubgroup H' J' hJ'H').Normal :=
    numberFieldEmbeddedExtensionSubgroup_normal K' L' j
  let qLower :=
    numberFieldEmbeddedExtensionQuotientEquivGaloisGroup
      K L jLower
  let qUpper :=
    numberFieldEmbeddedExtensionQuotientEquivGaloisGroup
      K' L' j
  let qLowerRaw :
      (H.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup H J hJH) ≃*
        Gal(L / K) := by
    exact
      { qLower.toEquiv with
        map_mul' := fun x y => qLower.map_mul x y }
  let qUpperRaw :
      (H'.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup H' J' hJ'H') ≃*
        Gal(L' / K') := by
    exact
      { qUpper.toEquiv with
        map_mul' := fun x y => qUpper.map_mul x y }
  let restrictActual :
      Gal(L' / K') →* Gal(L / K) :=
    (AlgEquiv.restrictNormalHom L).comp
      (AlgEquiv.restrictScalarsHom K)
  obtain ⟨q, rfl⟩ :=
    QuotientGroup.mk_surjective z
  obtain ⟨σ, rfl⟩ :=
    (numberFieldEmbeddedFiniteGaloisSubextension
      K' L' j).extensionQuotientMk_surjective q
  change
    restrictActual
        ((Abelianization.equivOfComm (H := Gal(L' / K'))).symm
          (qUpperRaw.abelianizationCongr
            (Abelianization.of (QuotientGroup.mk σ)))) =
      (Abelianization.equivOfComm (H := Gal(L / K))).symm
        (qLowerRaw.abelianizationCongr
          (normResidueNaturalityAbelianizedRestriction
            H H' J J' hJH hJ'H' hH'H hJ'J
            (Abelianization.of (QuotientGroup.mk σ))))
  rw [normResidueNaturalityAbelianizedRestriction_of_mk,
    abelianizationCongr_of, abelianizationCongr_of]
  change
    restrictActual (qUpperRaw (QuotientGroup.mk σ)) =
      qLowerRaw
        (QuotientGroup.mk (Subgroup.inclusion hH'H σ))
  apply AlgEquiv.ext
  intro x
  apply jLower.injective
  let hUpperAlgebra : Algebra K' (SeparableClosure ℚ) :=
    numberFieldEmbeddedSeparableClosureAlgebra K' L' j
  let eUpper :=
    numberFieldEmbeddedSeparableClosureEquiv K' L' j
  let hLowerAlgebra : Algebra K (SeparableClosure ℚ) :=
    numberFieldEmbeddedSeparableClosureAlgebra K L jLower
  let eLower :=
    numberFieldEmbeddedSeparableClosureEquiv K L jLower
  calc
    jLower
        (restrictActual
          (qUpperRaw (QuotientGroup.mk σ)) x) =
        j
          ((qUpperRaw (QuotientGroup.mk σ))
            (algebraMap L L' x)) := by
      exact congrArg j
        (AlgEquiv.restrictNormal_commutes
          ((AlgEquiv.restrictScalarsHom K)
            (qUpperRaw (QuotientGroup.mk σ)))
          L x)
    _ = σ.1.1
        (j (algebraMap L L' x)) := by
      exact
        ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk_apply
          ℚ K' L' j eUpper σ (algebraMap L L' x)
    _ = (Subgroup.inclusion hH'H σ).1.1
        (jLower x) := rfl
    _ = jLower
        (qLowerRaw
          (QuotientGroup.mk
            (Subgroup.inclusion hH'H σ)) x) := by
      exact
        (ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk_apply
          ℚ K L jLower eLower
          (Subgroup.inclusion hH'H σ) x).symm

/-- In a compatible common embedding, the fixed-part relative norm
between two (Galois-related) base fields is the genuine ordinary
idele-class norm. -/
theorem numberFieldEmbeddedIdeleClassEquivAmbientFixed_relativeNorm
    [FiniteDimensional K K'] [IsGalois K K']
    (j : L' →ₐ[ℚ] SeparableClosure ℚ)
    (c : IdeleClassGroup K') :
    let jLower : L →ₐ[ℚ] SeparableClosure ℚ :=
      j.comp (IsScalarTower.toAlgHom ℚ L L')
    let H :=
      numberFieldEmbeddedBaseSubgroup K L jLower
    let H' :=
      numberFieldEmbeddedBaseSubgroup K' L' j
    let hH'H :=
      numberFieldEmbeddedBaseSubgroup_le_of_tower K K' L L' j
    letI _ : Finite
        (H.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup H H' hH'H) :=
      numberFieldEmbeddedBaseChangeExtensionQuotientFinite
        K K' L L' j
    relativeNorm rationalIdeleClassRepresentation H H' hH'H
        (numberFieldEmbeddedIdeleClassEquivAmbientFixed
          K' L' j (Additive.ofMul c)) =
      numberFieldEmbeddedIdeleClassEquivAmbientFixed
        K L jLower
        (Additive.ofMul (_root_.ideleClassNorm K K' c)) := by
  intro jLower H H'
  let hH'H :=
    numberFieldEmbeddedBaseSubgroup_le_of_tower K K' L L' j
  let hnormal :=
    numberFieldEmbeddedBaseChangeExtensionSubgroupNormal K K' L L' j
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) H
  let E :=
    abstractRelativeFixedField ℚ (SeparableClosure ℚ) hH'H
  let _ :
      (CyclicCohomology.extensionSubgroup H H' hH'H).Normal :=
    hnormal
  let _ :
      Finite
        (H.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup H H' hH'H) :=
    numberFieldEmbeddedBaseChangeExtensionQuotientFinite
      K K' L L' j
  let _ :
      Finite
        ((baseField
          (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
          CyclicCohomology.extensionSubgroup
            (baseField
              (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
            H (le_baseField H)) :=
    numberFieldEmbeddedAbsoluteQuotientFinite K L jLower
  let _ : NumberField F :=
    numberFieldEmbeddedAbstractFixedFieldNumberField K L jLower
  let _ : NumberField E :=
    numberFieldEmbeddedBaseChangeRelativeFixedFieldNumberField
      K K' L L' j
  let _ : FiniteDimensional ℚ (E.restrictScalars ℚ) := by
    change FiniteDimensional ℚ E
    exact
      numberFieldEmbeddedBaseChangeRelativeFixedFieldAbsoluteFiniteDimensional
        K K' L L' j
  let _ : NumberField
      (abstractFixedField ℚ (SeparableClosure ℚ) H') :=
    numberFieldEmbeddedAbstractFixedFieldNumberField K' L' j
  have hE :
      E.restrictScalars ℚ =
        abstractFixedField ℚ (SeparableClosure ℚ) H' :=
    IntermediateField.extendScalars_restrictScalars
      (abstractFixedField_le
        ℚ (SeparableClosure ℚ) hH'H)
  let eRel :
      E ≃ₐ[ℚ]
        abstractFixedField ℚ (SeparableClosure ℚ) H' :=
    IntermediateField.equivOfEq hE
  let eK :
      K ≃ₐ[ℚ] F :=
    numberFieldEmbeddedAbstractBaseFieldEquiv K L jLower
  let eK'Base :
      K' ≃ₐ[ℚ]
        abstractFixedField ℚ (SeparableClosure ℚ) H' :=
    numberFieldEmbeddedAbstractBaseFieldEquiv K' L' j
  let eK' : K' ≃ₐ[ℚ] E :=
    eK'Base.trans eRel.symm
  have hcompat (x : K) :
      eK' (algebraMap K K' x) =
        algebraMap F E (eK x) := by
    apply eRel.injective
    apply Subtype.ext
    change
      j (algebraMap K' L' (algebraMap K K' x)) =
        j (algebraMap L L' (algebraMap K L x))
    rw [← IsScalarTower.algebraMap_apply K K' L',
      ← IsScalarTower.algebraMap_apply K L L']
  have hupper :
      rationalAbstractRelativeFixedFieldIdeleClassEquivFixed
          H H' hH'H
          (Additive.ofMul (ideleClassCongr eK' c)) =
        numberFieldEmbeddedIdeleClassEquivAmbientFixed
          K' L' j (Additive.ofMul c) := by
    apply Subtype.ext
    change
      ((rationalIdeleClassEquivFixed (E.restrictScalars ℚ))
          (Additive.ofMul (ideleClassCongr eK' c))).1 =
        ((rationalIdeleClassEquivFixed
            (abstractFixedField ℚ (SeparableClosure ℚ) H'))
          (Additive.ofMul (ideleClassCongr eK'Base c))).1
    exact rationalIdeleClassEquivFixed_transport_baseEquiv_val
      (T := K') (A := E.restrictScalars ℚ)
      (B := abstractFixedField ℚ (SeparableClosure ℚ) H') hE eK'Base c
  have hrelative :=
    rationalAbstractRelativeFixedFieldIdeleClassEquivFixed_relativeNorm
      H H' hH'H hnormal
        (Additive.ofMul (ideleClassCongr eK' c))
  change
    relativeNorm rationalIdeleClassRepresentation H H' hH'H
        (rationalAbstractRelativeFixedFieldIdeleClassEquivFixed
          H H' hH'H
          (Additive.ofMul (ideleClassCongr eK' c))) =
      rationalAbstractFixedFieldIdeleClassEquivFixed H
        (Additive.ofMul
          (_root_.ideleClassNorm F E
            (ideleClassCongr eK' c)))
    at hrelative
  calc
    relativeNorm rationalIdeleClassRepresentation H H' hH'H
        (numberFieldEmbeddedIdeleClassEquivAmbientFixed
          K' L' j (Additive.ofMul c)) =
      relativeNorm rationalIdeleClassRepresentation H H' hH'H
        (rationalAbstractRelativeFixedFieldIdeleClassEquivFixed
          H H' hH'H (Additive.ofMul (ideleClassCongr eK' c))) :=
      congrArg (relativeNorm rationalIdeleClassRepresentation H H' hH'H)
        hupper.symm
    _ = rationalAbstractFixedFieldIdeleClassEquivFixed H
        (Additive.ofMul
          (_root_.ideleClassNorm F E (ideleClassCongr eK' c))) := hrelative
    _ = numberFieldEmbeddedIdeleClassEquivAmbientFixed
        K L jLower (Additive.ofMul (_root_.ideleClassNorm K K' c)) := by
      change
        rationalAbstractFixedFieldIdeleClassEquivFixed H
            (Additive.ofMul
              (_root_.ideleClassNorm F E (ideleClassCongr eK' c))) =
          rationalAbstractFixedFieldIdeleClassEquivFixed H
            (Additive.ofMul
              (ideleClassCongr eK (_root_.ideleClassNorm K K' c)))
      apply congrArg (rationalAbstractFixedFieldIdeleClassEquivFixed H)
      apply congrArg Additive.ofMul
      exact
        (ideleClassCongr_ideleClassNorm
          (K := K) (K' := F) (L := K') (L' := E) eK eK' hcompat c).symm


end EmbeddedNumberFieldRestriction

end Reciprocity
end GlobalClassFieldTheory
