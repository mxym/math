/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalNormResidueNaturalityTowerRestriction


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

/-- For one common compatible embedding of a Galois base-change
diamond, the genuine global norm-residue maps commute with ordinary
idele-class norm and actual restriction of automorphisms. -/
theorem globalNormResidueMonoidHomOfEmbedding_norm_restriction
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [FiniteDimensional K' L'] [IsAbelianGalois K' L']
    [FiniteDimensional K K'] [IsGalois K K']
    (j : L' →ₐ[ℚ] SeparableClosure ℚ) :
    let jLower : L →ₐ[ℚ] SeparableClosure ℚ :=
      j.comp (IsScalarTower.toAlgHom ℚ L L')
    ((AlgEquiv.restrictNormalHom L).comp
        (AlgEquiv.restrictScalarsHom K)).comp
        (globalNormResidueMonoidHomOfEmbedding K' L' j) =
      (globalNormResidueMonoidHomOfEmbedding K L jLower).comp
        (_root_.ideleClassNorm K K') := by
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
  let hJH :=
    numberFieldEmbeddedTopSubgroup_le_baseSubgroup K L jLower
  let hJ'H' :=
    numberFieldEmbeddedTopSubgroup_le_baseSubgroup K' L' j
  let hH'H :=
    numberFieldEmbeddedBaseSubgroup_le_of_tower K K' L L' j
  let hJ'J :=
    numberFieldEmbeddedTopSubgroup_le_of_tower K K' L L' j
  let _ :
      (CyclicCohomology.extensionSubgroup H J hJH).Normal :=
    numberFieldEmbeddedExtensionSubgroup_normal K L jLower
  let _ :
      Finite
        (H.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup H J hJH) :=
    numberFieldEmbeddedExtensionQuotient_finite K L jLower
  let _ :
      (CyclicCohomology.extensionSubgroup H' J' hJ'H').Normal :=
    numberFieldEmbeddedExtensionSubgroup_normal K' L' j
  let _ :
      Finite
        (H'.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup H' J' hJ'H') :=
    numberFieldEmbeddedExtensionQuotient_finite K' L' j
  let hHH'finite :=
    numberFieldEmbeddedBaseChangeExtensionQuotientFinite K K' L L' j
  let T :
      FiniteAbstractFieldExtension
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) :=
    { field := numberFieldEmbeddedFiniteAbstractField K' L' j
      base := numberFieldEmbeddedFiniteAbstractField K L jLower
      below := hH'H
      finiteQuotient := hHH'finite }
  let hTBaseNormal :
      (CyclicCohomology.extensionSubgroup
        T.base.field J hJH).Normal := by
    change
      (CyclicCohomology.extensionSubgroup H J hJH).Normal
    exact numberFieldEmbeddedExtensionSubgroup_normal K L jLower
  let hTBaseFinite :
      Finite
        (T.base.field.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup
            T.base.field J hJH) := by
    change
      Finite
        (H.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup H J hJH)
    exact numberFieldEmbeddedExtensionQuotient_finite K L jLower
  let hTFieldNormal :
      (CyclicCohomology.extensionSubgroup
        T.field.field J' hJ'H').Normal := by
    change
      (CyclicCohomology.extensionSubgroup H' J' hJ'H').Normal
    exact numberFieldEmbeddedExtensionSubgroup_normal K' L' j
  let hTFieldFinite :
      Finite
        (T.field.field.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup
            T.field.field J' hJ'H') := by
    change
      Finite
        (H'.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup H' J' hJ'H')
    exact numberFieldEmbeddedExtensionQuotient_finite K' L' j
  let restrictActual :
      Gal(L' / K') →* Gal(L / K) :=
    (AlgEquiv.restrictNormalHom L).comp
      (AlgEquiv.restrictScalarsHom K)
  apply MonoidHom.ext
  intro c
  let a :=
    numberFieldEmbeddedIdeleClassEquivAmbientFixed
      K' L' j (Additive.ofMul c)
  have hnat :=
    DegreeData.normResidueNaturality_norm_restriction
      (D := rationalCyclotomicDegreeData)
      (A := rationalIdeleClassRepresentation)
      (v := rationalCyclotomicIdeleClassValuationData)
      (hcf := rationalIdeleClassRepresentation_satisfiesClassFieldAxiom)
      (T := T) (L := J) (L' := J')
      (hLnormal := hTBaseNormal)
      (hL'normal := hTFieldNormal)
      (hLKfinite := hTBaseFinite)
      (hL'K'finite := hTFieldFinite)
      hJH hJ'H' hJ'J
  have hnatc :=
    DFunLike.congr_fun hnat
      (finiteNormClass rationalIdeleClassRepresentation
        H' J' hJ'H' a)
  change _ =
    rationalCyclotomicDegreeData.normResidueSymbol
      rationalIdeleClassRepresentation
      rationalCyclotomicIdeleClassValuationData
      rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
      T.base
      { field := J
        below := hJH
        normal := hTBaseNormal
        finite := hTBaseFinite }
      (finiteReciprocityNaturalityNormMap
        rationalIdeleClassRepresentation
        T.base.field T.field.field J J'
        hJH hJ'H' T.below hJ'J
        (finiteNormClass rationalIdeleClassRepresentation
          T.field.field J' hJ'H' a)) at hnatc
  rw [finiteReciprocityNaturalityNormMap_finiteNormClass]
    at hnatc
  have hnorm :
      relativeNorm rationalIdeleClassRepresentation
          H H' hH'H a =
        numberFieldEmbeddedIdeleClassEquivAmbientFixed
          K L jLower
          (Additive.ofMul (_root_.ideleClassNorm K K' c)) :=
    numberFieldEmbeddedIdeleClassEquivAmbientFixed_relativeNorm
      K K' L L' j c
  calc
    restrictActual
        (globalNormResidueMonoidHomOfEmbedding K' L' j c) =
      restrictActual
        (Additive.toMul
          (numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup
            K' L' j
            (rationalCyclotomicDegreeData.normResidueSymbol
              rationalIdeleClassRepresentation
              rationalCyclotomicIdeleClassValuationData
              rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
              (numberFieldEmbeddedFiniteAbstractField K' L' j)
              (numberFieldEmbeddedFiniteGaloisSubextension K' L' j)
              (finiteNormClass rationalIdeleClassRepresentation
                H' J' hJ'H' a)))) := by
      rw [globalNormResidueMonoidHomOfEmbedding_apply]
    _ =
      Additive.toMul
        (numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup
          K L jLower
          (MonoidHom.toAdditive
            (normResidueNaturalityAbelianizedRestriction
              H H' J J' hJH hJ'H' hH'H hJ'J)
            (rationalCyclotomicDegreeData.normResidueSymbol
              rationalIdeleClassRepresentation
              rationalCyclotomicIdeleClassValuationData
              rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
              (numberFieldEmbeddedFiniteAbstractField K' L' j)
              (numberFieldEmbeddedFiniteGaloisSubextension K' L' j)
              (finiteNormClass rationalIdeleClassRepresentation
                H' J' hJ'H' a)))) := by
      exact
        numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup_restriction
          K K' L L' j _
    _ =
      Additive.toMul
        (numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup
          K L jLower
          (rationalCyclotomicDegreeData.normResidueSymbol
            rationalIdeleClassRepresentation
            rationalCyclotomicIdeleClassValuationData
            rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
            (numberFieldEmbeddedFiniteAbstractField K L jLower)
            (numberFieldEmbeddedFiniteGaloisSubextension K L jLower)
            (finiteNormClass rationalIdeleClassRepresentation
              H J hJH
              (relativeNorm rationalIdeleClassRepresentation
                H H' hH'H a)))) := by
      exact congrArg
        (fun z =>
          Additive.toMul
            (numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisGroup
              K L jLower z))
        hnatc
    _ =
      globalNormResidueMonoidHomOfEmbedding K L jLower
        (_root_.ideleClassNorm K K' c) := by
      rw [hnorm,
        ← globalNormResidueMonoidHomOfEmbedding_apply]

end EmbeddedNumberFieldRestriction


end Reciprocity
end GlobalClassFieldTheory
