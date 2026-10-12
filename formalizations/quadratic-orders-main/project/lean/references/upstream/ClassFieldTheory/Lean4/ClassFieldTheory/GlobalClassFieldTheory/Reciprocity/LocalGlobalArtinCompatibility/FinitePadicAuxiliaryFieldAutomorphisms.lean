/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.LocalGlobalArtinCompatibility.FinitePadicAuxiliaryFieldBase
import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.LocalGlobalArtinCompatibility.FinitePadicCyclicData
import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClassFieldRealization
import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.CyclotomicUnramifiedLocalGlobalCompatibility
import ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.OnePlaceBaseNorm


set_option autoImplicit false


open scoped IsMulCommutative NumberField
open AlgebraicNumberTheory IsDedekindDomain NumberField
open IdeleGroup RelativeIdeleGroup
open AlgebraicNumberTheory.Valuations
open HilbertRamification
open CyclicCohomology
open KummerTheory ClassFormation

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open GlobalClassFields

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]


local instance splitFactPrimeAutomorphisms (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

attribute [local instance]
  rationalSeparableClosureAlgebra
  finitePadicAuxiliaryExtensionNormal
  finitePadicAuxiliaryExtensionQuotientFinite
  finitePadicAuxiliaryExtensionQuotientIsMulCommutative

/-- The distinguished absolute lift, regarded as an element of the
auxiliary base subgroup. -/
noncomputable def numberFieldTowerFinitePadicAuxiliarySubgroupLift
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    (numberFieldTowerFinitePadicCyclicFixedSubgroup
      (K := K) (L := L) p τ).toSubgroup :=
  ⟨τ.1,
    numberFieldTowerFinitePadicCyclicFixedSubgroup_generator_mem
      (K := K) (L := L) p τ⟩

/-- The actual automorphism of the auxiliary compositum induced by
the distinguished simultaneous finite/cyclotomic lift. -/
noncomputable def numberFieldTowerFinitePadicAuxiliaryAutomorphism
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    let P :=
      numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
        (K := K) (L := L) p τ
    let S :=
      numberFieldTowerFinitePadicCyclicFixedSubgroup
        (K := K) (L := L) p τ
    Gal(
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below /
      LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) S) := by
  dsimp only
  let P :=
    numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
      (K := K) (L := L) p τ
  let S :=
    numberFieldTowerFinitePadicCyclicFixedSubgroup
      (K := K) (L := L) p τ
  let σS :=
    numberFieldTowerFinitePadicAuxiliarySubgroupLift
      (K := K) (L := L) p τ
  exact
    LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup
      ℚ (SeparableClosure ℚ)
      S P.field P.below
      P.toFiniteGaloisExtension.normal
      (QuotientGroup.mk'
        (extensionSubgroup
          S P.field P.below)
        σS)

/-- On the common separable closure, the auxiliary automorphism acts
by the original distinguished ambient lift. -/
theorem numberFieldTowerFinitePadicAuxiliaryAutomorphism_apply_val
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (x :
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
          (K := K) (L := L) p τ).below) :
    ((numberFieldTowerFinitePadicAuxiliaryAutomorphism
        (K := K) (L := L) p τ x :
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
          (K := K) (L := L) p τ).below) :
      SeparableClosure ℚ) =
        τ.1 (x : SeparableClosure ℚ) := by
  let P :=
    numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
      (K := K) (L := L) p τ
  let S :=
    numberFieldTowerFinitePadicCyclicFixedSubgroup
      (K := K) (L := L) p τ
  let σS :=
    numberFieldTowerFinitePadicAuxiliarySubgroupLift
      (K := K) (L := L) p τ
  exact
    (LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup_mk_apply_val
        ℚ (SeparableClosure ℚ)
        S P.field P.below
        P.toFiniteGaloisExtension.normal σS x).symm

/-- Restricting the auxiliary automorphism through the actual
base-change square recovers the finite quotient coordinate of the
distinguished lift. -/
theorem numberFieldTowerFinitePadicAuxiliaryAutomorphism_restriction
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    ((AlgEquiv.restrictNormalHom L).comp
        (AlgEquiv.restrictScalarsHom K))
        (numberFieldTowerFinitePadicAuxiliaryAutomorphism
          (K := K) (L := L) p τ) =
      numberFieldTowerExtensionQuotientEquivGaloisGroup K L
        (numberFieldTowerFiniteQuotientCoordinate
          (K := K) (L := L) τ) := by
  let E :=
    LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ)
      (numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
        (K := K) (L := L) p τ).below
  let σE :=
    numberFieldTowerFinitePadicAuxiliaryAutomorphism
      (K := K) (L := L) p τ
  apply AlgEquiv.ext
  intro x
  apply (numberFieldSeparableClosureEmbedding L).injective
  calc
    numberFieldSeparableClosureEmbedding L
        (((AlgEquiv.restrictNormalHom L).comp
          (AlgEquiv.restrictScalarsHom K)) σE x) =
      ((σE (algebraMap L E x) : E) :
        SeparableClosure ℚ) := by
          exact congrArg Subtype.val
            (AlgEquiv.restrictNormal_commutes
              ((AlgEquiv.restrictScalarsHom K) σE) L x)
    _ = τ.1 (numberFieldSeparableClosureEmbedding L x) := by
      rw [
        numberFieldTowerFinitePadicAuxiliaryAutomorphism_apply_val
          (K := K) (L := L) p τ]
      rfl
    _ =
      numberFieldSeparableClosureEmbedding L
        (numberFieldTowerExtensionQuotientEquivGaloisGroup K L
          (numberFieldTowerFiniteQuotientCoordinate
            (K := K) (L := L) τ) x) := by
      exact
        (numberFieldTowerExtensionQuotientEquivGaloisGroup_mk_apply
          (K := K) (L := L) τ x).symm

/-- Restriction of the chosen separable-closure place to the genuine
auxiliary base field.  This is an exact extension of the original
finite place of `K`, not merely an equivalent valuation. -/
noncomputable def
    numberFieldTowerFinitePadicAuxiliaryBasePlaceExtension
    (v : HeightOneSpectrum (𝓞 K))
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v)
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ)
        (numberFieldTowerFinitePadicCyclicFixedSubgroup
          (K := K) (L := L) p τ)) := by
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ)
      (numberFieldTowerFinitePadicCyclicFixedSubgroup
        (K := K) (L := L) p τ)
  let wΩ :=
    numberFieldTowerFinitePlaceExtensionToSeparableClosure
      K L v (chosenFinitePlaceExtension (L := L) v)
  refine
    ⟨wΩ.1.comp (f := F.val.toRingHom) F.val.injective, ?_⟩
  intro x
  change
    wΩ.1 (numberFieldTowerLowerEmbedding K L x) =
      NumberField.HeightOneSpectrum.adicAbv K v x
  exact wΩ.2 x

/-- Restriction of the same separable-closure place to the genuine
auxiliary compositum.  Its restriction to `K` agrees exactly with the
original normalized finite absolute value. -/
noncomputable def
    numberFieldTowerFinitePadicAuxiliaryTopPlaceExtension
    (v : HeightOneSpectrum (𝓞 K))
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v)
      (LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ)
        (numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
          (K := K) (L := L) p τ).below) := by
  let E :=
    LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ)
      (numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
        (K := K) (L := L) p τ).below
  let wΩ :=
    numberFieldTowerFinitePlaceExtensionToSeparableClosure
      K L v (chosenFinitePlaceExtension (L := L) v)
  refine
    ⟨wΩ.1.comp (f := E.val.toRingHom) E.val.injective, ?_⟩
  intro x
  change
    wΩ.1 (numberFieldTowerLowerEmbedding K L x) =
      NumberField.HeightOneSpectrum.adicAbv K v x
  exact wΩ.2 x

/-- The centre of the restricted place on the auxiliary compositum
lies above the centre of the same place on the auxiliary base field. -/
theorem
    numberFieldTowerFinitePadicAuxiliaryTopPlace_below
    (v : HeightOneSpectrum (𝓞 K))
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (hτ :
      numberFieldTowerBaseSubgroupPadicCyclotomicDegree
          (K := K) (L := L) p τ ≠
        1) :
    let S :=
      numberFieldTowerFinitePadicCyclicFixedSubgroup
        (K := K) (L := L) p τ
    let P :=
      numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
        (K := K) (L := L) p τ
    let F :=
      LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) S
    let E :=
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below
    letI hHfinite : Finite
        ((baseField
          (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
          extensionSubgroup
            (baseField
              (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
            S (le_baseField S)) :=
      (numberFieldTowerFinitePadicAuxiliaryAbstractField
        (K := K) (L := L) p τ hτ).finite
    letI hPfinite : Finite
        (S.toSubgroup ⧸
          extensionSubgroup S P.field P.below) :=
      P.finite
    letI _ : FiniteDimensional ℚ F :=
      LocalClassFieldTheory.abstractFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) S hHfinite
    letI _ : FiniteDimensional F E :=
      LocalClassFieldTheory.abstractRelativeFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ)
        S P.field P.below hHfinite hPfinite
    letI _ : IsScalarTower ℚ F E :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI _ : FiniteDimensional ℚ E :=
      FiniteDimensional.trans ℚ F E
    letI _ : NumberField F :=
      NumberField.of_module_finite ℚ F
    letI _ : NumberField E :=
      NumberField.of_module_finite ℚ E
    letI _ : Algebra K F :=
      numberFieldTowerFinitePadicAuxiliary_baseAlgebra
        (K := K) (L := L) p τ
    finitePlaceBelow (K := F)
        (finitePlaceExtensionCentre
          (K := K) (L := E) v
          (numberFieldTowerFinitePadicAuxiliaryTopPlaceExtension
            (K := K) (L := L) v p τ)) =
      finitePlaceExtensionCentre
        (K := K) (L := F) v
        (numberFieldTowerFinitePadicAuxiliaryBasePlaceExtension
          (K := K) (L := L) v p τ) := by
  dsimp only
  let S :=
    numberFieldTowerFinitePadicCyclicFixedSubgroup
      (K := K) (L := L) p τ
  let P :=
    numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
      (K := K) (L := L) p τ
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) S
  let E :=
    LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below
  let hHfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          S (le_baseField S)) :=
    (numberFieldTowerFinitePadicAuxiliaryAbstractField
      (K := K) (L := L) p τ hτ).finite
  let hPfinite : Finite
      (S.toSubgroup ⧸
        extensionSubgroup S P.field P.below) :=
    P.finite
  let auxiliaryBaseFiniteDimensional : FiniteDimensional ℚ F :=
    LocalClassFieldTheory.abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) S hHfinite
  let auxiliaryTopFiniteDimensional : FiniteDimensional F E :=
    LocalClassFieldTheory.abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ)
      S P.field P.below hHfinite hPfinite
  let auxiliaryScalarTower : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' rfl
  let auxiliaryAbsoluteFiniteDimensional : FiniteDimensional ℚ E :=
    FiniteDimensional.trans ℚ F E
  let auxiliaryBaseNumberField : NumberField F :=
    NumberField.of_module_finite ℚ F
  let auxiliaryTopNumberField : NumberField E :=
    NumberField.of_module_finite ℚ E
  let auxiliaryOriginalBaseAlgebra : Algebra K F :=
    numberFieldTowerFinitePadicAuxiliary_baseAlgebra
      (K := K) (L := L) p τ
  let wF :=
    numberFieldTowerFinitePadicAuxiliaryBasePlaceExtension
      (K := K) (L := L) v p τ
  let wE :=
    numberFieldTowerFinitePadicAuxiliaryTopPlaceExtension
      (K := K) (L := L) v p τ
  apply HeightOneSpectrum.ext
  ext x
  change
    algebraMap (𝓞 F) (𝓞 E) x ∈
        finitePlaceExtensionCentreIdeal
          (K := K) (L := E) v wE ↔
      x ∈
        finitePlaceExtensionCentreIdeal
          (K := K) (L := F) v wF
  rw [
    mem_finitePlaceExtensionCentreIdeal_iff,
    mem_finitePlaceExtensionCentreIdeal_iff]
  rfl

/-- Evaluation of the distinguished auxiliary automorphism through the
restricted top-field place.  Isolating this coercion calculation prevents the
whole decomposition-group proof from normalizing the fixed-field tower. -/
public opaque
    numberFieldTowerFinitePadicAuxiliaryTopPlace_automorphism_apply
    (v : HeightOneSpectrum (𝓞 K))
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup) :
    let P := numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
      (K := K) (L := L) p τ
    let E := LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below
    let wE := numberFieldTowerFinitePadicAuxiliaryTopPlaceExtension
      (K := K) (L := L) v p τ
    let σE := numberFieldTowerFinitePadicAuxiliaryAutomorphism
      (K := K) (L := L) p τ
    ∀ x : E,
      wE.1 (σE x) =
        (numberFieldTowerFinitePlaceExtensionToSeparableClosure
          K L v (chosenFinitePlaceExtension (L := L) v)).1
            (τ.1 (x : SeparableClosure ℚ)) := by
  let : Algebra K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseAlgebra K L
  dsimp only
  intro x
  change
    (numberFieldTowerFinitePlaceExtensionToSeparableClosure
      K L v (chosenFinitePlaceExtension (L := L) v)).1
        ((numberFieldTowerFinitePadicAuxiliaryAutomorphism
          (K := K) (L := L) p τ x :
            LocalClassFieldTheory.abstractRelativeFixedField
              ℚ (SeparableClosure ℚ)
              (numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
                (K := K) (L := L) p τ).below) : SeparableClosure ℚ) = _
  rw [
    numberFieldTowerFinitePadicAuxiliaryAutomorphism_apply_val
      (K := K) (L := L) p τ]

/-- The distinguished auxiliary automorphism preserves the top-field place
obtained by restricting the original separable-closure place. -/
public opaque numberFieldTowerFinitePadicAuxiliaryAutomorphism_mem_topPlaceDecomposition
    (v : HeightOneSpectrum (𝓞 K))
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (hdecomposition :
      letI : Algebra K (SeparableClosure ℚ) :=
        numberFieldTowerSeparableClosureBaseAlgebra K L
      (numberFieldTowerSeparableClosureEquivBaseSubgroup K L).symm τ ∈
        absoluteValueDecompositionGroup K
          (numberFieldTowerFinitePlaceExtensionToSeparableClosure
            K L v (chosenFinitePlaceExtension (L := L) v)).1) :
    let S := numberFieldTowerFinitePadicCyclicFixedSubgroup
      (K := K) (L := L) p τ
    let F := LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) S
    let wE := numberFieldTowerFinitePadicAuxiliaryTopPlaceExtension
      (K := K) (L := L) v p τ
    let σE := numberFieldTowerFinitePadicAuxiliaryAutomorphism
      (K := K) (L := L) p τ
    σE ∈ absoluteValueDecompositionGroup F wE.1 := by
  let : Algebra K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseAlgebra K L
  dsimp only at hdecomposition ⊢
  let S :=
    numberFieldTowerFinitePadicCyclicFixedSubgroup
      (K := K) (L := L) p τ
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) S
  let wE :=
    numberFieldTowerFinitePadicAuxiliaryTopPlaceExtension
      (K := K) (L := L) v p τ
  let σE :=
    numberFieldTowerFinitePadicAuxiliaryAutomorphism
      (K := K) (L := L) p τ
  intro x
  change
    wE.1 (σE x) < 1 ↔
      wE.1 x < 1
  rw [
    numberFieldTowerFinitePadicAuxiliaryTopPlace_automorphism_apply
      (K := K) (L := L) v p τ x,
    show
      wE.1 x =
        (numberFieldTowerFinitePlaceExtensionToSeparableClosure
          K L v
          (chosenFinitePlaceExtension (L := L) v)).1
            (x : SeparableClosure ℚ) from rfl]
  exact hdecomposition (x : SeparableClosure ℚ)

/-- The restricted top-field place and the chosen extension above its centre
have the same decomposition group. -/
public opaque numberFieldTowerFinitePadicAuxiliaryTopDecompositionGroup_eq_chosen
    (v : HeightOneSpectrum (𝓞 K))
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (hτ :
      numberFieldTowerBaseSubgroupPadicCyclotomicDegree
          (K := K) (L := L) p τ ≠ 1) :
    let S := numberFieldTowerFinitePadicCyclicFixedSubgroup
      (K := K) (L := L) p τ
    let P := numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
      (K := K) (L := L) p τ
    let F := LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) S
    let E := LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below
    letI hHfinite : Finite
        ((baseField
          (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
          extensionSubgroup
            (baseField
              (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
            S (le_baseField S)) :=
      (numberFieldTowerFinitePadicAuxiliaryAbstractField
        (K := K) (L := L) p τ hτ).finite
    letI hPfinite : Finite
        (S.toSubgroup ⧸ extensionSubgroup S P.field P.below) := P.finite
    letI : FiniteDimensional ℚ F :=
      LocalClassFieldTheory.abstractFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) S hHfinite
    letI : FiniteDimensional F E :=
      LocalClassFieldTheory.abstractRelativeFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) S P.field P.below hHfinite hPfinite
    letI : IsScalarTower ℚ F E := IsScalarTower.of_algebraMap_eq' rfl
    letI : FiniteDimensional ℚ E := FiniteDimensional.trans ℚ F E
    letI : NumberField F := NumberField.of_module_finite ℚ F
    letI : NumberField E := NumberField.of_module_finite ℚ E
    letI : IsAbelianGalois F E :=
      GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois P
    letI : Algebra K F :=
      numberFieldTowerFinitePadicAuxiliary_baseAlgebra
        (K := K) (L := L) p τ
    let wF := numberFieldTowerFinitePadicAuxiliaryBasePlaceExtension
      (K := K) (L := L) v p τ
    let wE := numberFieldTowerFinitePadicAuxiliaryTopPlaceExtension
      (K := K) (L := L) v p τ
    let V := finitePlaceExtensionCentre (K := K) (L := F) v wF
    absoluteValueDecompositionGroup F wE.1 =
      absoluteValueDecompositionGroup F
        (chosenFinitePlaceExtension (L := E) V).1 := by
  dsimp only
  let H :=
    numberFieldTowerFinitePadicAuxiliaryAbstractField
      (K := K) (L := L) p τ hτ
  let S :=
    numberFieldTowerFinitePadicCyclicFixedSubgroup
      (K := K) (L := L) p τ
  let P :=
    numberFieldTowerFinitePadicAuxiliaryCompositumSubextension
      (K := K) (L := L) p τ
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) S
  let E :=
    LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below
  let hHfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          S (le_baseField S)) :=
    H.finite
  let hPfinite : Finite
      (S.toSubgroup ⧸ extensionSubgroup S P.field P.below) :=
    P.finite
  let : FiniteDimensional ℚ F :=
    LocalClassFieldTheory.abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) S hHfinite
  let : FiniteDimensional F E :=
    LocalClassFieldTheory.abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) S P.field P.below hHfinite hPfinite
  let : IsScalarTower ℚ F E := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional ℚ E := FiniteDimensional.trans ℚ F E
  let : NumberField F := NumberField.of_module_finite ℚ F
  let : NumberField E := NumberField.of_module_finite ℚ E
  let : IsAbelianGalois F E :=
    GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois P
  let : Algebra K F :=
    numberFieldTowerFinitePadicAuxiliary_baseAlgebra
      (K := K) (L := L) p τ
  let wF :=
    numberFieldTowerFinitePadicAuxiliaryBasePlaceExtension
      (K := K) (L := L) v p τ
  let wE :=
    numberFieldTowerFinitePadicAuxiliaryTopPlaceExtension
      (K := K) (L := L) v p τ
  let V := finitePlaceExtensionCentre (K := K) (L := F) v wF
  let W := finitePlaceExtensionCentre (K := K) (L := E) v wE
  let Wover :
      {W' : HeightOneSpectrum (𝓞 E) //
        finitePlaceBelow (K := F) W' = V} :=
    ⟨W,
      numberFieldTowerFinitePadicAuxiliaryTopPlace_below
        (K := K) (L := L) v p τ hτ⟩
  let wFE :
      AbsoluteValueExtension
        (NumberField.HeightOneSpectrum.adicAbv F V) E :=
    (finitePlaceExtensionEquivAbove
      (K := F) (L := E) V).symm Wover
  have hwFEcentre :
      finitePlaceExtensionCentre
          (K := F) (L := E) V wFE =
        W := by
    exact
      congrArg Subtype.val
        ((finitePlaceExtensionEquivAbove
          (K := F) (L := E) V).apply_symm_apply Wover)
  have hwEquiv : wE.1.IsEquiv wFE.1 := by
    apply
      finitePlaceExtensions_isEquiv_of_centres_eq
        (F := K) (M := F) v V wE wFE
    exact hwFEcentre.symm
  calc
    absoluteValueDecompositionGroup F wE.1 =
        absoluteValueDecompositionGroup F wFE.1 :=
      absoluteValueDecompositionGroup_eq_of_absoluteValue_isEquiv
        (F := F) wE.1 wFE.1 hwEquiv
    _ =
      absoluteValueDecompositionGroup F
          (chosenFinitePlaceExtension (L := E) V).1 :=
      absoluteValueDecompositionGroup_eq_of_exactExtensions_of_isMulCommutative
        (F := F)
        (NumberField.HeightOneSpectrum.adicAbv F V)
        (RayClass.adicAbv_isNontrivial V)
        wFE
        (chosenFinitePlaceExtension (L := E) V)


end Reciprocity
end GlobalClassFieldTheory
