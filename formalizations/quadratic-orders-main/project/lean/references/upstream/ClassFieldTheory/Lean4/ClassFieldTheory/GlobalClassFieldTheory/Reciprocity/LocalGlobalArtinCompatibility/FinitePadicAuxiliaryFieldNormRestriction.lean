/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.LocalGlobalArtinCompatibility.FinitePadicAuxiliaryFieldAutomorphisms
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


local instance splitFactPrimeNormRestriction (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

attribute [local instance]
  rationalSeparableClosureAlgebra
  finitePadicAuxiliaryExtensionNormal
  finitePadicAuxiliaryExtensionQuotientFinite
  finitePadicAuxiliaryExtensionQuotientIsMulCommutative

/-- Pointwise form of norm/restriction naturality.  Keeping the function
equality and its coercion normalization in this small declaration prevents
the auxiliary-field witness construction below from repeatedly elaborating
the full pair of composite homomorphisms. -/
private theorem globalNormResidueMonoidHomOfEmbedding_norm_restriction_apply
    (K K' L L' : Type)
    [Field K] [NumberField K]
    [Field K'] [NumberField K']
    [Field L] [NumberField L]
    [Field L'] [NumberField L']
    [Algebra K K'] [Algebra K L] [Algebra K L']
    [Algebra K' L'] [Algebra L L']
    [IsScalarTower K K' L'] [IsScalarTower K L L']
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [FiniteDimensional K' L'] [IsAbelianGalois K' L']
    [FiniteDimensional K K'] [IsGalois K K']
    (j : L' →ₐ[ℚ] SeparableClosure ℚ)
    (c : IdeleClassGroup K') :
    ((AlgEquiv.restrictNormalHom L).comp
        (AlgEquiv.restrictScalarsHom K))
          (globalNormResidueMonoidHomOfEmbedding K' L' j c) =
      globalNormResidueMonoidHomOfEmbedding K L
        (j.comp (IsScalarTower.toAlgHom ℚ L L'))
        (_root_.ideleClassNorm K K' c) := by
  exact
    DFunLike.congr_fun
      (globalNormResidueMonoidHomOfEmbedding_norm_restriction
        (K := K) (L := L) (K' := K') (L' := L') j) c


/-- The auxiliary-field construction produces a lower local unit
whose chosen local Artin value and global norm-residue value are both
the finite quotient coordinate of the distinguished lift. -/
opaque numberFieldTowerFinitePadicAuxiliaryLocalGlobalRepresentative
    (v : HeightOneSpectrum (𝓞 K))
    (p : Nat.Primes)
    (τ : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (hτ :
      numberFieldTowerBaseSubgroupPadicCyclotomicDegree
          (K := K) (L := L) p τ ≠ 1)
    (hdecomposition :
      letI : Algebra K (SeparableClosure ℚ) :=
        numberFieldTowerSeparableClosureBaseAlgebra K L
      (numberFieldTowerSeparableClosureEquivBaseSubgroup K L).symm τ ∈
        absoluteValueDecompositionGroup K
          (numberFieldTowerFinitePlaceExtensionToSeparableClosure
            K L v (chosenFinitePlaceExtension (L := L) v)).1)
    (n : ℕ) (hn : 0 < n)
    (hdegree :
      numberFieldTowerBaseSubgroupPadicCyclotomicDegree
          (K := K) (L := L) p τ =
        (Multiplicative.ofAdd (1 : ℤ_[p.1])) ^ n)
    (hprimaryQuotient :
      numberFieldTowerFiniteQuotientCoordinate
          (K := K) (L := L) τ ∈
        CommGroup.primaryComponent
          ((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
            extensionSubgroup
              (numberFieldTowerBaseSubgroup K L)
              (numberFieldTowerTopSubgroup L)
              (numberFieldTowerTopSubgroup_le_baseSubgroup K L))
          p.1) :
    {z : (v.adicCompletion K)ˣ //
      chosenFinitePlaceArtinMonoidHom (K := K) (L := L) v z =
          numberFieldTowerExtensionQuotientEquivGaloisGroup K L
            (numberFieldTowerFiniteQuotientCoordinate
              (K := K) (L := L) τ) ∧
      globalNormResidueMonoidHom K L
          (IdeleGroup.finitePlaceIdeleClass v z) =
          numberFieldTowerExtensionQuotientEquivGaloisGroup K L
            (numberFieldTowerFiniteQuotientCoordinate
              (K := K) (L := L) τ)} := by
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
  letI hHfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          S (le_baseField S)) :=
    H.finite
  letI hPfinite : Finite
      (S.toSubgroup ⧸ extensionSubgroup S P.field P.below) :=
    P.finite
  letI auxiliaryBaseNumberField : NumberField F := by
    let : FiniteDimensional ℚ F :=
      LocalClassFieldTheory.abstractFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) S hHfinite
    exact NumberField.of_module_finite ℚ F
  letI auxiliaryTopNumberField : NumberField E := by
    let : FiniteDimensional F E :=
      LocalClassFieldTheory.abstractRelativeFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ)
        S P.field P.below hHfinite hPfinite
    exact NumberField.of_module_finite F E
  letI auxiliaryAbelianGalois : IsAbelianGalois F E :=
    GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois P
  letI auxiliaryOriginalBaseAlgebra : Algebra K F :=
    numberFieldTowerFinitePadicAuxiliary_baseAlgebra
      (K := K) (L := L) p τ
  letI auxiliaryOriginalTopAlgebra : Algebra L E :=
    numberFieldTowerFinitePadicAuxiliary_topAlgebra
      (K := K) (L := L) p τ
  letI auxiliaryOriginalBaseTopAlgebra : Algebra K E :=
    numberFieldTowerFinitePadicAuxiliary_originalBaseTopAlgebra
      (K := K) (L := L) p τ
  letI auxiliaryOriginalTopScalarTower : IsScalarTower K L E :=
    numberFieldTowerFinitePadicAuxiliary_originalTopScalarTower
      (K := K) (L := L) p τ
  letI auxiliaryBaseTopScalarTower : IsScalarTower K F E :=
    numberFieldTowerFinitePadicAuxiliary_baseTopScalarTower
      (K := K) (L := L) p τ
  letI auxiliaryOriginalBaseGalois : IsGalois K F :=
    numberFieldTowerFinitePadicAuxiliaryBase_isGalois
      (K := K) (L := L) p τ
  let auxiliaryOriginalTopAlgHom : L →ₐ[ℚ] E :=
    numberFieldTowerFinitePadicAuxiliaryTopEmbedding
      (K := K) (L := L) p τ
  let wF :=
    numberFieldTowerFinitePadicAuxiliaryBasePlaceExtension
      (K := K) (L := L) v p τ
  let wE :=
    numberFieldTowerFinitePadicAuxiliaryTopPlaceExtension
      (K := K) (L := L) v p τ
  let V :=
    finitePlaceExtensionCentre
      (K := K) (L := F) v wF
  have hVbelow : finitePlaceBelow (K := K) V = v :=
    finitePlaceBelow_finitePlaceExtensionCentre
      (K := K) (L := F) v wF
  let Vover :
      {V' : HeightOneSpectrum (𝓞 F) //
        finitePlaceBelow (K := K) V' = v} :=
    ⟨V, hVbelow⟩
  letI auxiliaryCompletionAlgebra :
      Algebra (v.adicCompletion K) (V.adicCompletion F) :=
    (finitePlaceAdicCompletionMap K F v Vover).toAlgebra
  let σE : Gal(E / F) :=
    numberFieldTowerFinitePadicAuxiliaryAutomorphism
      (K := K) (L := L) p τ
  have hσtop :
      σE ∈ absoluteValueDecompositionGroup F wE.1 :=
    numberFieldTowerFinitePadicAuxiliaryAutomorphism_mem_topPlaceDecomposition
      (K := K) (L := L) v p τ hdecomposition
  have hgroup :=
    numberFieldTowerFinitePadicAuxiliaryTopDecompositionGroup_eq_chosen
      (K := K) (L := L) v p τ hτ
  have hσchosen :
      σE ∈ absoluteValueDecompositionGroup F
        (chosenFinitePlaceExtension (L := E) V).1 := by
    rw [← hgroup]
    exact hσtop
  have hRange :
      σE ∈ (chosenFinitePlaceArtinMonoidHom
        (K := F) (L := E) V).range := by
    rw [chosenFinitePlaceArtinMonoidHom_range (K := F) (L := E) V]
    exact hσchosen
  let y : (V.adicCompletion F)ˣ := Classical.choose hRange
  have hy :
      chosenFinitePlaceArtinMonoidHom (K := F) (L := E) V y =
        numberFieldTowerFinitePadicAuxiliaryAutomorphism
          (K := K) (L := L) p τ :=
    Classical.choose_spec hRange
  let z : (v.adicCompletion K)ˣ :=
    LocalFieldTheory.normUnits
      (v.adicCompletion K) (V.adicCompletion F) y
  have hz :
      z = LocalFieldTheory.normUnits
        (v.adicCompletion K) (V.adicCompletion F) y := by
    rfl
  let σK : Gal(L / K) :=
    numberFieldTowerExtensionQuotientEquivGaloisGroup K L
      (numberFieldTowerFiniteQuotientCoordinate
        (K := K) (L := L) τ)
  let restriction : Gal(E / F) →* Gal(L / K) :=
    (AlgEquiv.restrictNormalHom L).comp
      (AlgEquiv.restrictScalarsHom K)
  have hrestrict : restriction σE = σK :=
    numberFieldTowerFinitePadicAuxiliaryAutomorphism_restriction
      (K := K) (L := L) p τ
  have hlocal :
      chosenFinitePlaceArtinMonoidHom (K := K) (L := L) v z =
        σK := by
    rw [hz]
    have hnat :=
      DFunLike.congr_fun
        (chosenFinitePlaceArtinMonoidHom_norm_restriction_of_below_eq
          (K := K) (L := L) (K' := F) (L' := E)
          v V hVbelow) y
    calc
      chosenFinitePlaceArtinMonoidHom (K := K) (L := L) v
          (LocalFieldTheory.normUnits
            (v.adicCompletion K) (V.adicCompletion F) y) =
        restriction
          (chosenFinitePlaceArtinMonoidHom (K := F) (L := E) V y) := by
            simpa only [
              MonoidHom.coe_comp, Function.comp_apply, restriction]
              using hnat.symm
      _ = restriction σE := congrArg restriction hy
      _ = σK := hrestrict
  let j : E →ₐ[ℚ] SeparableClosure ℚ :=
    E.val.restrictScalars ℚ
  have hjLower :
      j.comp auxiliaryOriginalTopAlgHom =
        AlgebraicNumberTheory.numberFieldSeparableClosureEmbedding L := by
    apply AlgHom.ext
    intro a
    exact
      numberFieldTowerFinitePadicAuxiliaryTopEmbedding_coe
        (K := K) (L := L) p τ a
  have hPUnramified :
      P.toFiniteGaloisExtension.IsUnramified
        rationalCyclotomicDegreeData :=
    numberFieldTowerFinitePadicAuxiliaryCompositumSubextension_isUnramified
      (K := K) (L := L) p τ n hn hdegree hprimaryQuotient
  have hcompat :
      (globalNormResidueMonoidHomOfEmbedding F E j).comp
          (IdeleGroup.finitePlaceIdeleClass V) =
        chosenFinitePlaceArtinMonoidHom (K := F) (L := E) V :=
    globalNormResidueMonoidHomOfEmbedding_comp_finitePlaceIdeleClass_of_abstractFixedFieldUnramified
      H P hPUnramified V
  have hupper :
      globalNormResidueMonoidHomOfEmbedding F E j
          (IdeleGroup.finitePlaceIdeleClass V y) =
        σE :=
    (congrArg
      (fun φ : (V.adicCompletion F)ˣ →* Gal(E / F) => φ y)
      hcompat).trans hy
  have hnormClass :
      _root_.ideleClassNorm K F
          (IdeleGroup.finitePlaceIdeleClass V y) =
        IdeleGroup.finitePlaceIdeleClass v z := by
    rw [hz]
    simpa only [Vover] using
      (IdeleGroup.ideleClassNorm_finitePlaceIdeleClass_eq_normUnits
        (K := K) (L := F) v Vover y)
  have hglobal :
      globalNormResidueMonoidHom K L
          (IdeleGroup.finitePlaceIdeleClass v z) =
        σK := by
    calc
      globalNormResidueMonoidHom K L
          (IdeleGroup.finitePlaceIdeleClass v z) =
          globalNormResidueMonoidHom K L
            (_root_.ideleClassNorm K F
              (IdeleGroup.finitePlaceIdeleClass V y)) :=
        congrArg (globalNormResidueMonoidHom K L) hnormClass.symm
      _ = globalNormResidueMonoidHomOfEmbedding K L
          (j.comp auxiliaryOriginalTopAlgHom)
          (_root_.ideleClassNorm K F
            (IdeleGroup.finitePlaceIdeleClass V y)) := by
        rw [hjLower,
          ← globalNormResidueMonoidHom_eq_ofEmbedding_standard]
      _ = ((AlgEquiv.restrictNormalHom L).comp
          (AlgEquiv.restrictScalarsHom K))
          (globalNormResidueMonoidHomOfEmbedding F E j
            (IdeleGroup.finitePlaceIdeleClass V y)) := by
        apply Eq.symm
        apply
          globalNormResidueMonoidHomOfEmbedding_norm_restriction_apply
      _ = ((AlgEquiv.restrictNormalHom L).comp
          (AlgEquiv.restrictScalarsHom K)) σE :=
        congrArg
          ((AlgEquiv.restrictNormalHom L).comp
            (AlgEquiv.restrictScalarsHom K)) hupper
      _ = restriction σE := rfl
      _ = σK := hrestrict
  exact ⟨z, hlocal, hglobal⟩


/-- Every genuine finite-place decomposition automorphism has a
compatible embedded absolute lift with the same finite quotient class
and positive integral cyclotomic `p`-adic degree. -/
theorem exists_numberFieldTowerFinitePadicLift_of_finitePlace
    (v : HeightOneSpectrum (𝓞 K))
    (p : Nat.Primes)
    (σ :
      absoluteValueDecompositionGroup K
        (chosenFinitePlaceExtension (L := L) v).1) :
    letI _ : Algebra K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseAlgebra K L
    letI _ : Algebra L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureTopAlgebra L
    letI _ : IsScalarTower K L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureScalarTower K L
    ∃ τ : (numberFieldTowerBaseSubgroup K L).toSubgroup,
      numberFieldTowerExtensionQuotientEquivGaloisGroup K L
          (numberFieldTowerFiniteQuotientCoordinate
            (K := K) (L := L) τ) =
        σ.1 ∧
      (numberFieldTowerSeparableClosureEquivBaseSubgroup K L).symm τ ∈
        absoluteValueDecompositionGroup K
          (numberFieldTowerFinitePlaceExtensionToSeparableClosure
            K L v
            (chosenFinitePlaceExtension (L := L) v)).1 ∧
      numberFieldTowerBaseSubgroupPadicCyclotomicDegree
          (K := K) (L := L) p τ ≠
        1 ∧
      ∃ n : ℕ, 0 < n ∧
        numberFieldTowerBaseSubgroupPadicCyclotomicDegree
            (K := K) (L := L) p τ =
          (Multiplicative.ofAdd (1 : ℤ_[p.1])) ^ n := by
  let : Algebra K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseAlgebra K L
  let : Algebra L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureTopAlgebra L
  let : IsScalarTower K L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureScalarTower K L
  obtain ⟨τΩ, hτΩrestrict, n, hn, hτΩdegree⟩ :=
    exists_finitePlaceSeparableClosureLift_with_positivePadicCyclotomicDegree
      (K := K) (L := L) v p σ
  let τ :
      (numberFieldTowerBaseSubgroup K L).toSubgroup :=
    numberFieldTowerSeparableClosureEquivBaseSubgroup
      K L τΩ.1
  have hfinite :
      numberFieldTowerExtensionQuotientEquivGaloisGroup K L
          (numberFieldTowerFiniteQuotientCoordinate
            (K := K) (L := L) τ) =
        σ.1 := by
    change
      numberFieldTowerExtensionQuotientEquivGaloisGroup K L
          (QuotientGroup.mk
            (numberFieldTowerSeparableClosureEquivBaseSubgroup
              K L τΩ.1)) =
        σ.1
    rw [
      numberFieldTowerExtensionQuotientEquivGaloisGroup_mk_baseSubgroupEquiv]
    exact congrArg Subtype.val hτΩrestrict
  have hdegree :
      numberFieldTowerBaseSubgroupPadicCyclotomicDegree
          (K := K) (L := L) p τ =
        (Multiplicative.ofAdd (1 : ℤ_[p.1])) ^ n := by
    exact hτΩdegree
  have hdecomposition :
      (numberFieldTowerSeparableClosureEquivBaseSubgroup K L).symm τ ∈
        absoluteValueDecompositionGroup K
          (numberFieldTowerFinitePlaceExtensionToSeparableClosure
            K L v
            (chosenFinitePlaceExtension (L := L) v)).1 := by
    simpa only [τ, MulEquiv.symm_apply_apply] using τΩ.2
  refine
    ⟨τ, hfinite, hdecomposition, ?_, n, hn, hdegree⟩
  rw [hdegree]
  exact
    PadicInt.multiplicative_positiveNatDegree_ne_one
      p.1 n hn


end Reciprocity
end GlobalClassFieldTheory
