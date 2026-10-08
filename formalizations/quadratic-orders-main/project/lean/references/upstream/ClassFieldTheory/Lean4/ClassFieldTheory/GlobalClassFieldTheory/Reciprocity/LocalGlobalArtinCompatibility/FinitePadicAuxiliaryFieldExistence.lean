/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.LocalGlobalArtinCompatibility.FinitePadicAuxiliaryFieldFixedFields
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


local instance splitFactPrimeExistence (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

attribute [local instance]
  rationalSeparableClosureAlgebra
  finitePadicAuxiliaryExtensionNormal
  finitePadicAuxiliaryExtensionQuotientFinite
  finitePadicAuxiliaryExtensionQuotientIsMulCommutative


/-- For a finite-place automorphism generating `Gal(L/K)`, construct
the genuine auxiliary number field used in the cyclotomic reduction.

The field is finite over `ℚ`, contains the compatible copy of `K`, and
has intersection with the compatible copy of `L` exactly equal to that
copy of `K`.  Its defining lift has the prescribed local restriction
and positive integral cyclotomic `p`-adic degree. -/
theorem exists_finitePlaceCyclotomicAuxiliaryFixedField
    (v : HeightOneSpectrum (𝓞 K))
    (p : Nat.Primes)
    (σ :
      absoluteValueDecompositionGroup K
        (chosenFinitePlaceExtension (L := L) v).1)
    (hσ :
      Subgroup.closure
          ({σ.1} : Set (Gal(L / K))) =
        ⊤) :
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
      FiniteDimensional ℚ
        (numberFieldTowerFinitePadicCyclicFixedField
          (K := K) (L := L) p τ) ∧
      numberFieldTowerBaseField K L ≤
        numberFieldTowerFinitePadicCyclicFixedField
          (K := K) (L := L) p τ ∧
      numberFieldTowerFinitePadicCyclicFixedField
            (K := K) (L := L) p τ ⊓
          numberFieldInRationalSeparableClosure L =
        numberFieldTowerBaseField K L ∧
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
  obtain
      ⟨τ, hτσ, hτdecomposition, hτdegree,
        n, hn, hdegree⟩ :=
    exists_numberFieldTowerFinitePadicLift_of_finitePlace
      (K := K) (L := L) v p σ
  have hgenerate :=
    numberFieldTowerFiniteQuotientCoordinate_generates_of_galoisGenerator
      (K := K) (L := L) τ σ.1 hτσ hσ
  refine
    ⟨τ, hτσ, hτdecomposition, hτdegree,
      numberFieldTowerFinitePadicCyclicFixedField_finiteDimensional
        (K := K) (L := L) p τ hτdegree,
      numberFieldTowerBaseField_le_finitePadicCyclicFixedField
        (K := K) (L := L) p τ,
      numberFieldTowerFinitePadicCyclicFixedField_inf_topField
        (K := K) (L := L) p τ hgenerate,
      n, hn, hdegree⟩

/-- A `p`-primary local generator admits a genuine auxiliary number
field whose compositum with the rational `p`-primary cyclotomic field
contains `L`.

Besides the field containment, the construction records the two
properties needed for descent: the auxiliary field meets `L` exactly
in `K`, and the chosen absolute lift has positive integral
cyclotomic degree. -/
theorem exists_finitePlacePrimaryCyclotomicAuxiliaryFixedField
    (v : HeightOneSpectrum (𝓞 K))
    (p : Nat.Primes)
    (σ :
      absoluteValueDecompositionGroup K
        (chosenFinitePlaceExtension (L := L) v).1)
    (hgenerate :
      Subgroup.closure
          ({σ.1} : Set (Gal(L / K))) =
        ⊤)
    (hprimary :
      σ.1 ∈
        CommGroup.primaryComponent
          (Gal(L / K)) p.1) :
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
      FiniteDimensional ℚ
        (numberFieldTowerFinitePadicCyclicFixedField
          (K := K) (L := L) p τ) ∧
      numberFieldTowerBaseField K L ≤
        numberFieldTowerFinitePadicCyclicFixedField
          (K := K) (L := L) p τ ∧
      numberFieldTowerFinitePadicCyclicFixedField
            (K := K) (L := L) p τ ⊓
          numberFieldInRationalSeparableClosure L =
        numberFieldTowerBaseField K L ∧
      numberFieldInRationalSeparableClosure L ≤
        numberFieldTowerFinitePadicCyclicFixedField
              (K := K) (L := L) p τ ⊔
          rationalCyclotomicPadicField p ∧
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
  obtain
      ⟨τ, hτσ, hτdecomposition, hτdegree,
        hfinite, hbase, hintersection,
        n, hn, hdegree⟩ :=
    exists_finitePlaceCyclotomicAuxiliaryFixedField
      (K := K) (L := L) v p σ hgenerate
  have hprimaryQuotient :
      numberFieldTowerFiniteQuotientCoordinate
          (K := K) (L := L) τ ∈
        CommGroup.primaryComponent
          ((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
            extensionSubgroup
              (numberFieldTowerBaseSubgroup K L)
              (numberFieldTowerTopSubgroup L)
              (numberFieldTowerTopSubgroup_le_baseSubgroup K L))
          p.1 := by
    obtain ⟨m, hm⟩ := hprimary
    refine ⟨m, ?_⟩
    let e :=
      numberFieldTowerExtensionQuotientEquivGaloisGroup K L
    let q :=
      numberFieldTowerFiniteQuotientCoordinate
        (K := K) (L := L) τ
    let N : ℕ := p.1 ^ m
    have hq : e q = σ.1 := by
      exact hτσ
    have hmN : σ.1 ^ N = 1 := by
      exact hm
    change q ^ N = 1
    apply e.injective
    calc
      e (q ^ N) = (e q) ^ N := by
        exact map_pow e q N
      _ = σ.1 ^ N := by rw [hq]
      _ = 1 := hmN
      _ = e 1 := (map_one e).symm
  have hcontainment :=
    numberFieldTowerTopField_le_finitePadicCyclicFixedField_sup_padicCyclotomicField
      (K := K) (L := L) p τ n hn hdegree
        hprimaryQuotient
  exact
    ⟨τ, hτσ, hτdecomposition, hτdegree,
      hfinite, hbase, hintersection,
      hcontainment, n, hn, hdegree⟩


end Reciprocity
end GlobalClassFieldTheory
