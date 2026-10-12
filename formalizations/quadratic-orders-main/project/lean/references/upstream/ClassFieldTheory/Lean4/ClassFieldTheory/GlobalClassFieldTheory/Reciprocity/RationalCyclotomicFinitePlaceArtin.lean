/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.RationalCyclotomicFinitePlaceArtinPrincipal


set_option autoImplicit false

open scoped Classical NNReal NumberField ValuativeRel
open NumberField IsDedekindDomain
open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open LubinTate

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

attribute [local instance]
  rationalFinitePlaceCompletionRatAlgebra
  primeFact
  levelNeZero
  rationalCyclotomicLevelFiniteDimensional
  rationalCyclotomicLevelIsAbelianGalois
  rationalFinitePlaceBaseNontriviallyNormedField
  rationalFinitePlaceBaseLocallyCompactSpace
  rationalFinitePlaceBaseIsUltrametricDist
  rationalFinitePlaceBaseValued
  rationalFinitePlaceBaseValuativeRel
  rationalFinitePlaceBaseValuationIsNontrivial
  rationalFinitePlaceBaseValuationCompatible
  rationalFinitePlaceBaseValuativeRelIsNontrivial
  rationalFinitePlaceBaseIsValuativeTopology
  rationalFinitePlaceBaseIsNonarchimedeanLocalField
  rationalCyclotomicArtinExtensionAlgebra
  rationalCyclotomicArtinExtensionSMul
  rationalCyclotomicArtinCompletionAlgebra
  rationalCyclotomicArtinLocalizedAlgebra
  rationalCyclotomicArtinLocalizedGlobalAlgebra
  rationalCyclotomicArtinLocalizedGlobalSMul
  rationalCyclotomicArtinLocalizedScalarTower
  rationalCyclotomicArtinLocalizedFiniteDimensional
  rationalCyclotomicArtinLocalizedIsAbelianGalois
  rationalCyclotomicArtinLocalizedIsSeparable
  rationalCyclotomicArtinLocalizedIsCyclotomic
  rationalCyclotomicArtinExtensionFiniteDimensional
  rationalCyclotomicArtinExtensionContinuousSMul
  rationalCyclotomicArtinExtensionLocallyCompact
  rationalCyclotomicArtinLocalizedLocallyCompact
  rationalCyclotomicArtinLocalizedIsUltrametricDist
  rationalCyclotomicArtinLocalizedValued
  rationalCyclotomicArtinLocalizedValuativeRel
  rationalCyclotomicArtinLocalizedValuationCompatible
  rationalCyclotomicArtinLocalizedValuationHasExtension
  rationalCyclotomicArtinLocalizedValuationIsNontrivial
  rationalCyclotomicArtinLocalizedValuativeRelIsNontrivial
  rationalCyclotomicArtinLocalizedIsValuativeTopology
  rationalCyclotomicArtinLocalizedIsNonarchimedeanLocalField
  rationalCyclotomicArtinLocalizedIntegerAlgebra
  rationalCyclotomicArtinLocalizedIsIntegralClosure
  rationalCyclotomicArtinLocalizedIntegerModuleFinite

private theorem rationalCyclotomicArtinUnramified
    (m : ℕ+) (q : Nat.Primes)
    (hq : ¬ q.1 ∣ (m : ℕ)) :
    IsNonarchimedeanLocalField.IsUnramifiedValuedExtension
      (rationalCyclotomicArtinBaseAbv q).Completion
      (rationalCyclotomicArtinLocalizedField m q) := by
  simpa [ChosenFinitePlaceIsUnramified] using
    (rationalCyclotomicLevel_chosenFinitePlaceIsUnramified
      m q hq)

private noncomputable def rationalCyclotomicArtinLocalFrobeniusOf
    (m : ℕ+) (q : Nat.Primes)
    (hUnramified :
      IsNonarchimedeanLocalField.IsUnramifiedValuedExtension
        (rationalCyclotomicArtinBaseAbv q).Completion
        (rationalCyclotomicArtinLocalizedField m q)) :
    rationalCyclotomicArtinLocalizedField m q ≃ₐ[
      (rationalCyclotomicArtinBaseAbv q).Completion]
      rationalCyclotomicArtinLocalizedField m q := by
  letI := hUnramified
  exact arithmeticFrobeniusOfUnramifiedValuation
    (rationalCyclotomicArtinBaseAbv q).Completion
    (rationalCyclotomicArtinLocalizedField m q)

private noncomputable def rationalCyclotomicArtinLocalFrobenius
    (m : ℕ+) (q : Nat.Primes)
    (hq : ¬ q.1 ∣ (m : ℕ)) :
    rationalCyclotomicArtinLocalizedField m q ≃ₐ[
      (rationalCyclotomicArtinBaseAbv q).Completion]
      rationalCyclotomicArtinLocalizedField m q :=
  rationalCyclotomicArtinLocalFrobeniusOf m q
    (rationalCyclotomicArtinUnramified m q hq)

private noncomputable def rationalCyclotomicArtinDecompositionEquiv
    (m : ℕ+) (q : Nat.Primes) :
    absoluteValueDecompositionGroup ℚ
        (rationalCyclotomicArtinExtension m q).1 ≃*
      (rationalCyclotomicArtinLocalizedField m q ≃ₐ[
        (rationalCyclotomicArtinBaseAbv q).Completion]
        rationalCyclotomicArtinLocalizedField m q) :=
  decompositionGroupEquivAlgebraicLocalizationAut
    (rationalCyclotomicArtinBaseAbv q)
    (RayClass.adicAbv_isNontrivial
      (rationalCyclotomicArtinPlace q))
    (rationalCyclotomicArtinExtension m q)

private noncomputable def rationalCyclotomicArtinLocalToGlobalMonoidHom
    (m : ℕ+) (q : Nat.Primes) :
    (rationalCyclotomicArtinLocalizedField m q ≃ₐ[
      (rationalCyclotomicArtinBaseAbv q).Completion]
      rationalCyclotomicArtinLocalizedField m q) →*
        (rationalCyclotomicArtinLevel m ≃ₐ[ℚ]
          rationalCyclotomicArtinLevel m) :=
  finitePlaceLocalToGlobalMonoidHom
    (K := ℚ) (L := rationalCyclotomicArtinLevel m)
    (rationalCyclotomicArtinPlace q)
    (rationalCyclotomicArtinExtension m q)

private noncomputable abbrev rationalCyclotomicArtinLocalArtin
    (m : ℕ+) (q : Nat.Primes)
    (x : ((RayClass.rationalPrime q).adicCompletion ℚ)ˣ) :
    rationalCyclotomicArtinLocalizedField m q ≃ₐ[
      (rationalCyclotomicArtinBaseAbv q).Completion]
      rationalCyclotomicArtinLocalizedField m q :=
  finitePlaceLocalArtinMonoidHom
    (K := ℚ) (L := rationalCyclotomicArtinLevel m)
    (rationalCyclotomicArtinPlace q)
    (rationalCyclotomicArtinExtension m q) x

private noncomputable def rationalCyclotomicArtinGlobalFrobeniusOf
    (m : ℕ+) (q : Nat.Primes)
    (hUnramified :
      IsNonarchimedeanLocalField.IsUnramifiedValuedExtension
        (rationalCyclotomicArtinBaseAbv q).Completion
        (rationalCyclotomicArtinLocalizedField m q)) :
    rationalCyclotomicArtinLevel m ≃ₐ[ℚ]
      rationalCyclotomicArtinLevel m :=
  rationalCyclotomicArtinLocalToGlobalMonoidHom m q
    (rationalCyclotomicArtinLocalFrobeniusOf
      m q hUnramified)

/-- The global decomposition-group lift of arithmetic Frobenius at the
chosen place above `q`.  Keeping the local construction opaque prevents its
many completion instances from leaking into later theorem statements. -/
private noncomputable def rationalCyclotomicChosenArithmeticFrobenius
    (m : ℕ+) (q : Nat.Primes)
    (hq : ¬ q.1 ∣ (m : ℕ)) :
      KummerTheory.rationalCyclotomicLevel m ≃ₐ[ℚ]
      KummerTheory.rationalCyclotomicLevel m := by
  exact
    rationalCyclotomicArtinGlobalFrobeniusOf m q
      (rationalCyclotomicArtinUnramified m q hq)

private noncomputable abbrev rationalCyclotomicArtinLocalInput
    (q : Nat.Primes)
    (x : ((RayClass.rationalPrime q).adicCompletion ℚ)ˣ) :
    (rationalCyclotomicArtinBaseAbv q).Completionˣ :=
  finitePlaceLocalArtinInput
    (K := ℚ) (rationalCyclotomicArtinPlace q) x

/-- The normalized valuation of the canonical completion input used by the
rational finite-place Artin map.  This named endpoint keeps the completion
instances out of downstream theorem statements. -/
noncomputable def rationalCyclotomicArtinLocalExponent
    (q : Nat.Primes)
    (x : ((RayClass.rationalPrime q).adicCompletion ℚ)ˣ) : ℤ :=
  IsNonarchimedeanLocalField.valuationMap
    (rationalCyclotomicArtinBaseAbv q).Completion
    (Additive.ofMul (rationalCyclotomicArtinLocalInput q x))


/-- The Galois automorphism of the rational cyclotomic extension at level `m`
assigned to the nonzero `q`-adic input by the chosen finite-place Artin map. -/
noncomputable def rationalCyclotomicChosenFinitePlaceArtinValue
    (m : ℕ+) (q : Nat.Primes)
    (x : ((RayClass.rationalPrime q).adicCompletion ℚ)ˣ) :
    Gal(KummerTheory.rationalCyclotomicLevel m / ℚ) :=
  chosenFinitePlaceArtinMonoidHom
    (K := ℚ)
    (L := KummerTheory.rationalCyclotomicLevel m)
    (RayClass.rationalPrime q) x

private theorem rationalCyclotomicArtinLocalArtin_eq
    (m : ℕ+) (q : Nat.Primes)
    (x : ((RayClass.rationalPrime q).adicCompletion ℚ)ˣ) :
    rationalCyclotomicArtinLocalArtin m q x =
      @LocalClassFieldTheory.abelianLocalArtinMonoidHom
        (rationalCyclotomicArtinBaseAbv q).Completion
        (rationalCyclotomicArtinLocalizedField m q)
        (inferInstance : Field
          (rationalCyclotomicArtinBaseAbv q).Completion)
        (inferInstance : Field
          (rationalCyclotomicArtinLocalizedField m q))
        (finitePlaceLocalArtinLocalizedAlgebra
          (K := ℚ) (L := rationalCyclotomicArtinLevel m)
          (rationalCyclotomicArtinPlace q)
          (rationalCyclotomicArtinExtension m q))
        (finitePlaceLocalArtinCompletionValuativeRel
          (K := ℚ) (rationalCyclotomicArtinPlace q))
        (inferInstance : TopologicalSpace
          (rationalCyclotomicArtinBaseAbv q).Completion)
        (finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField
          (K := ℚ) (rationalCyclotomicArtinPlace q))
        (finitePlaceLocalArtinFiniteDimensional
          (K := ℚ) (L := rationalCyclotomicArtinLevel m)
          (rationalCyclotomicArtinPlace q)
          (rationalCyclotomicArtinExtension m q))
        (finitePlaceLocalArtinIsAbelianGalois
          (K := ℚ) (L := rationalCyclotomicArtinLevel m)
          (rationalCyclotomicArtinPlace q)
          (rationalCyclotomicArtinExtension m q)
          (inferInstance : FiniteDimensional ℚ
            (rationalCyclotomicArtinLevel m)))
        (finitePlaceLocalArtinInput
          (K := ℚ) (rationalCyclotomicArtinPlace q) x) := by
  unfold rationalCyclotomicArtinLocalArtin
  have h := finitePlaceLocalArtinMonoidHom_apply_normalized
    (K := ℚ) (L := rationalCyclotomicArtinLevel m)
    (rationalCyclotomicArtinPlace q)
    (rationalCyclotomicArtinExtension m q) x
  with_reducible exact h

private theorem rationalCyclotomicChosenArithmeticFrobenius_eq_lift
    (m : ℕ+) (q : Nat.Primes)
    (hq : ¬ q.1 ∣ (m : ℕ)) :
    rationalCyclotomicChosenArithmeticFrobenius m q hq =
      (absoluteValueDecompositionGroup ℚ
        (rationalCyclotomicArtinExtension m q).1).subtype
        ((rationalCyclotomicArtinDecompositionEquiv m q).symm
          (rationalCyclotomicArtinLocalFrobenius m q hq)) := by
  rfl

private theorem
    rationalCyclotomicFinitePlaceMappedLocalArtin_eq_frobenius_zpow_of
    (m : ℕ+) (q : Nat.Primes)
    (hAbelian :
      IsAbelianGalois
        (rationalCyclotomicArtinBaseAbv q).Completion
        (rationalCyclotomicArtinLocalizedField m q))
    (hUnramified :
      IsNonarchimedeanLocalField.IsUnramifiedValuedExtension
        (rationalCyclotomicArtinBaseAbv q).Completion
        (rationalCyclotomicArtinLocalizedField m q))
    (x : ((RayClass.rationalPrime q).adicCompletion ℚ)ˣ) :
    rationalCyclotomicArtinLocalToGlobalMonoidHom m q
        (LocalClassFieldTheory.abelianLocalArtinMonoidHom
          (rationalCyclotomicArtinBaseAbv q).Completion
          (rationalCyclotomicArtinLocalizedField m q)
          (rationalCyclotomicArtinLocalInput q x)) =
      (rationalCyclotomicArtinGlobalFrobeniusOf
        m q hUnramified) ^
        rationalCyclotomicArtinLocalExponent q x := by
  let := hAbelian
  let := hUnramified
  change
    rationalCyclotomicArtinLocalToGlobalMonoidHom m q
        (LocalClassFieldTheory.abelianLocalArtinMonoidHom
          (rationalCyclotomicArtinBaseAbv q).Completion
          (rationalCyclotomicArtinLocalizedField m q)
          (rationalCyclotomicArtinLocalInput q x)) =
      (rationalCyclotomicArtinLocalToGlobalMonoidHom m q
        (arithmeticFrobeniusOfUnramifiedValuation
          (rationalCyclotomicArtinBaseAbv q).Completion
          (rationalCyclotomicArtinLocalizedField m q))) ^
        rationalCyclotomicArtinLocalExponent q x
  exact
    mappedAbelianLocalArtin_eq_frobenius_zpow
      (F := (rationalCyclotomicArtinBaseAbv q).Completion)
      (E := rationalCyclotomicArtinLocalizedField m q)
      (rationalCyclotomicArtinLocalToGlobalMonoidHom m q)
      (rationalCyclotomicArtinLocalInput q x)

private theorem
    rationalCyclotomicFinitePlaceMappedLocalArtin_eq_frobenius_zpow
    (m : ℕ+) (q : Nat.Primes)
    (hq : ¬ q.1 ∣ (m : ℕ))
    (x : ((RayClass.rationalPrime q).adicCompletion ℚ)ˣ) :
    rationalCyclotomicArtinLocalToGlobalMonoidHom m q
        (rationalCyclotomicArtinLocalArtin m q x) =
      (rationalCyclotomicChosenArithmeticFrobenius m q hq) ^
        rationalCyclotomicArtinLocalExponent q x := by
  change
    rationalCyclotomicArtinLocalToGlobalMonoidHom m q
        (rationalCyclotomicArtinLocalArtin m q x) =
      (rationalCyclotomicArtinGlobalFrobeniusOf m q
        (rationalCyclotomicArtinUnramified m q hq)) ^
        rationalCyclotomicArtinLocalExponent q x
  calc
    rationalCyclotomicArtinLocalToGlobalMonoidHom m q
          (rationalCyclotomicArtinLocalArtin m q x) =
        rationalCyclotomicArtinLocalToGlobalMonoidHom m q
          (LocalClassFieldTheory.abelianLocalArtinMonoidHom
            (rationalCyclotomicArtinBaseAbv q).Completion
            (rationalCyclotomicArtinLocalizedField m q)
            (rationalCyclotomicArtinLocalInput q x)) :=
      congrArg
        (fun σ =>
          rationalCyclotomicArtinLocalToGlobalMonoidHom m q σ)
        (rationalCyclotomicArtinLocalArtin_eq m q x)
    _ =
        (rationalCyclotomicArtinGlobalFrobeniusOf m q
          (rationalCyclotomicArtinUnramified m q hq)) ^
          rationalCyclotomicArtinLocalExponent q x :=
      rationalCyclotomicFinitePlaceMappedLocalArtin_eq_frobenius_zpow_of
        m q (rationalCyclotomicArtinLocalizedIsAbelianGalois m q)
        (rationalCyclotomicArtinUnramified m q hq) x

/-- The chosen local Artin symbol is the chosen global Frobenius lift raised
to the normalized local valuation. -/
private theorem
    chosenFinitePlaceArtin_eq_chosenArithmeticFrobenius_zpow
    (m : ℕ+) (q : Nat.Primes)
    (hq : ¬ q.1 ∣ (m : ℕ))
    (x : ((RayClass.rationalPrime q).adicCompletion ℚ)ˣ) :
    chosenFinitePlaceArtinMonoidHom
        (K := ℚ) (L := rationalCyclotomicArtinLevel m)
        (rationalCyclotomicArtinPlace q) x =
      (rationalCyclotomicChosenArithmeticFrobenius m q hq) ^
        rationalCyclotomicArtinLocalExponent q x := by
  change
    finitePlaceArtinMonoidHomOfExtension
        (K := ℚ) (L := rationalCyclotomicArtinLevel m)
        (rationalCyclotomicArtinPlace q)
        (rationalCyclotomicArtinExtension m q) x =
      (rationalCyclotomicChosenArithmeticFrobenius m q hq) ^
        rationalCyclotomicArtinLocalExponent q x
  have hFactor :
      finitePlaceArtinMonoidHomOfExtension
          (K := ℚ) (L := rationalCyclotomicArtinLevel m)
          (rationalCyclotomicArtinPlace q)
          (rationalCyclotomicArtinExtension m q) x =
        rationalCyclotomicArtinLocalToGlobalMonoidHom m q
          (rationalCyclotomicArtinLocalArtin m q x) := by
    change
      finitePlaceArtinMonoidHomOfExtension
          (K := ℚ) (L := rationalCyclotomicArtinLevel m)
          (rationalCyclotomicArtinPlace q)
          (rationalCyclotomicArtinExtension m q) x =
        finitePlaceLocalToGlobalMonoidHom
          (K := ℚ) (L := rationalCyclotomicArtinLevel m)
          (rationalCyclotomicArtinPlace q)
          (rationalCyclotomicArtinExtension m q)
          (finitePlaceLocalArtinMonoidHom
            (K := ℚ) (L := rationalCyclotomicArtinLevel m)
            (rationalCyclotomicArtinPlace q)
            (rationalCyclotomicArtinExtension m q) x)
    exact
      congrArg
        (fun φ :
          ((rationalCyclotomicArtinPlace q).adicCompletion ℚ)ˣ →*
            (rationalCyclotomicArtinLevel m ≃ₐ[ℚ]
              rationalCyclotomicArtinLevel m) => φ x)
        (finitePlaceArtinMonoidHomOfExtension_factor
          (K := ℚ) (L := rationalCyclotomicArtinLevel m)
          (rationalCyclotomicArtinPlace q)
          (rationalCyclotomicArtinExtension m q))
  exact
    hFactor.trans
      (rationalCyclotomicFinitePlaceMappedLocalArtin_eq_frobenius_zpow
        m q hq x)

private theorem rationalCyclotomicArtinResidueFieldCard
    (q : Nat.Primes) :
    Nat.card 𝓀[(rationalCyclotomicArtinBaseAbv q).Completion] = q.1 := by
  simpa [rationalCyclotomicArtinPlace,
    rationalCyclotomicArtinBaseAbv] using
    rationalFinitePlaceCompletion_residueField_card
      (rationalCyclotomicArtinPlace q)

private theorem rationalCyclotomicArtinLocalFrobenius_apply_root
    (m : ℕ+) (q : Nat.Primes)
    (hq : ¬ q.1 ∣ (m : ℕ)) :
    rationalCyclotomicArtinLocalFrobenius m q hq
        (rationalCyclotomicLocalizedPrimitiveRoot
          m (rationalCyclotomicArtinPlace q)) =
      (rationalCyclotomicLocalizedPrimitiveRoot
        m (rationalCyclotomicArtinPlace q)) ^ q.1 := by
  let := rationalCyclotomicArtinUnramified m q hq
  have hRoot :
      IsPrimitiveRoot
        (rationalCyclotomicLocalizedPrimitiveRoot
          m (rationalCyclotomicArtinPlace q)) (m : ℕ) :=
    rationalCyclotomicLocalizedPrimitiveRoot_isPrimitiveRoot
      m (rationalCyclotomicArtinPlace q)
  have hCoprime :
      (Nat.card
        𝓀[(rationalCyclotomicArtinBaseAbv q).Completion]).Coprime
          (m : ℕ) := by
    rw [rationalCyclotomicArtinResidueFieldCard q]
    exact q.2.coprime_iff_not_dvd.mpr hq
  exact
    (arithmeticFrobeniusOfUnramifiedValuation_apply_primitiveRoot
      (rationalCyclotomicArtinBaseAbv q).Completion
      (rationalCyclotomicArtinLocalizedField m q)
      hRoot hCoprime).trans
      (congrArg
        (fun n : ℕ => (rationalCyclotomicLocalizedPrimitiveRoot
          m (rationalCyclotomicArtinPlace q)) ^ n)
        (rationalCyclotomicArtinResidueFieldCard q))

private theorem rationalCyclotomicArtinFrobeniusLift_localization
    (m : ℕ+) (q : Nat.Primes)
    (hq : ¬ q.1 ∣ (m : ℕ)) :
    AbsoluteValue.toAlgebraicLocalization
        (rationalCyclotomicArtinBaseAbv q)
        (rationalCyclotomicArtinExtension m q).1
        (rationalCyclotomicArtinExtension m q).2
        (((absoluteValueDecompositionGroup ℚ
          (rationalCyclotomicArtinExtension m q).1).subtype
          ((rationalCyclotomicArtinDecompositionEquiv m q).symm
            (rationalCyclotomicArtinLocalFrobenius m q hq)))
          (rationalCyclotomicLevelPrimitiveRoot m)) =
      rationalCyclotomicArtinLocalFrobenius m q hq
        (AbsoluteValue.toAlgebraicLocalization
          (rationalCyclotomicArtinBaseAbv q)
          (rationalCyclotomicArtinExtension m q).1
          (rationalCyclotomicArtinExtension m q).2
          (rationalCyclotomicLevelPrimitiveRoot m)) := by
  calc
    AbsoluteValue.toAlgebraicLocalization
        (rationalCyclotomicArtinBaseAbv q)
        (rationalCyclotomicArtinExtension m q).1
        (rationalCyclotomicArtinExtension m q).2
        (((absoluteValueDecompositionGroup ℚ
          (rationalCyclotomicArtinExtension m q).1).subtype
          ((rationalCyclotomicArtinDecompositionEquiv m q).symm
            (rationalCyclotomicArtinLocalFrobenius m q hq)))
          (rationalCyclotomicLevelPrimitiveRoot m)) =
      rationalCyclotomicArtinDecompositionEquiv m q
          ((rationalCyclotomicArtinDecompositionEquiv m q).symm
            (rationalCyclotomicArtinLocalFrobenius m q hq))
        (AbsoluteValue.toAlgebraicLocalization
          (rationalCyclotomicArtinBaseAbv q)
          (rationalCyclotomicArtinExtension m q).1
          (rationalCyclotomicArtinExtension m q).2
          (rationalCyclotomicLevelPrimitiveRoot m)) :=
      (localizationRamificationGroups_decompositionGroupEquiv_toLocalization
        (rationalCyclotomicArtinBaseAbv q)
        (RayClass.adicAbv_isNontrivial
          (rationalCyclotomicArtinPlace q))
        (rationalCyclotomicArtinExtension m q)
        ((rationalCyclotomicArtinDecompositionEquiv m q).symm
          (rationalCyclotomicArtinLocalFrobenius m q hq))
        (rationalCyclotomicLevelPrimitiveRoot m)).symm
    _ = rationalCyclotomicArtinLocalFrobenius m q hq
        (AbsoluteValue.toAlgebraicLocalization
          (rationalCyclotomicArtinBaseAbv q)
          (rationalCyclotomicArtinExtension m q).1
          (rationalCyclotomicArtinExtension m q).2
          (rationalCyclotomicLevelPrimitiveRoot m)) :=
      congrArg
        (fun σ : rationalCyclotomicArtinLocalizedField m q ≃ₐ[
          (rationalCyclotomicArtinBaseAbv q).Completion]
          rationalCyclotomicArtinLocalizedField m q =>
            σ (AbsoluteValue.toAlgebraicLocalization
              (rationalCyclotomicArtinBaseAbv q)
              (rationalCyclotomicArtinExtension m q).1
              (rationalCyclotomicArtinExtension m q).2
              (rationalCyclotomicLevelPrimitiveRoot m)))
        ((rationalCyclotomicArtinDecompositionEquiv m q).apply_symm_apply
          (rationalCyclotomicArtinLocalFrobenius m q hq))

private theorem rationalCyclotomicChosenArithmeticFrobenius_localization
    (m : ℕ+) (q : Nat.Primes)
    (hq : ¬ q.1 ∣ (m : ℕ)) :
    AbsoluteValue.toAlgebraicLocalization
        (rationalCyclotomicArtinBaseAbv q)
        (rationalCyclotomicArtinExtension m q).1
        (rationalCyclotomicArtinExtension m q).2
        (rationalCyclotomicChosenArithmeticFrobenius m q hq
          (rationalCyclotomicLevelPrimitiveRoot m)) =
      rationalCyclotomicArtinLocalFrobenius m q hq
        (AbsoluteValue.toAlgebraicLocalization
          (rationalCyclotomicArtinBaseAbv q)
          (rationalCyclotomicArtinExtension m q).1
          (rationalCyclotomicArtinExtension m q).2
          (rationalCyclotomicLevelPrimitiveRoot m)) := by
  calc
    AbsoluteValue.toAlgebraicLocalization
        (rationalCyclotomicArtinBaseAbv q)
        (rationalCyclotomicArtinExtension m q).1
        (rationalCyclotomicArtinExtension m q).2
        (rationalCyclotomicChosenArithmeticFrobenius m q hq
          (rationalCyclotomicLevelPrimitiveRoot m)) =
      AbsoluteValue.toAlgebraicLocalization
        (rationalCyclotomicArtinBaseAbv q)
        (rationalCyclotomicArtinExtension m q).1
        (rationalCyclotomicArtinExtension m q).2
        (((absoluteValueDecompositionGroup ℚ
          (rationalCyclotomicArtinExtension m q).1).subtype
          ((rationalCyclotomicArtinDecompositionEquiv m q).symm
            (rationalCyclotomicArtinLocalFrobenius m q hq)))
          (rationalCyclotomicLevelPrimitiveRoot m)) :=
      congrArg
        (fun σ : rationalCyclotomicArtinLevel m ≃ₐ[ℚ]
          rationalCyclotomicArtinLevel m =>
            AbsoluteValue.toAlgebraicLocalization
              (rationalCyclotomicArtinBaseAbv q)
              (rationalCyclotomicArtinExtension m q).1
              (rationalCyclotomicArtinExtension m q).2
              (σ (rationalCyclotomicLevelPrimitiveRoot m)))
        (rationalCyclotomicChosenArithmeticFrobenius_eq_lift m q hq)
    _ = rationalCyclotomicArtinLocalFrobenius m q hq
        (AbsoluteValue.toAlgebraicLocalization
          (rationalCyclotomicArtinBaseAbv q)
          (rationalCyclotomicArtinExtension m q).1
          (rationalCyclotomicArtinExtension m q).2
          (rationalCyclotomicLevelPrimitiveRoot m)) :=
      rationalCyclotomicArtinFrobeniusLift_localization m q hq

private theorem rationalCyclotomicArtinPrimitiveRoot_localization
    (m : ℕ+) (q : Nat.Primes) :
    AbsoluteValue.toAlgebraicLocalization
        (rationalCyclotomicArtinBaseAbv q)
        (rationalCyclotomicArtinExtension m q).1
        (rationalCyclotomicArtinExtension m q).2
        (rationalCyclotomicLevelPrimitiveRoot m) =
      rationalCyclotomicLocalizedPrimitiveRoot
        m (rationalCyclotomicArtinPlace q) := by
  rfl

private theorem rationalCyclotomicArtinLocalizedRoot_pow
    (m : ℕ+) (q : Nat.Primes) :
    (rationalCyclotomicLocalizedPrimitiveRoot
        m (rationalCyclotomicArtinPlace q)) ^ q.1 =
      rationalCyclotomicGlobalToLocalizedAlgHom
        m (rationalCyclotomicArtinPlace q)
        (rationalCyclotomicLevelPrimitiveRoot m ^ q.1) := by
  calc
    (rationalCyclotomicLocalizedPrimitiveRoot
        m (rationalCyclotomicArtinPlace q)) ^ q.1 =
      (rationalCyclotomicGlobalToLocalizedAlgHom
        m (rationalCyclotomicArtinPlace q)
        (rationalCyclotomicLevelPrimitiveRoot m)) ^ q.1 :=
      congrArg (fun z => z ^ q.1)
        (rationalCyclotomicGlobalToLocalizedAlgHom_primitiveRoot m
          (rationalCyclotomicArtinPlace q)).symm
    _ = rationalCyclotomicGlobalToLocalizedAlgHom
        m (rationalCyclotomicArtinPlace q)
        (rationalCyclotomicLevelPrimitiveRoot m ^ q.1) :=
      (map_pow
        (rationalCyclotomicGlobalToLocalizedAlgHom
          m (rationalCyclotomicArtinPlace q))
        (rationalCyclotomicLevelPrimitiveRoot m) q.1).symm

private theorem rationalCyclotomicChosenArithmeticFrobenius_apply_root
    (m : ℕ+) (q : Nat.Primes)
    (hq : ¬ q.1 ∣ (m : ℕ)) :
    rationalCyclotomicChosenArithmeticFrobenius m q hq
        (rationalCyclotomicLevelPrimitiveRoot m) =
      rationalCyclotomicLevelPrimitiveRoot m ^ q.1 := by
  apply
    (AbsoluteValue.toAlgebraicLocalization
      (rationalCyclotomicArtinBaseAbv q)
      (rationalCyclotomicArtinExtension m q).1
      (rationalCyclotomicArtinExtension m q).2).injective
  have hLocalization :
      AbsoluteValue.toAlgebraicLocalization
        (rationalCyclotomicArtinBaseAbv q)
        (rationalCyclotomicArtinExtension m q).1
        (rationalCyclotomicArtinExtension m q).2
        (rationalCyclotomicChosenArithmeticFrobenius m q hq
          (rationalCyclotomicLevelPrimitiveRoot m)) =
      rationalCyclotomicArtinLocalFrobenius m q hq
        (AbsoluteValue.toAlgebraicLocalization
          (rationalCyclotomicArtinBaseAbv q)
          (rationalCyclotomicArtinExtension m q).1
          (rationalCyclotomicArtinExtension m q).2
          (rationalCyclotomicLevelPrimitiveRoot m)) :=
    rationalCyclotomicChosenArithmeticFrobenius_localization m q hq
  have hPrimitiveRoot :
      rationalCyclotomicArtinLocalFrobenius m q hq
        (AbsoluteValue.toAlgebraicLocalization
          (rationalCyclotomicArtinBaseAbv q)
          (rationalCyclotomicArtinExtension m q).1
          (rationalCyclotomicArtinExtension m q).2
          (rationalCyclotomicLevelPrimitiveRoot m)) =
      rationalCyclotomicArtinLocalFrobenius m q hq
        (rationalCyclotomicLocalizedPrimitiveRoot
          m (rationalCyclotomicArtinPlace q)) :=
    congrArg
      (rationalCyclotomicArtinLocalFrobenius m q hq)
      (rationalCyclotomicArtinPrimitiveRoot_localization m q)
  have hLocalFrobenius :
      rationalCyclotomicArtinLocalFrobenius m q hq
          (rationalCyclotomicLocalizedPrimitiveRoot
            m (rationalCyclotomicArtinPlace q)) =
        (rationalCyclotomicLocalizedPrimitiveRoot
          m (rationalCyclotomicArtinPlace q)) ^ q.1 :=
    rationalCyclotomicArtinLocalFrobenius_apply_root m q hq
  have hPower :
      (rationalCyclotomicLocalizedPrimitiveRoot
          m (rationalCyclotomicArtinPlace q)) ^ q.1 =
        rationalCyclotomicGlobalToLocalizedAlgHom
          m (rationalCyclotomicArtinPlace q)
          (rationalCyclotomicLevelPrimitiveRoot m ^ q.1) :=
    rationalCyclotomicArtinLocalizedRoot_pow m q
  have hAlgebraicLocalization :
      rationalCyclotomicGlobalToLocalizedAlgHom
          m (rationalCyclotomicArtinPlace q)
          (rationalCyclotomicLevelPrimitiveRoot m ^ q.1) =
        AbsoluteValue.toAlgebraicLocalization
          (rationalCyclotomicArtinBaseAbv q)
          (rationalCyclotomicArtinExtension m q).1
          (rationalCyclotomicArtinExtension m q).2
          (rationalCyclotomicLevelPrimitiveRoot m ^ q.1) :=
    rationalCyclotomicGlobalToLocalizedAlgHom_apply
      m (rationalCyclotomicArtinPlace q)
      (rationalCyclotomicLevelPrimitiveRoot m ^ q.1)
  exact
    Eq.trans hLocalization
      (Eq.trans hPrimitiveRoot
        (Eq.trans hLocalFrobenius
          (Eq.trans hPower hAlgebraicLocalization)))

/-- The cyclotomic character sends the chosen arithmetic Frobenius lift to
the residue prime. -/
private theorem galEquivZMod_chosenArithmeticFrobenius
    (m : ℕ+) (q : Nat.Primes)
    (hq : ¬ q.1 ∣ (m : ℕ)) :
    IsCyclotomicExtension.Rat.galEquivZMod
        (m : ℕ) (KummerTheory.rationalCyclotomicLevel m)
        (rationalCyclotomicChosenArithmeticFrobenius m q hq) =
      ZMod.unitOfCoprime q.1
        (q.2.coprime_iff_not_dvd.mpr hq) := by
  exact
    rationalCyclotomicLevel_galEquivZMod_eq_unitOfCoprime
      m q hq (rationalCyclotomicChosenArithmeticFrobenius m q hq)
      (rationalCyclotomicChosenArithmeticFrobenius_apply_root m q hq)

/-- At a rational prime not dividing the level, the cyclotomic character
of the chosen finite-place Artin symbol is the residue prime raised to the
normalized local valuation. -/
theorem galEquivZMod_chosenFinitePlaceArtinMonoidHom_of_not_dvd
    (m : ℕ+) (q : Nat.Primes)
    (hq : ¬ q.1 ∣ (m : ℕ))
    (x : ((RayClass.rationalPrime q).adicCompletion ℚ)ˣ) :
    let v : HeightOneSpectrum (𝓞 ℚ) :=
      RayClass.rationalPrime q
    let L := KummerTheory.rationalCyclotomicLevel m
    let vQ := HeightOneSpectrum.adicAbv ℚ v
    let localInput :=
      (finitePlaceCompletionUnitsContinuousMulEquiv v).symm x
    let localExponent :=
      LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap
        vQ.Completion (Additive.ofMul localInput)
    IsCyclotomicExtension.Rat.galEquivZMod
        (m : ℕ) L
        (chosenFinitePlaceArtinMonoidHom
          (K := ℚ)
          (L := L) v x) =
      (ZMod.unitOfCoprime q.1
        (q.2.coprime_iff_not_dvd.mpr hq)) ^ localExponent := by
  dsimp only
  rw [chosenFinitePlaceArtin_eq_chosenArithmeticFrobenius_zpow
      m q hq x, map_zpow,
    galEquivZMod_chosenArithmeticFrobenius m q hq]
  rfl

/-- Away from the cyclotomic level, a finite-place input of normalized
valuation zero has trivial cyclotomic character. -/
theorem
    galEquivZMod_chosenFinitePlaceArtinMonoidHom_eq_one_of_not_dvd_of_localExponent_eq_zero
    (m : ℕ+) (q : Nat.Primes)
    (hq : ¬ q.1 ∣ (m : ℕ))
    (x : ((RayClass.rationalPrime q).adicCompletion ℚ)ˣ)
    (hzero : rationalCyclotomicArtinLocalExponent q x = 0) :
    IsCyclotomicExtension.Rat.galEquivZMod
        (m : ℕ) (KummerTheory.rationalCyclotomicLevel m)
        (chosenFinitePlaceArtinMonoidHom
          (K := ℚ)
          (L := KummerTheory.rationalCyclotomicLevel m)
          (RayClass.rationalPrime q) x) =
      1 := by
  rw [chosenFinitePlaceArtin_eq_chosenArithmeticFrobenius_zpow
      m q hq x,
    map_zpow, galEquivZMod_chosenArithmeticFrobenius m q hq,
    hzero, zpow_zero]

/-- Away from the cyclotomic level, valuation zero makes the chosen
finite-place Artin symbol itself trivial.  Returning the Galois element,
rather than an equality between cyclotomic characters with frozen instance
arguments, lets downstream restriction arguments apply their own canonical
character without a dependent instance transport. -/
theorem
    chosenFinitePlaceArtinMonoidHom_eq_one_of_not_dvd_of_localExponent_eq_zero
    (m : ℕ+) (q : Nat.Primes)
    (hq : ¬ q.1 ∣ (m : ℕ))
    (x : ((RayClass.rationalPrime q).adicCompletion ℚ)ˣ)
    (hzero : rationalCyclotomicArtinLocalExponent q x = 0) :
    chosenFinitePlaceArtinMonoidHom
        (K := ℚ)
        (L := KummerTheory.rationalCyclotomicLevel m)
        (RayClass.rationalPrime q) x =
      1 := by
  apply
    (IsCyclotomicExtension.Rat.galEquivZMod
      (m : ℕ) (KummerTheory.rationalCyclotomicLevel m)).injective
  simpa only [map_one] using
    galEquivZMod_chosenFinitePlaceArtinMonoidHom_eq_one_of_not_dvd_of_localExponent_eq_zero
      m q hq x hzero

/-- For a rational principal idele, the unramified finite-place
cyclotomic Artin symbol at `q` is `q` raised to the negative usual
`q`-adic exponent. -/
theorem
    galEquivZMod_chosenFinitePlaceArtinMonoidHom_principal_of_not_dvd
    (m : ℕ+) (q : Nat.Primes)
    (hq : ¬ q.1 ∣ (m : ℕ)) (x : ℚˣ) :
    IsCyclotomicExtension.Rat.galEquivZMod
        (m : ℕ)
        (KummerTheory.rationalCyclotomicLevel m)
        (chosenFinitePlaceArtinMonoidHom
          (K := ℚ)
          (L := KummerTheory.rationalCyclotomicLevel m)
          (RayClass.rationalPrime q)
          (IdeleGroup.finiteComponent
            (RayClass.rationalPrime q)
            (IdeleGroup.principalIdele ℚ x))) =
      (ZMod.unitOfCoprime q.1
        (q.2.coprime_iff_not_dvd.mpr hq)) ^
          (-padicValRat q.1 (x : ℚ)) := by
  rw [
    galEquivZMod_chosenFinitePlaceArtinMonoidHom_of_not_dvd
      m q hq,
    rationalPrincipalFiniteComponent_valuationMap]

end Reciprocity
end GlobalClassFieldTheory
