/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.RationalCyclotomicFinitePlaceArtinBase


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

/-- The finite place of `ℚ` determined by the rational prime `q`. -/
abbrev rationalCyclotomicArtinPlace (q : Nat.Primes) :
    HeightOneSpectrum (𝓞 ℚ) :=
  RayClass.rationalPrime q

/-- The `q`-adic absolute value on `ℚ` used for the finite-place Artin map. -/
abbrev rationalCyclotomicArtinBaseAbv (q : Nat.Primes) :
    AbsoluteValue ℚ ℝ :=
  HeightOneSpectrum.adicAbv ℚ (rationalCyclotomicArtinPlace q)

/-- The rational cyclotomic extension at the positive level `m`. -/
abbrev rationalCyclotomicArtinLevel (m : ℕ+) :=
  KummerTheory.rationalCyclotomicLevel m

/-- A chosen extension of the `q`-adic absolute value to the cyclotomic field. -/
abbrev rationalCyclotomicArtinExtension
    (m : ℕ+) (q : Nat.Primes) :
    AbsoluteValueExtension
      (rationalCyclotomicArtinBaseAbv q)
      (rationalCyclotomicArtinLevel m) :=
  chosenFinitePlaceExtension
    (L := rationalCyclotomicArtinLevel m)
    (rationalCyclotomicArtinPlace q)

/-- The local completion of the cyclotomic field at the chosen place above `q`. -/
abbrev rationalCyclotomicArtinLocalizedField
    (m : ℕ+) (q : Nat.Primes) :=
  AlgebraicNumberTheory.Valuations.LocalizedCompletion
    (rationalCyclotomicArtinBaseAbv q)
    (rationalCyclotomicArtinExtension m q)

@[reducible]
noncomputable local instance rationalCyclotomicArtinExtensionAlgebra
    (m : ℕ+) (q : Nat.Primes) :
    Algebra ℚ
      (rationalCyclotomicArtinExtension m q).1.Completion :=
  AbsoluteValue.extensionCompletionAlgebra
    (K := ℚ) (rationalCyclotomicArtinExtension m q).1

@[reducible]
noncomputable local instance rationalCyclotomicArtinExtensionSMul
    (m : ℕ+) (q : Nat.Primes) :
    SMul ℚ
      (rationalCyclotomicArtinExtension m q).1.Completion :=
  (rationalCyclotomicArtinExtensionAlgebra m q).toSMul

@[reducible]
noncomputable local instance
    rationalCyclotomicArtinCompletionAlgebra
    (m : ℕ+) (q : Nat.Primes) :
    Algebra (rationalCyclotomicArtinBaseAbv q).Completion
      (rationalCyclotomicArtinExtension m q).1.Completion :=
  AbsoluteValue.completionAlgebra
    (rationalCyclotomicArtinBaseAbv q)
    (rationalCyclotomicArtinExtension m q).1
    (rationalCyclotomicArtinExtension m q).2

@[reducible]
noncomputable local instance rationalCyclotomicArtinLocalizedAlgebra
    (m : ℕ+) (q : Nat.Primes) :
    Algebra (rationalCyclotomicArtinBaseAbv q).Completion
      (rationalCyclotomicArtinLocalizedField m q) :=
  finitePlaceLocalArtinLocalizedAlgebra
    (K := ℚ) (L := rationalCyclotomicArtinLevel m)
    (rationalCyclotomicArtinPlace q)
    (rationalCyclotomicArtinExtension m q)

noncomputable local instance
    rationalCyclotomicArtinLocalizedGlobalAlgebra
    (m : ℕ+) (q : Nat.Primes) :
    Algebra ℚ (rationalCyclotomicArtinLocalizedField m q) :=
  LocalClassFieldTheory.localizedCompletionGlobalAlgebra
    (rationalCyclotomicArtinBaseAbv q)
    (rationalCyclotomicArtinExtension m q)

noncomputable local instance
    rationalCyclotomicArtinLocalizedGlobalSMul
    (m : ℕ+) (q : Nat.Primes) :
    SMul ℚ (rationalCyclotomicArtinLocalizedField m q) :=
  (rationalCyclotomicArtinLocalizedGlobalAlgebra m q).toSMul

noncomputable local instance
    rationalCyclotomicArtinLocalizedScalarTower
    (m : ℕ+) (q : Nat.Primes) :
    IsScalarTower ℚ
      (rationalCyclotomicArtinBaseAbv q).Completion
      (rationalCyclotomicArtinLocalizedField m q) := by
  constructor
  intro r x y
  simp only [Algebra.smul_def, map_mul, eq_ratCast,
    map_ratCast, mul_assoc]

noncomputable local instance
    rationalCyclotomicArtinLocalizedFiniteDimensional
    (m : ℕ+) (q : Nat.Primes) :
    FiniteDimensional
      (rationalCyclotomicArtinBaseAbv q).Completion
      (rationalCyclotomicArtinLocalizedField m q) :=
  finitePlaceLocalArtinFiniteDimensional
    (K := ℚ) (L := rationalCyclotomicArtinLevel m)
    (rationalCyclotomicArtinPlace q)
    (rationalCyclotomicArtinExtension m q)

noncomputable local instance
    rationalCyclotomicArtinLocalizedIsAbelianGalois
    (m : ℕ+) (q : Nat.Primes) :
    IsAbelianGalois
      (rationalCyclotomicArtinBaseAbv q).Completion
      (rationalCyclotomicArtinLocalizedField m q) :=
  finitePlaceLocalArtinIsAbelianGalois
    (K := ℚ) (L := rationalCyclotomicArtinLevel m)
    (rationalCyclotomicArtinPlace q)
    (rationalCyclotomicArtinExtension m q)
    (inferInstance :
      FiniteDimensional ℚ (rationalCyclotomicArtinLevel m))

noncomputable local instance
    rationalCyclotomicArtinLocalizedIsSeparable
    (m : ℕ+) (q : Nat.Primes) :
    Algebra.IsSeparable
      (rationalCyclotomicArtinBaseAbv q).Completion
      (rationalCyclotomicArtinLocalizedField m q) :=
  (rationalCyclotomicArtinLocalizedIsAbelianGalois m q).toIsGalois.to_isSeparable

noncomputable local instance
    rationalCyclotomicArtinLocalizedIsCyclotomic
    (m : ℕ+) (q : Nat.Primes) :
    IsCyclotomicExtension {(m : ℕ)}
      (rationalCyclotomicArtinBaseAbv q).Completion
      (rationalCyclotomicArtinLocalizedField m q) :=
  rationalCyclotomicLevel_localizedCompletion_isCyclotomicExtension
    m (rationalCyclotomicArtinPlace q)

noncomputable local instance
    rationalCyclotomicArtinExtensionFiniteDimensional
    (m : ℕ+) (q : Nat.Primes) :
    FiniteDimensional
      (rationalCyclotomicArtinBaseAbv q).Completion
      (rationalCyclotomicArtinExtension m q).1.Completion :=
  completionModuleFinite
    (rationalCyclotomicArtinBaseAbv q)
    (RayClass.adicAbv_isNontrivial
      (rationalCyclotomicArtinPlace q))
    (rationalCyclotomicArtinExtension m q)

noncomputable local instance
    rationalCyclotomicArtinExtensionContinuousSMul
    (m : ℕ+) (q : Nat.Primes) :
    ContinuousSMul
      (rationalCyclotomicArtinBaseAbv q).Completion
      (rationalCyclotomicArtinExtension m q).1.Completion :=
  continuousSMul_of_algebraMap _ _
    (AbsoluteValue.completionMap_isometry
      (rationalCyclotomicArtinBaseAbv q)
      (rationalCyclotomicArtinExtension m q).1
      (rationalCyclotomicArtinExtension m q).2).continuous

noncomputable local instance
    rationalCyclotomicArtinExtensionLocallyCompact
    (m : ℕ+) (q : Nat.Primes) :
    LocallyCompactSpace
      (rationalCyclotomicArtinExtension m q).1.Completion :=
  LocallyCompactSpace.of_finiteDimensional_of_complete
    (rationalCyclotomicArtinBaseAbv q).Completion
    (rationalCyclotomicArtinExtension m q).1.Completion

private noncomputable def
    rationalCyclotomicArtinLocalizedEquivCompletion
    (m : ℕ+) (q : Nat.Primes) :
    rationalCyclotomicArtinLocalizedField m q ≃ᵢ
      (rationalCyclotomicArtinExtension m q).1.Completion :=
  { toEquiv :=
      (localizedCompletionEquivCompletion
        (rationalCyclotomicArtinBaseAbv q)
        (RayClass.adicAbv_isNontrivial
          (rationalCyclotomicArtinPlace q))
        (rationalCyclotomicArtinExtension m q)).toEquiv
    isometry_toFun :=
      Isometry.of_dist_eq fun _ _ => rfl }

noncomputable local instance
    rationalCyclotomicArtinLocalizedLocallyCompact
    (m : ℕ+) (q : Nat.Primes) :
    LocallyCompactSpace
      (rationalCyclotomicArtinLocalizedField m q) :=
  ((rationalCyclotomicArtinLocalizedEquivCompletion m q).toHomeomorph.locallyCompactSpace_iff).2
    inferInstance

noncomputable local instance
    rationalCyclotomicArtinLocalizedIsUltrametricDist
    (m : ℕ+) (q : Nat.Primes) :
    IsUltrametricDist
      (rationalCyclotomicArtinLocalizedField m q) :=
  localizedCompletionIsUltrametricDist
    (rationalCyclotomicArtinBaseAbv q)
    (rationalCyclotomicArtinExtension m q)
    (HeightOneSpectrum.isNonarchimedean_adicAbv
      ℚ (rationalCyclotomicArtinPlace q))

noncomputable local instance rationalCyclotomicArtinLocalizedValued
    (m : ℕ+) (q : Nat.Primes) :
    Valued (rationalCyclotomicArtinLocalizedField m q) ℝ≥0 :=
  localizedCompletionFinitePlaceValued
    (rationalCyclotomicArtinBaseAbv q)
    (rationalCyclotomicArtinExtension m q)
    (HeightOneSpectrum.isNonarchimedean_adicAbv
      ℚ (rationalCyclotomicArtinPlace q))

@[reducible]
noncomputable local instance
    rationalCyclotomicArtinLocalizedValuativeRel
    (m : ℕ+) (q : Nat.Primes) :
    ValuativeRel (rationalCyclotomicArtinLocalizedField m q) :=
  localizedCompletionFinitePlaceValuativeRel
    (rationalCyclotomicArtinBaseAbv q)
    (rationalCyclotomicArtinExtension m q)
    (HeightOneSpectrum.isNonarchimedean_adicAbv
      ℚ (rationalCyclotomicArtinPlace q))

noncomputable local instance
    rationalCyclotomicArtinLocalizedValuationCompatible
    (m : ℕ+) (q : Nat.Primes) :
    (Valued.v : Valuation
      (rationalCyclotomicArtinLocalizedField m q) ℝ≥0).Compatible :=
  Valuation.Compatible.ofValuation _

noncomputable local instance
    rationalCyclotomicArtinLocalizedValuationHasExtension
    (m : ℕ+) (q : Nat.Primes) :
    Valuation.HasExtension
      (ValuativeRel.valuation
        (rationalCyclotomicArtinBaseAbv q).Completion)
      (ValuativeRel.valuation
        (rationalCyclotomicArtinLocalizedField m q)) :=
  localizedCompletionValuationHasExtension
    (rationalCyclotomicArtinBaseAbv q)
    (rationalCyclotomicArtinExtension m q)
    (HeightOneSpectrum.isNonarchimedean_adicAbv
      ℚ (rationalCyclotomicArtinPlace q))

noncomputable local instance
    rationalCyclotomicArtinLocalizedValuationIsNontrivial
    (m : ℕ+) (q : Nat.Primes) :
    (ValuativeRel.valuation
      (rationalCyclotomicArtinLocalizedField m q)).IsNontrivial :=
  Valuation.IsNontrivial.of_hasExtension
    (ValuativeRel.valuation
      (rationalCyclotomicArtinBaseAbv q).Completion)
    (ValuativeRel.valuation
      (rationalCyclotomicArtinLocalizedField m q))

noncomputable local instance
    rationalCyclotomicArtinLocalizedValuativeRelIsNontrivial
    (m : ℕ+) (q : Nat.Primes) :
    ValuativeRel.IsNontrivial
      (rationalCyclotomicArtinLocalizedField m q) :=
  (ValuativeRel.isNontrivial_iff_isNontrivial
    (ValuativeRel.valuation
      (rationalCyclotomicArtinLocalizedField m q))).2 inferInstance

noncomputable local instance
    rationalCyclotomicArtinLocalizedIsValuativeTopology
    (m : ℕ+) (q : Nat.Primes) :
    IsValuativeTopology
      (rationalCyclotomicArtinLocalizedField m q) :=
  isValuativeTopology_of_valued_ofValuation
    (rationalCyclotomicArtinLocalizedField m q) ℝ≥0

noncomputable local instance
    rationalCyclotomicArtinLocalizedIsNonarchimedeanLocalField
    (m : ℕ+) (q : Nat.Primes) :
    IsNonarchimedeanLocalField
      (rationalCyclotomicArtinLocalizedField m q) :=
  { toIsValuativeTopology := inferInstance
    toLocallyCompactSpace := inferInstance
    toIsNontrivial := inferInstance }

noncomputable local instance
    rationalCyclotomicArtinLocalizedIntegerAlgebra
    (m : ℕ+) (q : Nat.Primes) :
    Algebra
      𝒪[(rationalCyclotomicArtinBaseAbv q).Completion]
      (rationalCyclotomicArtinLocalizedField m q) :=
  Algebra.ofSubsemiring
    𝒪[(rationalCyclotomicArtinBaseAbv q).Completion]

noncomputable local instance
    rationalCyclotomicArtinLocalizedIsIntegralClosure
    (m : ℕ+) (q : Nat.Primes) :
    IsIntegralClosure
      𝒪[rationalCyclotomicArtinLocalizedField m q]
      𝒪[(rationalCyclotomicArtinBaseAbv q).Completion]
      (rationalCyclotomicArtinLocalizedField m q) :=
  localizedCompletionIsIntegralClosureWithExtension
    (rationalCyclotomicArtinBaseAbv q)
    (rationalCyclotomicArtinExtension m q)
    (RayClass.adicAbv_isNontrivial
      (rationalCyclotomicArtinPlace q))
    (HeightOneSpectrum.isNonarchimedean_adicAbv
      ℚ (rationalCyclotomicArtinPlace q))

noncomputable local instance
    rationalCyclotomicArtinLocalizedIntegerModuleFinite
    (m : ℕ+) (q : Nat.Primes) :
    Module.Finite
      𝒪[(rationalCyclotomicArtinBaseAbv q).Completion]
      𝒪[rationalCyclotomicArtinLocalizedField m q] :=
  integerRing_moduleFinite_of_isIntegralClosure
    (rationalCyclotomicArtinBaseAbv q).Completion
    (rationalCyclotomicArtinLocalizedField m q)


end Reciprocity
end GlobalClassFieldTheory
