/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.RationalCyclotomicFinitePlaceArtinAction


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

section RationalCyclotomicPrincipalPrime

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
  rationalCyclotomicPrincipalPrimeLevelIsCyclotomicExtension
  rationalCyclotomicArtinLocalizedPadicAlgebra
  rationalCyclotomicArtinLocalizedPadicScalarTower
  rationalCyclotomicPrincipalPrimePadicLevelIsAbelianGalois
  rationalPrimeFactorCompletionPadicAlgebra
  rationalCyclotomicPrincipalPrimePadicLevelFiniteDimensional

private theorem
    rationalCyclotomicPrincipalPrime_padicUnitParameterArtin_action
    (p : Nat.Primes) (n : ℕ) (x : ℚˣ) :
    rationalCyclotomicPrincipalPrimePadicUnitParameterArtin p n x
        (rationalCyclotomicLocalizedCompletionPadicAlgEquiv p n
          (rationalCyclotomicPrincipalPrimeLocalizedRoot p n)) =
      (rationalCyclotomicLocalizedCompletionPadicAlgEquiv p n
        (rationalCyclotomicPrincipalPrimeLocalizedRoot p n)) ^
        (rationalCyclotomicPrincipalPrimeResidueUnit p n x).val.val := by
  let m := rationalCyclotomicPrincipalPrimeModulus p n
  let E := rationalCyclotomicArtinLocalizedField m p
  let T := RationalCyclotomicPrincipalPrimePadicLevel p n
  let eL : E ≃ₐ[ℚ_[p.1]] T :=
    rationalCyclotomicLocalizedCompletionPadicAlgEquiv p n
  let zetaE : E := rationalCyclotomicPrincipalPrimeLocalizedRoot p n
  let tau : Gal(T / ℚ_[p.1]) :=
    rationalCyclotomicPrincipalPrimePadicUnitParameterArtin p n x
  let a := rationalCyclotomicPrincipalPrimeResidueUnit p n x
  let zetaT : T := padicMultiplicativePrimitiveRoot p.1 n
  have hzetaE : IsPrimitiveRoot zetaE (p.1 ^ (n + 1)) := by
    change
      IsPrimitiveRoot
        (rationalCyclotomicLocalizedPrimitiveRoot m
          (RayClass.rationalPrime p)) (m : ℕ)
    exact
      rationalCyclotomicLocalizedPrimitiveRoot_isPrimitiveRoot
        m (RayClass.rationalPrime p)
  have hrho : IsPrimitiveRoot (eL zetaE) (p.1 ^ (n + 1)) :=
    hzetaE.map_of_injective eL.injective
  have hzetaT : IsPrimitiveRoot zetaT (p.1 ^ (n + 1)) :=
    padicMultiplicativePrimitiveRoot_isPrimitiveRoot p.1 n
  have htauZetaT : tau zetaT = zetaT ^ a.val.val :=
    padicMultiplicativePrimitiveRoot_rationalPrimeUnitParameterGaloisAction
      p n x
  exact
    map_primitiveRoot_eq_pow_of_eq_pow
      tau.toMonoidHom zetaT (eL zetaE)
      (p.1 ^ (n + 1)) a.val.val hzetaT hrho htauZetaT

private theorem rationalCyclotomicPrincipalPrime_localArtin_action
    (p : Nat.Primes) (n : ℕ) (x : ℚˣ) :
    finitePlaceLocalArtinMonoidHom
        (K := ℚ)
        (L := KummerTheory.rationalCyclotomicLevel
          (rationalCyclotomicPrincipalPrimeModulus p n))
        (RayClass.rationalPrime p)
        (rationalCyclotomicChosenFinitePlaceExtension
          (rationalCyclotomicPrincipalPrimeModulus p n)
          (RayClass.rationalPrime p))
        (IdeleGroup.finiteComponent
          (RayClass.rationalPrime p)
          (IdeleGroup.principalIdele ℚ x))
        (rationalCyclotomicPrincipalPrimeLocalizedRoot p n) =
      (rationalCyclotomicPrincipalPrimeLocalizedRoot p n) ^
        (rationalCyclotomicPrincipalPrimeResidueUnit p n x).val.val := by
  let eL := rationalCyclotomicLocalizedCompletionPadicAlgEquiv p n
  apply eL.injective
  calc
    _ = _ :=
      finitePlaceLocalArtinMonoidHom_apply_semilinear
        (K := ℚ)
        (L := KummerTheory.rationalCyclotomicLevel
          (rationalCyclotomicPrincipalPrimeModulus p n))
        (K' := ℚ_[p.1])
        (L' := RationalCyclotomicPrincipalPrimePadicLevel p n)
        (RayClass.rationalPrime p)
        (rationalCyclotomicChosenFinitePlaceExtension
          (rationalCyclotomicPrincipalPrimeModulus p n)
          (RayClass.rationalPrime p))
        (rationalFinitePlaceCompletionRingEquivPadic p)
        eL.toRingEquiv
        (rationalCyclotomicPrincipalPrime_localizedBase_commutes p n)
        (rationalFinitePlaceCompletionRingEquivPadic_semilinearValuationCompatible
          p)
        (IdeleGroup.finiteComponent
          (RayClass.rationalPrime p)
          (IdeleGroup.principalIdele ℚ x))
        (rationalCyclotomicPrincipalPrimeLocalizedRoot p n)
    _ = rationalCyclotomicPrincipalPrimePadicUnitParameterArtin p n x
          (eL (rationalCyclotomicPrincipalPrimeLocalizedRoot p n)) :=
      rationalCyclotomicPrincipalPrime_padicArtin_action_eq_unitParameter
        p n x
    _ = (eL (rationalCyclotomicPrincipalPrimeLocalizedRoot p n)) ^
          (rationalCyclotomicPrincipalPrimeResidueUnit p n x).val.val :=
      rationalCyclotomicPrincipalPrime_padicUnitParameterArtin_action p n x
    _ = eL ((rationalCyclotomicPrincipalPrimeLocalizedRoot p n) ^
          (rationalCyclotomicPrincipalPrimeResidueUnit p n x).val.val) :=
      (map_pow eL (rationalCyclotomicPrincipalPrimeLocalizedRoot p n)
        (rationalCyclotomicPrincipalPrimeResidueUnit p n x).val.val).symm

/-- The finite-place Artin symbol at the ramified prime, in its canonical
local-to-global factored form.  Keeping this specialization opaque prevents its
dependent local/global instance tower from being unfolded downstream. -/
noncomputable def rationalCyclotomicPrincipalPrimeChosenArtin
    (p : Nat.Primes) (n : ℕ) (x : ℚˣ) :
    KummerTheory.rationalCyclotomicLevel
        (rationalCyclotomicPrincipalPrimeModulus p n) ≃ₐ[ℚ]
      KummerTheory.rationalCyclotomicLevel
        (rationalCyclotomicPrincipalPrimeModulus p n) :=
  finitePlaceLocalToGlobalMonoidHom
    (K := ℚ)
    (L := KummerTheory.rationalCyclotomicLevel
      (rationalCyclotomicPrincipalPrimeModulus p n))
    (RayClass.rationalPrime p)
    (rationalCyclotomicChosenFinitePlaceExtension
      (rationalCyclotomicPrincipalPrimeModulus p n)
      (RayClass.rationalPrime p))
    (finitePlaceLocalArtinMonoidHom
      (K := ℚ)
      (L := KummerTheory.rationalCyclotomicLevel
        (rationalCyclotomicPrincipalPrimeModulus p n))
      (RayClass.rationalPrime p)
      (rationalCyclotomicChosenFinitePlaceExtension
        (rationalCyclotomicPrincipalPrimeModulus p n)
        (RayClass.rationalPrime p))
      (IdeleGroup.finiteComponent
        (RayClass.rationalPrime p)
        (IdeleGroup.principalIdele ℚ x)))

/-- At the ramified prime, the cyclotomic character of the chosen finite-place
Artin symbol is the direct reduction of the rational `p`-adic unit. -/
theorem galEquivZMod_chosenFinitePlaceArtinMonoidHom_principal_at_prime
    (p : Nat.Primes) (n : ℕ) (x : ℚˣ) :
    IsCyclotomicExtension.Rat.galEquivZMod
        (p.1 ^ (n + 1))
        (KummerTheory.rationalCyclotomicLevel
          (rationalCyclotomicPrincipalPrimeModulus p n))
        (hK :=
          KummerTheory.rationalCyclotomicLevel_isCyclotomicExtension
            (rationalCyclotomicPrincipalPrimeModulus p n))
        (rationalCyclotomicPrincipalPrimeChosenArtin p n x) =
      Units.map
        (PadicInt.toZModPow (p := p.1) (n + 1)).toMonoidHom
        (padicIntUnitOfRat p
          (rationalPrimeUnit x p : ℚ)
          (rationalPrimeUnit x p).ne_zero
          (padicValRat_rationalPrimeUnit x p)) := by
  change _ = rationalCyclotomicPrincipalPrimeResidueUnit p n x
  apply rationalCyclotomicPrincipalPrime_galEquivZMod_eq_of_action p n
  simp only [rationalCyclotomicPrincipalPrimeChosenArtin]
  apply finitePlaceLocalToGlobalMonoidHom_apply_pow_of_localized_action
    (zLocal := rationalCyclotomicPrincipalPrimeLocalizedRoot p n)
  · rfl
  · exact rationalCyclotomicPrincipalPrime_localArtin_action p n x

end RationalCyclotomicPrincipalPrime


end Reciprocity
end GlobalClassFieldTheory
