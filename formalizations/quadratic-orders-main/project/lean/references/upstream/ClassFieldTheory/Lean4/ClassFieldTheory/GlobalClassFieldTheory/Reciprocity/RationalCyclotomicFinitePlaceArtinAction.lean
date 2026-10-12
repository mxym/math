/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.RationalCyclotomicFinitePlaceArtinTransport


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

/-- If a semilinearly identified target local Artin value is trivial, then the
corresponding global finite-place Artin value is trivial.  This generic bridge
keeps concrete completion and localization instance towers out of downstream
proof terms. -/
theorem finitePlaceArtinMonoidHomOfExtension_eq_one_of_semilinear
    {K L K' L' : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [hKLfinite : FiniteDimensional K L] [IsAbelianGalois K L]
    [Field K'] [ValuativeRel K'] [TopologicalSpace K']
    [IsNonarchimedeanLocalField K']
    [Field L'] [Algebra K' L']
    [FiniteDimensional K' L'] [IsAbelianGalois K' L']
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L)
    (eK : (HeightOneSpectrum.adicAbv K v).Completion ≃+* K')
    (eL : LocalizedCompletion
      (HeightOneSpectrum.adicAbv K v) w ≃+* L')
    (hcomm : ∀ y : (HeightOneSpectrum.adicAbv K v).Completion,
      eL (@algebraMap
        (HeightOneSpectrum.adicAbv K v).Completion
        (LocalizedCompletion (HeightOneSpectrum.adicAbv K v) w)
        _ _ (finitePlaceLocalArtinLocalizedAlgebra v w) y) =
        algebraMap K' L' (eK y))
    (hExt : SemilinearValuationCompatible
      (HeightOneSpectrum.adicAbv K v).Completion K' eK)
    (x : (v.adicCompletion K)ˣ)
    (htrivial :
      LocalClassFieldTheory.abelianLocalArtinMonoidHom K' L'
          (Units.map eK.toMonoidHom
            (finitePlaceLocalArtinInput v x)) = 1) :
    finitePlaceArtinMonoidHomOfExtension
        (K := K) (L := L) v w x = 1 := by
  rw [finitePlaceArtinMonoidHomOfExtension_factor,
    MonoidHom.comp_apply]
  have hlocal :
      finitePlaceLocalArtinMonoidHom
          (K := K) (L := L) v w x = 1 := by
    rw [finitePlaceLocalArtinMonoidHom_apply_normalized]
    exact
      @abelianLocalArtinMonoidHom_eq_one_of_semilinear
        (HeightOneSpectrum.adicAbv K v).Completion K'
        (LocalizedCompletion (HeightOneSpectrum.adicAbv K v) w) L'
        (inferInstance : Field
          (HeightOneSpectrum.adicAbv K v).Completion)
        (finitePlaceLocalArtinCompletionValuativeRel v)
        (inferInstance : TopologicalSpace
          (HeightOneSpectrum.adicAbv K v).Completion)
        (finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v)
        (inferInstance : Field K')
        (inferInstance : ValuativeRel K')
        (inferInstance : TopologicalSpace K')
        (inferInstance : IsNonarchimedeanLocalField K')
        (inferInstance : Field
          (LocalizedCompletion (HeightOneSpectrum.adicAbv K v) w))
        (inferInstance : Field L')
        (finitePlaceLocalArtinLocalizedAlgebra v w)
        (inferInstance : Algebra K' L')
        (finitePlaceLocalArtinFiniteDimensional v w)
        (finitePlaceLocalArtinIsAbelianGalois v w hKLfinite)
        (inferInstance : FiniteDimensional K' L')
        (inferInstance : IsAbelianGalois K' L')
        eK eL hcomm hExt (finitePlaceLocalArtinInput v x) htrivial
  rw [hlocal, map_one]

/-- The chosen primitive cyclotomic root in the localized prime-power extension. -/
noncomputable def rationalCyclotomicPrincipalPrimeLocalizedRoot
    (p : Nat.Primes) (n : ℕ) :
    rationalCyclotomicArtinLocalizedField
      (rationalCyclotomicPrincipalPrimeModulus p n) p :=
  rationalCyclotomicLocalizedPrimitiveRoot
    (rationalCyclotomicPrincipalPrimeModulus p n)
    (RayClass.rationalPrime p)

/-- The residue modulo `p^(n+1)` of the `p`-adic unit part of a rational unit. -/
noncomputable def rationalCyclotomicPrincipalPrimeResidueUnit
    (p : Nat.Primes) (n : ℕ) (x : ℚˣ) :
    (ZMod (p.1 ^ (n + 1)))ˣ :=
  Units.map
    (PadicInt.toZModPow (p := p.1) (n + 1)).toMonoidHom
    (padicIntUnitOfRat p
      (rationalPrimeUnit x p : ℚ)
      (rationalPrimeUnit x p).ne_zero
      (padicValRat_rationalPrimeUnit x p))

theorem rationalCyclotomicPrincipalPrime_localizedBase_commutes
    (p : Nat.Primes) (n : ℕ)
    (y : (rationalCyclotomicArtinBaseAbv p).Completion) :
    rationalCyclotomicLocalizedCompletionPadicAlgEquiv p n
        (algebraMap (rationalCyclotomicArtinBaseAbv p).Completion
          (rationalCyclotomicArtinLocalizedField
            (rationalCyclotomicPrincipalPrimeModulus p n) p) y) =
      algebraMap ℚ_[p.1]
        (RationalCyclotomicPrincipalPrimePadicLevel p n)
        (rationalFinitePlaceCompletionRingEquivPadic p y) := by
  let m := rationalCyclotomicPrincipalPrimeModulus p n
  let E := rationalCyclotomicArtinLocalizedField m p
  let eL := rationalCyclotomicLocalizedCompletionPadicAlgEquiv p n
  have hy :
      algebraMap (rationalCyclotomicArtinBaseAbv p).Completion E y =
        algebraMap ℚ_[p.1] E
          (rationalFinitePlaceCompletionRingEquivPadic p y) := by
    change
      algebraMap (rationalCyclotomicArtinBaseAbv p).Completion E y =
        algebraMap (rationalCyclotomicArtinBaseAbv p).Completion E
          ((rationalFinitePlaceCompletionRingEquivPadic p).symm
            (rationalFinitePlaceCompletionRingEquivPadic p y))
    exact
      (congrArg
        (algebraMap (rationalCyclotomicArtinBaseAbv p).Completion E)
        ((rationalFinitePlaceCompletionRingEquivPadic p).symm_apply_apply y)).symm
  calc
    eL (algebraMap (rationalCyclotomicArtinBaseAbv p).Completion E y) =
        eL (algebraMap ℚ_[p.1] E
          (rationalFinitePlaceCompletionRingEquivPadic p y)) :=
      congrArg eL hy
    _ = algebraMap ℚ_[p.1]
        (RationalCyclotomicPrincipalPrimePadicLevel p n)
        (rationalFinitePlaceCompletionRingEquivPadic p y) :=
      eL.commutes (rationalFinitePlaceCompletionRingEquivPadic p y)

/-- Specialized ramified-prime bridge from the standard `p`-adic Artin value
to the canonical global finite-place Artin value.  The localized completion
and all of its dependent instances remain private to this provider. -/
theorem
    rationalCyclotomicPrincipalPrime_finitePlaceArtinOfExtension_eq_one_of_padic
    (p : Nat.Primes) (n : ℕ)
    (x : ((RayClass.rationalPrime p).adicCompletion ℚ)ˣ)
    (htrivial :
      abelianLocalArtinMonoidHom ℚ_[p.1]
          (RationalCyclotomicPrincipalPrimePadicLevel p n)
          (Units.map
            (rationalFinitePlaceCompletionRingEquivPadic p).toMonoidHom
            (finitePlaceLocalArtinInput (RayClass.rationalPrime p) x)) = 1) :
    finitePlaceArtinMonoidHomOfExtension
        (K := ℚ)
        (L := KummerTheory.rationalCyclotomicLevel
          (rationalCyclotomicPrincipalPrimeModulus p n))
        (RayClass.rationalPrime p)
        (rationalCyclotomicChosenFinitePlaceExtension
          (rationalCyclotomicPrincipalPrimeModulus p n)
          (RayClass.rationalPrime p)) x = 1 := by
  exact
    finitePlaceArtinMonoidHomOfExtension_eq_one_of_semilinear
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
      (rationalCyclotomicLocalizedCompletionPadicAlgEquiv p n).toRingEquiv
      (rationalCyclotomicPrincipalPrime_localizedBase_commutes p n)
      (rationalFinitePlaceCompletionRingEquivPadic_semilinearValuationCompatible p)
      x htrivial

theorem
    padicMultiplicativePrimitiveRoot_rationalPrimeUnitParameterGaloisAction
    (p : Nat.Primes) (n : ℕ) (x : ℚˣ) :
    standardLubinTateUnitParameterEquivGal
        (padicLocalField p.1)
        (padicMultiplicativeLubinTateSeries_isUniformizer p.1) n
        (standardLubinTateUnitParameterClass
          (padicLocalField p.1) n
          (rationalPrimeUnitValuationSubringUnit x p))
        (padicMultiplicativePrimitiveRoot p.1 n) =
      padicMultiplicativePrimitiveRoot p.1 n ^
        (PadicInt.toZModPow (p := p.1) (n + 1)
          (padicIntUnitOfRat p
            (rationalPrimeUnit x p : ℚ)
            (rationalPrimeUnit x p).ne_zero
            (padicValRat_rationalPrimeUnit x p) : ℤ_[p.1])).val := by
  let uZ : ℤ_[p.1]ˣ :=
    padicIntUnitOfRat p
      (rationalPrimeUnit x p : ℚ)
      (rationalPrimeUnit x p).ne_zero
      (padicValRat_rationalPrimeUnit x p)
  let u : (padicLocalField p.1).valuationSubringˣ :=
    Units.map (padicIntEquivValuationSubring p.1).toMonoidHom uZ
  have huRational :
      rationalPrimeUnitValuationSubringUnit x p = u := by
    rfl
  have huPreimage :
      (padicIntEquivValuationSubring p.1).symm
          ((u : (padicLocalField p.1).valuationSubringˣ) :
            (padicLocalField p.1).valuationSubring) =
        (uZ : ℤ_[p.1]) := by
    change
      (padicIntEquivValuationSubring p.1).symm
          (padicIntEquivValuationSubring p.1 (uZ : ℤ_[p.1])) =
        (uZ : ℤ_[p.1])
    exact
      (padicIntEquivValuationSubring p.1).symm_apply_apply
        (uZ : ℤ_[p.1])
  have hAction :=
    padicMultiplicativePrimitiveRoot_unitParameterGaloisAction
      p.1 n u
  rw [huPreimage] at hAction
  rw [huRational]
  exact hAction

private noncomputable def rationalCyclotomicPrincipalPrimePadicTargetArtin
    (p : Nat.Primes) (n : ℕ) (x : ℚˣ) :
    Gal(RationalCyclotomicPrincipalPrimePadicLevel p n / ℚ_[p.1]) :=
  @LocalClassFieldTheory.abelianLocalArtinMonoidHom
    ℚ_[p.1] (RationalCyclotomicPrincipalPrimePadicLevel p n)
    (inferInstance : Field ℚ_[p.1])
    (inferInstance : Field
      (RationalCyclotomicPrincipalPrimePadicLevel p n))
    (inferInstance : Algebra ℚ_[p.1]
      (RationalCyclotomicPrincipalPrimePadicLevel p n))
    (inferInstance : ValuativeRel ℚ_[p.1])
    (inferInstance : TopologicalSpace ℚ_[p.1])
    (inferInstance : IsNonarchimedeanLocalField ℚ_[p.1])
    (rationalCyclotomicPrincipalPrimePadicLevelFiniteDimensional p n)
    (standardLubinTateLevelField_isAbelianGalois
      (padicLocalField p.1)
      (padicMultiplicativeLubinTateSeries_isUniformizer p.1) n)
    (Units.map
      (rationalFinitePlaceCompletionRingEquivPadic p).toMonoidHom
      (rationalPrincipalFinitePlaceInput x p))

/-- The cyclotomic Galois automorphism corresponding to the unit parameter of `x`
under the standard Lubin–Tate equivalence. -/
noncomputable def
    rationalCyclotomicPrincipalPrimePadicUnitParameterArtin
    (p : Nat.Primes) (n : ℕ) (x : ℚˣ) :
    Gal(RationalCyclotomicPrincipalPrimePadicLevel p n / ℚ_[p.1]) :=
  standardLubinTateUnitParameterEquivGal
    (padicLocalField p.1)
    (padicMultiplicativeLubinTateSeries_isUniformizer p.1) n
    (standardLubinTateUnitParameterClass
      (padicLocalField p.1) n
      (rationalPrimeUnitValuationSubringUnit x p))

private theorem
    rationalCyclotomicPrincipalPrime_padicTargetArtin_eq_unitParameter
    (p : Nat.Primes) (n : ℕ) (x : ℚˣ) :
    rationalCyclotomicPrincipalPrimePadicTargetArtin p n x =
      rationalCyclotomicPrincipalPrimePadicUnitParameterArtin p n x := by
  let T := RationalCyclotomicPrincipalPrimePadicLevel p n
  let eK := rationalFinitePlaceCompletionRingEquivPadic p
  let : FiniteDimensional ℚ_[p.1] T :=
    rationalCyclotomicPrincipalPrimePadicLevelFiniteDimensional p n
  let hpi := padicMultiplicativeLubinTateSeries_isUniformizer p.1
  let : IsAbelianGalois ℚ_[p.1] T :=
    standardLubinTateLevelField_isAbelianGalois
      (padicLocalField p.1) hpi n
  have hsource :
      Units.map eK.toMonoidHom (rationalPrincipalFinitePlaceInput x p) =
        Units.map (algebraMap ℚ ℚ_[p.1]).toMonoidHom x := by
    rw [rationalPrincipalFinitePlaceInput_eq_algebraMap]
    apply Units.ext
    exact rationalFinitePlaceCompletionRingEquivPadic_algebraMap p (x : ℚ)
  change
    LocalClassFieldTheory.abelianLocalArtinMonoidHom ℚ_[p.1] T
        (Units.map eK.toMonoidHom
          (rationalPrincipalFinitePlaceInput x p)) =
      standardLubinTateUnitParameterEquivGal
        (padicLocalField p.1) hpi n
        (standardLubinTateUnitParameterClass
          (padicLocalField p.1) n
          (rationalPrimeUnitValuationSubringUnit x p))
  rw [hsource]
  rw [
    padicMultiplicativeAbelianLocalArtin_eq_uniformizerUnitPart,
    rationalPadicFieldUnit_uniformizerUnitPart,
    padicMultiplicativeAbelianLocalArtin_eq_unitParameter]

theorem
    rationalCyclotomicPrincipalPrime_padicArtin_action_eq_unitParameter
    (p : Nat.Primes) (n : ℕ) (x : ℚˣ) :
    (@LocalClassFieldTheory.abelianLocalArtinMonoidHom
      ℚ_[p.1] (RationalCyclotomicPrincipalPrimePadicLevel p n)
      (inferInstance : Field ℚ_[p.1])
      (inferInstance : Field
        (RationalCyclotomicPrincipalPrimePadicLevel p n))
      (inferInstance : Algebra ℚ_[p.1]
        (RationalCyclotomicPrincipalPrimePadicLevel p n))
      (inferInstance : ValuativeRel ℚ_[p.1])
      (inferInstance : TopologicalSpace ℚ_[p.1])
      (inferInstance : IsNonarchimedeanLocalField ℚ_[p.1])
      (rationalCyclotomicPrincipalPrimePadicLevelFiniteDimensional p n)
      (standardLubinTateLevelField_isAbelianGalois
        (padicLocalField p.1)
        (padicMultiplicativeLubinTateSeries_isUniformizer p.1) n)
      (Units.map
        (rationalFinitePlaceCompletionRingEquivPadic p).toMonoidHom
        (finitePlaceLocalArtinInput
          (K := ℚ) (RayClass.rationalPrime p)
          (IdeleGroup.finiteComponent
            (RayClass.rationalPrime p)
            (IdeleGroup.principalIdele ℚ x)))))
        ((rationalCyclotomicLocalizedCompletionPadicAlgEquiv p n).toRingEquiv
          (rationalCyclotomicPrincipalPrimeLocalizedRoot p n)) =
      rationalCyclotomicPrincipalPrimePadicUnitParameterArtin p n x
        (rationalCyclotomicLocalizedCompletionPadicAlgEquiv p n
          (rationalCyclotomicPrincipalPrimeLocalizedRoot p n)) := by
  let eK := rationalFinitePlaceCompletionRingEquivPadic p
  have hInput :
      finitePlaceLocalArtinInput
          (K := ℚ) (RayClass.rationalPrime p)
          (IdeleGroup.finiteComponent
            (RayClass.rationalPrime p)
            (IdeleGroup.principalIdele ℚ x)) =
        rationalPrincipalFinitePlaceInput x p := by
    rfl
  have hMapped :
      Units.map eK.toMonoidHom
          (finitePlaceLocalArtinInput
            (K := ℚ) (RayClass.rationalPrime p)
            (IdeleGroup.finiteComponent
              (RayClass.rationalPrime p)
              (IdeleGroup.principalIdele ℚ x))) =
        Units.map eK.toMonoidHom
          (rationalPrincipalFinitePlaceInput x p) :=
    congrArg (Units.map eK.toMonoidHom) hInput
  calc
    _ = rationalCyclotomicPrincipalPrimePadicTargetArtin p n x
          (rationalCyclotomicLocalizedCompletionPadicAlgEquiv p n
            (rationalCyclotomicPrincipalPrimeLocalizedRoot p n)) := by
      exact congrArg
        (fun uQp =>
          (@LocalClassFieldTheory.abelianLocalArtinMonoidHom
            ℚ_[p.1] (RationalCyclotomicPrincipalPrimePadicLevel p n)
            (inferInstance : Field ℚ_[p.1])
            (inferInstance : Field
              (RationalCyclotomicPrincipalPrimePadicLevel p n))
            (inferInstance : Algebra ℚ_[p.1]
              (RationalCyclotomicPrincipalPrimePadicLevel p n))
            (inferInstance : ValuativeRel ℚ_[p.1])
            (inferInstance : TopologicalSpace ℚ_[p.1])
            (inferInstance : IsNonarchimedeanLocalField ℚ_[p.1])
            (rationalCyclotomicPrincipalPrimePadicLevelFiniteDimensional p n)
            (standardLubinTateLevelField_isAbelianGalois
              (padicLocalField p.1)
              (padicMultiplicativeLubinTateSeries_isUniformizer p.1) n)
            uQp)
              (rationalCyclotomicLocalizedCompletionPadicAlgEquiv p n
                (rationalCyclotomicPrincipalPrimeLocalizedRoot p n)))
        hMapped
    _ = rationalCyclotomicPrincipalPrimePadicUnitParameterArtin p n x
          (rationalCyclotomicLocalizedCompletionPadicAlgEquiv p n
            (rationalCyclotomicPrincipalPrimeLocalizedRoot p n)) :=
      congrArg
        (fun tau => tau
          (rationalCyclotomicLocalizedCompletionPadicAlgEquiv p n
            (rationalCyclotomicPrincipalPrimeLocalizedRoot p n)))
        (rationalCyclotomicPrincipalPrime_padicTargetArtin_eq_unitParameter
          p n x)


end RationalCyclotomicPrincipalPrime

end Reciprocity
end GlobalClassFieldTheory
