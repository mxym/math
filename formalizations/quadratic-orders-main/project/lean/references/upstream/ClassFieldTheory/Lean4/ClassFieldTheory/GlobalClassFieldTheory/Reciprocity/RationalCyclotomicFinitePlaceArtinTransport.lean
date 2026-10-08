/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.RationalCyclotomicFinitePlaceArtinPadic


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

/-- The chosen localized global cyclotomic level, transported over the
completion equivalence, is the standard multiplicative Lubin--Tate level. -/
noncomputable def rationalCyclotomicLocalizedCompletionPadicAlgEquiv
    (p : Nat.Primes) (n : ℕ) :
    rationalCyclotomicArtinLocalizedField
        (rationalCyclotomicPrincipalPrimeModulus p n) p ≃ₐ[ℚ_[p.1]]
      RationalCyclotomicPrincipalPrimePadicLevel p n := by
  letI : IsCyclotomicExtension {p.1 ^ (n + 1)} ℚ_[p.1]
      (rationalCyclotomicArtinLocalizedField
        (rationalCyclotomicPrincipalPrimeModulus p n) p) :=
    rationalCyclotomicPrincipalPrimeLocalizedLevel_isCyclotomicExtension p n
  letI : IsCyclotomicExtension {p.1 ^ (n + 1)} ℚ_[p.1]
      (RationalCyclotomicPrincipalPrimePadicLevel p n) :=
    padicMultiplicativeLevel_isCyclotomicExtension p.1 n
  exact
    IsCyclotomicExtension.algEquiv
      {p.1 ^ (n + 1)} ℚ_[p.1]
      (rationalCyclotomicArtinLocalizedField
        (rationalCyclotomicPrincipalPrimeModulus p n) p)
      (RationalCyclotomicPrincipalPrimePadicLevel p n)

/-! ## The ramified principal finite-place factor -/

theorem
    rationalCyclotomicPrincipalPrime_galEquivZMod_eq_of_action
    (p : Nat.Primes) (n : ℕ)
    (sigma : Gal(
      rationalCyclotomicPrincipalPrimeLevel
        (rationalCyclotomicPrincipalPrimeModulus p n) / ℚ))
    (a : (ZMod (p.1 ^ (n + 1)))ˣ)
    (haction :
      sigma (rationalCyclotomicLevelPrimitiveRoot
          (rationalCyclotomicPrincipalPrimeModulus p n)) =
        rationalCyclotomicLevelPrimitiveRoot
            (rationalCyclotomicPrincipalPrimeModulus p n) ^ a.val.val) :
    IsCyclotomicExtension.Rat.galEquivZMod
        (p.1 ^ (n + 1))
        (rationalCyclotomicPrincipalPrimeLevel
          (rationalCyclotomicPrincipalPrimeModulus p n))
        (hK :=
          KummerTheory.rationalCyclotomicLevel_isCyclotomicExtension
            (rationalCyclotomicPrincipalPrimeModulus p n)) sigma =
      a := by
  let m := rationalCyclotomicPrincipalPrimeModulus p n
  let L := rationalCyclotomicPrincipalPrimeLevel m
  let zeta : L := rationalCyclotomicLevelPrimitiveRoot m
  have hzeta : IsPrimitiveRoot zeta (p.1 ^ (n + 1)) := by
    change
      IsPrimitiveRoot
        (rationalCyclotomicLevelPrimitiveRoot m) (m : ℕ)
    exact rationalCyclotomicLevelPrimitiveRoot_isPrimitiveRoot m
  change
    IsCyclotomicExtension.Rat.galEquivZMod
        (p.1 ^ (n + 1)) L
        (hK :=
          KummerTheory.rationalCyclotomicLevel_isCyclotomicExtension m)
        sigma = a
  let c :=
    IsCyclotomicExtension.Rat.galEquivZMod
      (p.1 ^ (n + 1)) L
      (hK :=
        KummerTheory.rationalCyclotomicLevel_isCyclotomicExtension m)
      sigma
  have hc :
      sigma zeta = zeta ^ c.val.val :=
    IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq
      (hK :=
        KummerTheory.rationalCyclotomicLevel_isCyclotomicExtension m)
      (p.1 ^ (n + 1)) L sigma hzeta.pow_eq_one
  have hpowers :
      zeta ^ c.val.val = zeta ^ a.val.val :=
    hc.symm.trans haction
  rw [(hzeta.isOfFinOrder m.ne_zero).pow_inj_mod,
    ← hzeta.eq_orderOf,
    ← ZMod.natCast_eq_natCast_iff'] at hpowers
  change
      (c.val.val : ZMod (p.1 ^ (n + 1))) =
        (a.val.val : ZMod (p.1 ^ (n + 1))) at hpowers
  have hValues : c.val = a.val := by
    calc
      c.val = (c.val.val : ZMod (p.1 ^ (n + 1))) :=
        (ZMod.natCast_zmod_val c.val).symm
      _ = (a.val.val : ZMod (p.1 ^ (n + 1))) := hpowers
      _ = a.val := ZMod.natCast_zmod_val a.val
  change c = a
  apply Units.ext
  exact hValues

/-- The chosen finite-place Artin map factors through any extension identified
with the chosen one. -/
theorem chosenFinitePlaceArtinMonoidHom_apply_factor_of_extension_eq
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L)
    (hw : chosenFinitePlaceExtension (L := L) v = w)
    (x : (v.adicCompletion K)ˣ) :
    chosenFinitePlaceArtinMonoidHom
        (K := K) (L := L) v x =
      finitePlaceLocalToGlobalMonoidHom
        (K := K) (L := L) v w
        (finitePlaceLocalArtinMonoidHom
          (K := K) (L := L) v w x) := by
  subst w
  exact
    congrArg
      (fun f : (v.adicCompletion K)ˣ →* (L ≃ₐ[K] L) => f x)
      (finitePlaceArtinMonoidHomOfExtension_factor
        (K := K) (L := L) v
        (chosenFinitePlaceExtension (L := L) v))

private theorem
    chosenFinitePlaceArtinMonoidHom_apply_factor_of_extension_eq_at
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L)
    (hw : chosenFinitePlaceExtension (L := L) v = w)
    (x : (v.adicCompletion K)ˣ) (z : L) :
    chosenFinitePlaceArtinMonoidHom
        (K := K) (L := L) v x z =
      finitePlaceLocalToGlobalMonoidHom
        (K := K) (L := L) v w
        (finitePlaceLocalArtinMonoidHom
          (K := K) (L := L) v w x) z := by
  exact
    congrArg (fun sigma : Gal(L / K) => sigma z)
      (chosenFinitePlaceArtinMonoidHom_apply_factor_of_extension_eq
        (K := K) (L := L) v w hw x)

theorem finitePlaceLocalToGlobalMonoidHom_apply_pow_of_localized_action
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L)
    (sigma :
      let vK := HeightOneSpectrum.adicAbv K v
      let E := LocalizedCompletion vK w
      letI : Algebra vK.Completion E :=
        finitePlaceLocalArtinLocalizedAlgebra v w
      Gal(E / vK.Completion))
    (z : L)
    (zLocal :
      let vK := HeightOneSpectrum.adicAbv K v
      LocalizedCompletion vK w)
    (e : ℕ)
    (hLocalization :
      let vK := HeightOneSpectrum.adicAbv K v
      let E := LocalizedCompletion vK w
      letI : Algebra vK.Completion E :=
        finitePlaceLocalArtinLocalizedAlgebra v w
      let eLoc : L →+* E :=
        AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
      eLoc z = zLocal)
    (hlocal : sigma zLocal = zLocal ^ e) :
    finitePlaceLocalToGlobalMonoidHom
        (K := K) (L := L) v w sigma z = z ^ e := by
  let vK := HeightOneSpectrum.adicAbv K v
  let hvK : vK.IsNontrivial := RayClass.adicAbv_isNontrivial v
  let E := LocalizedCompletion vK w
  let : Algebra vK.Completion E :=
    finitePlaceLocalArtinLocalizedAlgebra v w
  let eD : absoluteValueDecompositionGroup K w.1 ≃* Gal(E / vK.Completion) :=
    decompositionGroupEquivAlgebraicLocalizationAut vK hvK w
  let eLoc : L →+* E :=
    AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
  let delta : absoluteValueDecompositionGroup K w.1 := eD.symm sigma
  have hDecomposition : eD delta = sigma := eD.apply_symm_apply sigma
  apply eLoc.injective
  calc
    eLoc (finitePlaceLocalToGlobalMonoidHom
        (K := K) (L := L) v w sigma z) =
        eD delta (eLoc z) :=
      (localizationRamificationGroups_decompositionGroupEquiv_toLocalization
        vK hvK w delta z).symm
    _ = sigma (eLoc z) :=
      congrArg (fun tau : Gal(E / vK.Completion) => tau (eLoc z))
        hDecomposition
    _ = sigma zLocal :=
      congrArg (fun y : E => sigma y) hLocalization
    _ = zLocal ^ e := hlocal
    _ = (eLoc z) ^ e :=
      congrArg (fun y : E => y ^ e) hLocalization.symm
    _ = eLoc (z ^ e) := (map_pow eLoc z e).symm

theorem map_primitiveRoot_eq_pow_of_eq_pow
    {M : Type} [CommRing M] [IsDomain M]
    (f : M →* M) (zeta rho : M) (order exponent : ℕ)
    [NeZero order]
    (hzeta : IsPrimitiveRoot zeta order)
    (hrho : IsPrimitiveRoot rho order)
    (hf : f zeta = zeta ^ exponent) :
    f rho = rho ^ exponent := by
  obtain ⟨j, -, hj⟩ :=
    hzeta.eq_pow_of_pow_eq_one hrho.pow_eq_one
  calc
    f rho = f (zeta ^ j) := congrArg f hj.symm
    _ = (f zeta) ^ j := map_pow f zeta j
    _ = (zeta ^ exponent) ^ j := congrArg (fun z => z ^ j) hf
    _ = zeta ^ (exponent * j) := (pow_mul zeta exponent j).symm
    _ = zeta ^ (j * exponent) :=
      congrArg (fun e : ℕ => zeta ^ e) (Nat.mul_comm exponent j)
    _ = (zeta ^ j) ^ exponent := pow_mul zeta j exponent
    _ = rho ^ exponent := congrArg (fun z => z ^ exponent) hj

theorem finitePlaceLocalArtinMonoidHom_apply_semilinear
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
    (z : LocalizedCompletion (HeightOneSpectrum.adicAbv K v) w) :
    eL (finitePlaceLocalArtinMonoidHom
        (K := K) (L := L) v w x z) =
      LocalClassFieldTheory.abelianLocalArtinMonoidHom K' L'
        (Units.map eK.toMonoidHom
          (finitePlaceLocalArtinInput v x)) (eL z) := by
  calc
    eL (finitePlaceLocalArtinMonoidHom
        (K := K) (L := L) v w x z) =
      eL ((@LocalClassFieldTheory.abelianLocalArtinMonoidHom
        (HeightOneSpectrum.adicAbv K v).Completion
        (LocalizedCompletion (HeightOneSpectrum.adicAbv K v) w)
        (inferInstance : Field
          (HeightOneSpectrum.adicAbv K v).Completion)
        (inferInstance : Field
          (LocalizedCompletion (HeightOneSpectrum.adicAbv K v) w))
        (finitePlaceLocalArtinLocalizedAlgebra v w)
        (finitePlaceLocalArtinCompletionValuativeRel v)
        (inferInstance : TopologicalSpace
          (HeightOneSpectrum.adicAbv K v).Completion)
        (finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v)
        (finitePlaceLocalArtinFiniteDimensional v w)
        (finitePlaceLocalArtinIsAbelianGalois v w hKLfinite)
        (finitePlaceLocalArtinInput v x)) z) :=
      congrArg eL
        (finitePlaceLocalArtinMonoidHom_apply_normalized_at
          (K := K) (L := L) v w x z)
    _ = LocalClassFieldTheory.abelianLocalArtinMonoidHom K' L'
          (Units.map eK.toMonoidHom
            (finitePlaceLocalArtinInput v x)) (eL z) :=
      @abelianLocalArtinMonoidHom_semilinear_action
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
        eK eL hcomm hExt (finitePlaceLocalArtinInput v x) z


end RationalCyclotomicPrincipalPrime

end Reciprocity
end GlobalClassFieldTheory
