/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.CompletionToIdeal
import ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.IdealToCompletion
import ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.LocalNorm
import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquiv
import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.BaseChange
import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.Core
import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.NormComparison
import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.NormalClosureNorm
import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.Tower
import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.TowerAlgEquivNaturality
import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.TowerBaseChange
import ClassFieldTheory.AlgebraicNumberTheory.Idele.Relative.FinitePlaceTensorNorm
import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.RationalCyclotomicFinitePlace
import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.RationalCyclotomicLocalization
import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.RationalPrimeFactorization
import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.RationalPrincipalLocalUnit
import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SemilinearNaturality
import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UnramifiedNormalization
import ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.PadicMultiplicativeArtinComparison
import ValuedFieldTheory.LocalField.DiscreteValuationField.PadicValuationComparison
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.UnramifiedFrobenius
import ValuedFieldTheory.LocalField.Padic.Cyclotomic.TotallyRamified.EisensteinPolynomial
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois


set_option autoImplicit false

/-!
# Finite-place Artin symbols in rational cyclotomic levels

At a rational prime away from the cyclotomic level, the chosen completed
extension is unramified.  Its normalized local Artin map is therefore the
arithmetic Frobenius raised to the local valuation.  The genuine primitive
root in the localized cyclotomic level identifies the image of arithmetic
Frobenius under the global cyclotomic character with the residue prime.
-/

open scoped Classical NNReal NumberField ValuativeRel
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

-- Specializing the generic finite-place comparison to `ℚ` must retain its
-- `Algebra.id` owner rather than selecting the competing rational-field
-- instance introduced after specialization.
@[reducible] noncomputable local instance
    rationalFinitePlaceCompletionRatAlgebra
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    Algebra ℚ (HeightOneSpectrum.adicAbv ℚ v).Completion := by
  letI : Algebra ℚ ℚ := Algebra.id ℚ
  let hWith : Algebra ℚ
      (WithAbs (HeightOneSpectrum.adicAbv ℚ v)) :=
    WithAbs.instAlgebra _
  let hUniform : UniformContinuousConstSMul ℚ
      (WithAbs (HeightOneSpectrum.adicAbv ℚ v)) :=
    WithAbs.instUniformContinuousConstSMulReal _
  exact
    @UniformSpace.Completion.algebra
      (WithAbs (HeightOneSpectrum.adicAbv ℚ v)) _ _ _ _
      ℚ _ hWith hUniform

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open LubinTate

theorem mappedAbelianLocalArtin_eq_frobenius_zpow
    {F E G : Type}
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [ValuativeRel E] [UniformSpace E] [IsUniformAddGroup E]
    [IsNonarchimedeanLocalField E]
    [Algebra F E] [FiniteDimensional F E] [IsAbelianGalois F E]
    [Valuation.HasExtension
      (ValuativeRel.valuation F) (ValuativeRel.valuation E)]
    [IsNonarchimedeanLocalField.IsUnramifiedValuedExtension F E]
    [Group G]
    (f : (E ≃ₐ[F] E) →* G) (x : Fˣ) :
    f (LocalClassFieldTheory.abelianLocalArtinMonoidHom F E x) =
      (f (arithmeticFrobeniusOfUnramifiedValuation F E)) ^
        IsNonarchimedeanLocalField.valuationMap F
          (Additive.ofMul x) := by
  rw [LocalClassFieldTheory.abelianLocalArtinMonoidHom_eq_frobenius_zpow,
    map_zpow]

local instance primeFact (q : Nat.Primes) : Fact q.1.Prime :=
  ⟨q.2⟩

local instance levelNeZero (m : ℕ+) : NeZero (m : ℕ) :=
  ⟨m.ne_zero⟩

noncomputable local instance
    rationalCyclotomicLevelFiniteDimensional
    (m : ℕ+) :
    FiniteDimensional ℚ
      (KummerTheory.rationalCyclotomicLevel m) :=
  IsCyclotomicExtension.finiteDimensional
    {(m : ℕ)} ℚ (KummerTheory.rationalCyclotomicLevel m)

noncomputable local instance
    rationalCyclotomicLevelIsAbelianGalois
    (m : ℕ+) :
    IsAbelianGalois ℚ
      (KummerTheory.rationalCyclotomicLevel m) := by
  have : IsGalois ℚ
      (KummerTheory.rationalCyclotomicLevel m) :=
    inferInstance
  let e :=
    IsCyclotomicExtension.Rat.galEquivZMod
      (m : ℕ) (KummerTheory.rationalCyclotomicLevel m)
  exact
    { is_comm.comm σ τ := by
        apply e.injective
        simp only [map_mul]
        exact mul_comm _ _ }

@[reducible]
noncomputable local instance rationalFinitePlaceBaseNontriviallyNormedField
    (q : Nat.Primes) :
    NontriviallyNormedField
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion :=
  absoluteValueExtension_completionNontriviallyNormedField
    (HeightOneSpectrum.adicAbv ℚ
      (RayClass.rationalPrime q))
    (RayClass.adicAbv_isNontrivial
      (RayClass.rationalPrime q))

noncomputable local instance rationalFinitePlaceBaseLocallyCompactSpace
    (q : Nat.Primes) :
    LocallyCompactSpace
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion :=
  AbsoluteValue.Completion.locallyCompactSpace
    (finitePlaceCompletionBaseMap_isometry
      (RayClass.rationalPrime q))

noncomputable local instance rationalFinitePlaceBaseIsUltrametricDist
    (q : Nat.Primes) :
    IsUltrametricDist
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion :=
  finitePlaceArtinCompletionIsUltrametricDist
    (HeightOneSpectrum.adicAbv ℚ
      (RayClass.rationalPrime q))
    (HeightOneSpectrum.isNonarchimedean_adicAbv
      ℚ (RayClass.rationalPrime q))

@[reducible]
noncomputable local instance rationalFinitePlaceBaseValued
    (q : Nat.Primes) :
    Valued
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion ℝ≥0 :=
  finitePlaceArtinCompletionValued
    (HeightOneSpectrum.adicAbv ℚ
      (RayClass.rationalPrime q))
    (HeightOneSpectrum.isNonarchimedean_adicAbv
      ℚ (RayClass.rationalPrime q))

@[reducible]
noncomputable local instance rationalFinitePlaceBaseValuativeRel
    (q : Nat.Primes) :
    ValuativeRel
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion :=
  finitePlaceLocalArtinCompletionValuativeRel
    (K := ℚ) (RayClass.rationalPrime q)

noncomputable local instance
    rationalFinitePlaceBaseValuationIsNontrivial
    (q : Nat.Primes) :
    (Valued.v :
      Valuation
        (HeightOneSpectrum.adicAbv ℚ
          (RayClass.rationalPrime q)).Completion
        ℝ≥0).IsNontrivial :=
  (inferInstance :
    (NormedField.valuation
      (K :=
        (HeightOneSpectrum.adicAbv ℚ
          (RayClass.rationalPrime q)).Completion)).IsNontrivial)

noncomputable local instance rationalFinitePlaceBaseValuationCompatible
    (q : Nat.Primes) :
    (Valued.v :
      Valuation
        (HeightOneSpectrum.adicAbv ℚ
          (RayClass.rationalPrime q)).Completion
        ℝ≥0).Compatible :=
  Valuation.Compatible.ofValuation _

noncomputable local instance
    rationalFinitePlaceBaseValuativeRelIsNontrivial
    (q : Nat.Primes) :
    ValuativeRel.IsNontrivial
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion :=
  (ValuativeRel.isNontrivial_iff_isNontrivial
    (Valued.v :
      Valuation
        (HeightOneSpectrum.adicAbv ℚ
          (RayClass.rationalPrime q)).Completion
        ℝ≥0)).2 inferInstance

noncomputable local instance rationalFinitePlaceBaseIsValuativeTopology
    (q : Nat.Primes) :
    IsValuativeTopology
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion :=
  isValuativeTopology_of_valued_ofValuation
    (HeightOneSpectrum.adicAbv ℚ
      (RayClass.rationalPrime q)).Completion ℝ≥0

noncomputable local instance
    rationalFinitePlaceBaseIsNonarchimedeanLocalField
    (q : Nat.Primes) :
    IsNonarchimedeanLocalField
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion :=
  finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField
    (K := ℚ) (RayClass.rationalPrime q)


/-- Rational cyclotomic levels are finite-dimensional over `ℚ`. -/
theorem rationalCyclotomicPrincipalPrimeLevelFiniteDimensional
    (m : ℕ+) :
    FiniteDimensional ℚ (KummerTheory.rationalCyclotomicLevel m) :=
  rationalCyclotomicLevelFiniteDimensional m

/-- Rational cyclotomic levels are abelian Galois extensions of `ℚ`. -/
theorem rationalCyclotomicPrincipalPrimeLevelIsAbelianGalois
    (m : ℕ+) :
    IsAbelianGalois ℚ (KummerTheory.rationalCyclotomicLevel m) :=
  rationalCyclotomicLevelIsAbelianGalois m

/-- The canonical nontrivially normed field structure on the completion of
`ℚ` at the rational prime `p`, exposed for principal-prime constructions. -/
@[reducible]
noncomputable def rationalPrimeFactorCompletionNontriviallyNormedField
    (p : Nat.Primes) :
    NontriviallyNormedField
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime p)).Completion :=
  rationalFinitePlaceBaseNontriviallyNormedField p

/-- The completion of `ℚ` at `p` is locally compact. -/
theorem rationalPrimeFactorCompletionLocallyCompactSpace
    (p : Nat.Primes) :
    LocallyCompactSpace
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime p)).Completion :=
  rationalFinitePlaceBaseLocallyCompactSpace p

/-- The completion of `ℚ` at `p` carries its canonical ultrametric distance. -/
theorem rationalPrimeFactorCompletionIsUltrametricDist
    (p : Nat.Primes) :
    IsUltrametricDist
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime p)).Completion :=
  rationalFinitePlaceBaseIsUltrametricDist p

/-- The canonical `ℝ≥0`-valued structure on the completion of `ℚ` at `p`. -/
@[reducible]
noncomputable def rationalPrimeFactorCompletionValued
    (p : Nat.Primes) :
    Valued
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime p)).Completion ℝ≥0 :=
  rationalFinitePlaceBaseValued p

/-- The valuative relation induced by the canonical valuation on the
completion of `ℚ` at `p`. -/
@[reducible]
noncomputable def rationalPrimeFactorCompletionValuativeRel
    (p : Nat.Primes) :
    ValuativeRel
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime p)).Completion :=
  rationalFinitePlaceBaseValuativeRel p

/-- The canonical valuation on the completion of `ℚ` at `p` is nontrivial. -/
theorem rationalPrimeFactorCompletionValuationIsNontrivial
    (p : Nat.Primes) :
    (Valued.v : Valuation
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime p)).Completion ℝ≥0).IsNontrivial :=
  rationalFinitePlaceBaseValuationIsNontrivial p

/-- The canonical valuation on the completion of `ℚ` at `p` is compatible
with its field structure. -/
theorem rationalPrimeFactorCompletionValuationCompatible
    (p : Nat.Primes) :
    (Valued.v : Valuation
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime p)).Completion ℝ≥0).Compatible :=
  rationalFinitePlaceBaseValuationCompatible p

/-- The canonical valuative relation on the completion at `p` is nontrivial. -/
theorem rationalPrimeFactorCompletionValuativeRelIsNontrivial
    (p : Nat.Primes) :
    ValuativeRel.IsNontrivial
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime p)).Completion :=
  rationalFinitePlaceBaseValuativeRelIsNontrivial p

/-- The completion topology at `p` is induced by its canonical valuation. -/
theorem rationalPrimeFactorCompletionIsValuativeTopology
    (p : Nat.Primes) :
    IsValuativeTopology
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime p)).Completion :=
  rationalFinitePlaceBaseIsValuativeTopology p

/-- The completion of `ℚ` at `p` is a nonarchimedean local field. -/
theorem rationalPrimeFactorCompletionIsNonarchimedeanLocalField
    (p : Nat.Primes) :
    IsNonarchimedeanLocalField
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime p)).Completion :=
  rationalFinitePlaceBaseIsNonarchimedeanLocalField p

/-- The positive conductor of the `n`-th ramified cyclotomic level at
`p`. -/
def rationalCyclotomicPrincipalPrimeModulus
    (p : Nat.Primes) (n : ℕ) : ℕ+ :=
  ⟨p.1 ^ (n + 1), pow_pos p.2.pos (n + 1)⟩

/-- The rational finite-place completion used at the prime `p`. -/
abbrev RationalCyclotomicPrincipalPrimeCompletion
    (p : Nat.Primes) :=
  (HeightOneSpectrum.adicAbv ℚ
    (RayClass.rationalPrime p)).Completion

/-- The chosen localized cyclotomic field at level `p ^ (n + 1)`. -/
abbrev RationalCyclotomicPrincipalPrimeLocalizedLevel
    (p : Nat.Primes) (n : ℕ) :=
  rationalCyclotomicLocalizedCompletion
    (rationalCyclotomicPrincipalPrimeModulus p n)
    (RayClass.rationalPrime p)

/-- The standard multiplicative Lubin--Tate field at level `n`. -/
abbrev RationalCyclotomicPrincipalPrimePadicLevel
    (p : Nat.Primes) (n : ℕ) :=
  standardLubinTateLevelField
    (padicMultiplicativeLubinTateSeries_isUniformizer p.1) n

/-- The valuation ring of the absolute-value completion at `q`, identified
with the standard p-adic integer ring `ℤ_q`. -/
noncomputable def rationalFinitePlaceCompletionIntegerRingEquivPadicInt
    (q : Nat.Primes) :
    𝒪[(HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion] ≃+*
      ℤ_[q.1] := by
  let v : HeightOneSpectrum (𝓞 ℚ) :=
    RayClass.rationalPrime q
  let vQ := HeightOneSpectrum.adicAbv ℚ v
  let eConcreteIntegers :
      𝒪[vQ.Completion] ≃+*
        v.adicCompletionIntegers ℚ :=
    finitePlaceCompletionIntegerRingEquiv v
  exact
    eConcreteIntegers.trans
      (PadicInt.adicCompletionIntegersEquiv
        (𝓞 ℚ) q).symm.toRingEquiv

/-- The absolute-value completion at the rational prime `q`, identified
with the standard field `ℚ_q`. -/
noncomputable def rationalFinitePlaceCompletionRingEquivPadic
    (q : Nat.Primes) :
    (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion ≃+*
      ℚ_[q.1] :=
  IsFractionRing.ringEquivOfRingEquiv
    (rationalFinitePlaceCompletionIntegerRingEquivPadicInt q)

/-- The completion-to-`ℚ_q` equivalence respects the rational embedding. -/
theorem rationalFinitePlaceCompletionRingEquivPadic_algebraMap
    (q : Nat.Primes) (a : ℚ) :
    rationalFinitePlaceCompletionRingEquivPadic q
        (algebraMap ℚ
          (HeightOneSpectrum.adicAbv ℚ
            (RayClass.rationalPrime q)).Completion a) =
      algebraMap ℚ ℚ_[q.1] a := by
  exact
    (rationalFinitePlaceCompletionRingEquivPadic q).toRingHom.map_rat_algebraMap a

/-- The completion field equivalence and its restriction to valuation
rings commute with the natural inclusions into the fields. -/
theorem rationalFinitePlaceCompletionIntegerRingEquivPadicInt_coe
    (q : Nat.Primes)
    (a :
      𝒪[(HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion]) :
    rationalFinitePlaceCompletionRingEquivPadic q
        (algebraMap
          𝒪[(HeightOneSpectrum.adicAbv ℚ
            (RayClass.rationalPrime q)).Completion]
          (HeightOneSpectrum.adicAbv ℚ
            (RayClass.rationalPrime q)).Completion a) =
      algebraMap ℤ_[q.1] ℚ_[q.1]
        (rationalFinitePlaceCompletionIntegerRingEquivPadicInt q a) := by
  exact
    (IsFractionRing.ringEquivOfRingEquiv_algebraMap
      (rationalFinitePlaceCompletionIntegerRingEquivPadicInt q) a)

/-- The canonical rational-completion equivalence preserves the canonical
valuations. -/
theorem
    rationalFinitePlaceCompletionRingEquivPadic_semilinearValuationCompatible
    (p : Nat.Primes) :
    SemilinearValuationCompatible
      (RationalCyclotomicPrincipalPrimeCompletion p) ℚ_[p.1]
      (rationalFinitePlaceCompletionRingEquivPadic p) := by
  let F := RationalCyclotomicPrincipalPrimeCompletion p
  let eK := rationalFinitePlaceCompletionRingEquivPadic p
  let : Algebra F ℚ_[p.1] := eK.toRingHom.toAlgebra
  change
    (ValuativeRel.valuation F).HasExtension
      (ValuativeRel.valuation ℚ_[p.1])
  let eO :=
    (rationalFinitePlaceCompletionIntegerRingEquivPadicInt p).trans
      (padicIntEquivValuationSubring p.1)
  have hChosen :
      (localCompleteDVF F).valuation.HasExtension
        (padicDVRValuation p.1) := by
    change
      (localCompleteDVF F).valuation.HasExtension
        (padicCompleteDVF p.1).valuation
    apply
      ValuationTheory.DiscreteValuationField.ValuedExtension.valuation_hasExtension_of_valuationSubring_equiv
        (localCompleteDVF F)
        (padicCompleteDVF p.1)
        eO
    intro z
    change
      algebraMap
          (padicDVRValuation p.1).valuationSubring ℚ_[p.1]
          (padicIntEquivValuationSubring p.1
            (rationalFinitePlaceCompletionIntegerRingEquivPadicInt
              p z)) =
        rationalFinitePlaceCompletionRingEquivPadic p
          (algebraMap 𝒪[F] F z)
    symm
    calc
      rationalFinitePlaceCompletionRingEquivPadic p
          (algebraMap 𝒪[F] F z) =
        algebraMap ℤ_[p.1] ℚ_[p.1]
          (rationalFinitePlaceCompletionIntegerRingEquivPadicInt
            p z) :=
        rationalFinitePlaceCompletionIntegerRingEquivPadicInt_coe
          p z
      _ =
        algebraMap
          (padicDVRValuation p.1).valuationSubring ℚ_[p.1]
          (padicIntEquivValuationSubring p.1
            (rationalFinitePlaceCompletionIntegerRingEquivPadicInt
              p z)) := by
        rw [PadicInt.algebraMap_apply,
          ValuationSubring.algebraMap_apply]
        exact
          (padicIntEquivValuationSubring_coe p.1
            (rationalFinitePlaceCompletionIntegerRingEquivPadicInt
              p z)).symm
  have hBase :
      (ValuativeRel.valuation F).HasExtension
        (padicDVRValuation p.1) := by
    rw [← localCompleteDVF_valuation_eq]
    exact hChosen
  refine
    { val_isEquiv_comap := ?_ }
  exact
    hBase.val_isEquiv_comap.trans
      ((padicDVRValuation_isEquiv_valuativeRelValuation
        p.1).comap (algebraMap F ℚ_[p.1]))

/-- The rational prime, pulled back from `ℤ_q` to the valuation ring of
the absolute-value completion at `q`. -/
noncomputable def rationalPrimeFinitePlaceInteger
    (q : Nat.Primes) :
    𝒪[(HeightOneSpectrum.adicAbv ℚ
      (RayClass.rationalPrime q)).Completion] :=
  (rationalFinitePlaceCompletionIntegerRingEquivPadicInt q).symm
    (q.1 : ℤ_[q.1])

/-- The pulled-back rational prime is irreducible in the completion
valuation ring. -/
theorem rationalPrimeFinitePlaceInteger_irreducible
    (q : Nat.Primes) :
    Irreducible (rationalPrimeFinitePlaceInteger q) := by
  exact
    (MulEquiv.irreducible_iff
      (rationalFinitePlaceCompletionIntegerRingEquivPadicInt
        q).symm.toMulEquiv).2
      ((PadicInt.prime_p :
        Prime (q.1 : ℤ_[q.1])).irreducible)

/-- Coercing the pulled-back prime to the completion field gives the
ordinary image of the rational number `q`. -/
theorem rationalPrimeFinitePlaceInteger_coe
    (q : Nat.Primes) :
    ((rationalPrimeFinitePlaceInteger q :
      𝒪[(HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion]) :
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion) =
      algebraMap ℚ
        (HeightOneSpectrum.adicAbv ℚ
          (RayClass.rationalPrime q)).Completion
        (q.1 : ℚ) := by
  apply
    (rationalFinitePlaceCompletionRingEquivPadic q).injective
  change
    rationalFinitePlaceCompletionRingEquivPadic q
        (algebraMap
          𝒪[(HeightOneSpectrum.adicAbv ℚ
            (RayClass.rationalPrime q)).Completion]
          (HeightOneSpectrum.adicAbv ℚ
            (RayClass.rationalPrime q)).Completion
          (rationalPrimeFinitePlaceInteger q)) =
      rationalFinitePlaceCompletionRingEquivPadic q
        (algebraMap ℚ
          (HeightOneSpectrum.adicAbv ℚ
            (RayClass.rationalPrime q)).Completion
          (q.1 : ℚ))
  calc
    rationalFinitePlaceCompletionRingEquivPadic q
        (algebraMap
          𝒪[(HeightOneSpectrum.adicAbv ℚ
            (RayClass.rationalPrime q)).Completion]
          (HeightOneSpectrum.adicAbv ℚ
            (RayClass.rationalPrime q)).Completion
          (rationalPrimeFinitePlaceInteger q)) =
      algebraMap ℤ_[q.1] ℚ_[q.1]
        ((rationalFinitePlaceCompletionIntegerRingEquivPadicInt q)
          (rationalPrimeFinitePlaceInteger q)) :=
        rationalFinitePlaceCompletionIntegerRingEquivPadicInt_coe
          q (rationalPrimeFinitePlaceInteger q)
    _ = (q.1 : ℚ_[q.1]) := by
      rw [rationalPrimeFinitePlaceInteger,
        (rationalFinitePlaceCompletionIntegerRingEquivPadicInt
          q).apply_symm_apply,
        PadicInt.algebraMap_apply,
        PadicInt.coe_natCast]
    _ =
      rationalFinitePlaceCompletionRingEquivPadic q
        (algebraMap ℚ
          (HeightOneSpectrum.adicAbv ℚ
            (RayClass.rationalPrime q)).Completion
          (q.1 : ℚ)) := by
      rw [
        rationalFinitePlaceCompletionRingEquivPadic_algebraMap]
      norm_num

/-- The rational prime as a field unit of its absolute-value completion. -/
noncomputable def rationalPrimeFinitePlaceFieldUnit
    (q : Nat.Primes) :
    (HeightOneSpectrum.adicAbv ℚ
      (RayClass.rationalPrime q)).Completionˣ :=
  Units.mk0
    (rationalPrimeFinitePlaceInteger q :
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion)
    (by
      intro hzero
      exact
        (rationalPrimeFinitePlaceInteger_irreducible q).ne_zero
          (Subtype.ext hzero))

/-- In the inverse-standard local reciprocity normalization, the rational
prime itself has normalized additive value `-1`. -/
theorem rationalPrimeFinitePlaceFieldUnit_valuationMap
    (q : Nat.Primes) :
    IsNonarchimedeanLocalField.valuationMap
        (HeightOneSpectrum.adicAbv ℚ
          (RayClass.rationalPrime q)).Completion
        (Additive.ofMul
          (rationalPrimeFinitePlaceFieldUnit q)) =
      -1 := by
  simpa [IsNonarchimedeanLocalField.valuationMap_apply] using
    (LocalFieldTheory.v_integerRingIrreducibleFieldUnit
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion
      (rationalPrimeFinitePlaceInteger q)
      (rationalPrimeFinitePlaceInteger_irreducible q)
      (rationalPrimeFinitePlaceFieldUnit q) rfl)

/-- The rational `q`-unit part of `x`, pulled back from `ℤ_qˣ` to the
valuation ring of the absolute-value completion. -/
noncomputable def rationalPrimeUnitFinitePlaceIntegerUnit
    (x : ℚˣ) (q : Nat.Primes) :
    𝒪[(HeightOneSpectrum.adicAbv ℚ
      (RayClass.rationalPrime q)).Completion]ˣ :=
  Units.map
      (rationalFinitePlaceCompletionIntegerRingEquivPadicInt
        q).symm.toMonoidHom
    (padicIntUnitOfRat q
      (rationalPrimeUnit x q : ℚ)
      (rationalPrimeUnit x q).ne_zero
      (padicValRat_rationalPrimeUnit x q))

/-- Forgetting the integrality proof from the pulled-back `q`-unit gives
the ordinary image of the rational `q`-unit in the completion field. -/
theorem rationalPrimeUnitFinitePlaceIntegerUnit_coe
    (x : ℚˣ) (q : Nat.Primes) :
    (((rationalPrimeUnitFinitePlaceIntegerUnit x q :
        𝒪[(HeightOneSpectrum.adicAbv ℚ
          (RayClass.rationalPrime q)).Completion]ˣ) :
        𝒪[(HeightOneSpectrum.adicAbv ℚ
          (RayClass.rationalPrime q)).Completion]) :
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion) =
      algebraMap ℚ
        (HeightOneSpectrum.adicAbv ℚ
          (RayClass.rationalPrime q)).Completion
        (rationalPrimeUnit x q : ℚ) := by
  apply
    (rationalFinitePlaceCompletionRingEquivPadic q).injective
  change
    rationalFinitePlaceCompletionRingEquivPadic q
        (algebraMap
          𝒪[(HeightOneSpectrum.adicAbv ℚ
            (RayClass.rationalPrime q)).Completion]
          (HeightOneSpectrum.adicAbv ℚ
            (RayClass.rationalPrime q)).Completion
          (rationalPrimeUnitFinitePlaceIntegerUnit x q :
            𝒪[(HeightOneSpectrum.adicAbv ℚ
              (RayClass.rationalPrime q)).Completion])) =
      rationalFinitePlaceCompletionRingEquivPadic q
        (algebraMap ℚ
          (HeightOneSpectrum.adicAbv ℚ
            (RayClass.rationalPrime q)).Completion
          (rationalPrimeUnit x q : ℚ))
  calc
    rationalFinitePlaceCompletionRingEquivPadic q
        (algebraMap
          𝒪[(HeightOneSpectrum.adicAbv ℚ
            (RayClass.rationalPrime q)).Completion]
          (HeightOneSpectrum.adicAbv ℚ
            (RayClass.rationalPrime q)).Completion
          (rationalPrimeUnitFinitePlaceIntegerUnit x q :
          𝒪[(HeightOneSpectrum.adicAbv ℚ
            (RayClass.rationalPrime q)).Completion])) =
      algebraMap ℤ_[q.1] ℚ_[q.1]
        ((rationalFinitePlaceCompletionIntegerRingEquivPadicInt q)
          (rationalPrimeUnitFinitePlaceIntegerUnit x q :
            𝒪[(HeightOneSpectrum.adicAbv ℚ
              (RayClass.rationalPrime q)).Completion])) :=
        rationalFinitePlaceCompletionIntegerRingEquivPadicInt_coe q
          (rationalPrimeUnitFinitePlaceIntegerUnit x q :
            𝒪[(HeightOneSpectrum.adicAbv ℚ
              (RayClass.rationalPrime q)).Completion])
    _ =
      ((padicIntUnitOfRat q
        (rationalPrimeUnit x q : ℚ)
        (rationalPrimeUnit x q).ne_zero
        (padicValRat_rationalPrimeUnit x q) :
          ℤ_[q.1]) : ℚ_[q.1]) := by
      rw [rationalPrimeUnitFinitePlaceIntegerUnit]
      simp [PadicInt.algebraMap_apply]
    _ = ((rationalPrimeUnit x q : ℚ) : ℚ_[q.1]) := by
      rw [padicIntUnitOfRat_coe]
    _ =
      rationalFinitePlaceCompletionRingEquivPadic q
        (algebraMap ℚ
          (HeightOneSpectrum.adicAbv ℚ
            (RayClass.rationalPrime q)).Completion
          (rationalPrimeUnit x q : ℚ)) := by
      rw [
        rationalFinitePlaceCompletionRingEquivPadic_algebraMap]
      simp

/-- The completion field unit underlying the pulled-back rational `q`-unit
has normalized additive value zero. -/
theorem rationalPrimeUnitFinitePlaceField_valuationMap
    (x : ℚˣ) (q : Nat.Primes) :
    IsNonarchimedeanLocalField.valuationMap
        (HeightOneSpectrum.adicAbv ℚ
          (RayClass.rationalPrime q)).Completion
        (Additive.ofMul
          (IsNonarchimedeanLocalField.integerUnitsToFieldUnits
            (HeightOneSpectrum.adicAbv ℚ
              (RayClass.rationalPrime q)).Completion
            (rationalPrimeUnitFinitePlaceIntegerUnit x q))) =
      0 := by
  rw [IsNonarchimedeanLocalField.valuationMap_apply]
  exact
    IsNonarchimedeanLocalField.v_integerUnitsToFieldUnits
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion
      (rationalPrimeUnitFinitePlaceIntegerUnit x q)

/-- The rational prime `q`, regarded as a unit of `ℚ`. -/
def rationalPrimeGeneratorUnit (q : Nat.Primes) : ℚˣ :=
  Units.mk0 (q.1 : ℚ) (by exact_mod_cast q.2.ne_zero)

/-- The underlying rational number of the prime generator unit is `q`. -/
@[simp]
theorem rationalPrimeGeneratorUnit_coe (q : Nat.Primes) :
    (rationalPrimeGeneratorUnit q : ℚ) = q.1 :=
  rfl

/-- Reattaching the removed `q`-power to the rational `q`-unit recovers
the original rational field unit. -/
theorem rationalPrimeGeneratorUnit_zpow_mul_rationalPrimeUnit
    (x : ℚˣ) (q : Nat.Primes) :
    rationalPrimeGeneratorUnit q ^
          padicValRat q.1 (x : ℚ) *
        rationalPrimeUnit x q =
      x := by
  rw [rationalPrimeGeneratorUnit, rationalPrimeUnit,
    ← mul_assoc, ← zpow_add]
  simp

/-- The source unit in the absolute-value completion represented by the
finite component of a rational principal idele. -/
noncomputable def rationalPrincipalFinitePlaceInput
    (x : ℚˣ) (q : Nat.Primes) :
    (HeightOneSpectrum.adicAbv ℚ
      (RayClass.rationalPrime q)).Completionˣ :=
  (finitePlaceCompletionUnitsContinuousMulEquiv
      (RayClass.rationalPrime q)).symm
    (IdeleGroup.finiteComponent
      (RayClass.rationalPrime q)
      (IdeleGroup.principalIdele ℚ x))

/-- The source unit represented by a principal finite component is the
ordinary image of the rational field unit in the absolute-value
completion. -/
theorem rationalPrincipalFinitePlaceInput_eq_algebraMap
    (x : ℚˣ) (q : Nat.Primes) :
    rationalPrincipalFinitePlaceInput x q =
      Units.map
        (algebraMap ℚ
          (HeightOneSpectrum.adicAbv ℚ
            (RayClass.rationalPrime q)).Completion).toMonoidHom
        x := by
  apply Units.ext
  let v : HeightOneSpectrum (𝓞 ℚ) :=
    RayClass.rationalPrime q
  let vQ := HeightOneSpectrum.adicAbv ℚ v
  let component : (v.adicCompletion ℚ)ˣ :=
    IdeleGroup.finiteComponent v
      (IdeleGroup.principalIdele ℚ x)
  apply (finitePlaceCompletionRingEquiv v).injective
  change
    finitePlaceCompletionRingEquiv v
        (rationalPrincipalFinitePlaceInput x q : vQ.Completion) =
      finitePlaceCompletionRingEquiv v
        (algebraMap ℚ vQ.Completion (x : ℚ))
  have hCompletion :
      finitePlaceCompletionRingEquiv v
          (rationalPrincipalFinitePlaceInput x q :
            vQ.Completion) =
        (component : v.adicCompletion ℚ) := by
    have hUnits :=
      congrArg Units.val
        ((finitePlaceCompletionUnitsContinuousMulEquiv v).apply_symm_apply
          component)
    exact hUnits
  have hComponent :
      (component : v.adicCompletion ℚ) =
        algebraMap ℚ (v.adicCompletion ℚ) (x : ℚ) := by
    apply (Padic.adicCompletionEquiv (𝓞 ℚ) q).symm.injective
    calc
      (Padic.adicCompletionEquiv (𝓞 ℚ) q).symm
          (component : v.adicCompletion ℚ) =
        algebraMap ℚ ℚ_[q.1] (x : ℚ) := by
          dsimp only [component]
          rw [IdeleGroup.finiteComponent_principalIdele]
          exact
            (Padic.adicCompletionEquiv
              (𝓞 ℚ) q).symm.commutes (x : ℚ)
      _ = (Padic.adicCompletionEquiv (𝓞 ℚ) q).symm
          (algebraMap ℚ (v.adicCompletion ℚ) (x : ℚ)) := by
        symm
        exact
          (Padic.adicCompletionEquiv
            (𝓞 ℚ) q).symm.commutes (x : ℚ)
  calc
    finitePlaceCompletionRingEquiv v
        (rationalPrincipalFinitePlaceInput x q :
          vQ.Completion) =
      (component : v.adicCompletion ℚ) := hCompletion
    _ = algebraMap ℚ (v.adicCompletion ℚ) (x : ℚ) := hComponent
    _ = finitePlaceCompletionRingEquiv v
        (algebraMap ℚ vQ.Completion (x : ℚ)) := by
      symm
      exact
        (finitePlaceCompletionAlgEquiv (K := ℚ) v).commutes (x : ℚ)

/-- The normalized local exponent of a rational principal finite
component is the negative of the usual `q`-adic exponent.  The minus sign
records the inverse-standard local reciprocity convention in which a
prime element has normalized value `-1`. -/
theorem rationalPrincipalFiniteComponent_valuationMap
    (x : ℚˣ) (q : Nat.Primes) :
    IsNonarchimedeanLocalField.valuationMap
        (HeightOneSpectrum.adicAbv ℚ
          (RayClass.rationalPrime q)).Completion
        (Additive.ofMul
          ((finitePlaceCompletionUnitsContinuousMulEquiv
            (RayClass.rationalPrime q)).symm
            (IdeleGroup.finiteComponent
              (RayClass.rationalPrime q)
              (IdeleGroup.principalIdele ℚ x)))) =
      -padicValRat q.1 (x : ℚ) := by
  let F :=
    (HeightOneSpectrum.adicAbv ℚ
      (RayClass.rationalPrime q)).Completion
  let embed : ℚˣ →* Fˣ :=
    Units.map (algebraMap ℚ F).toMonoidHom
  let primeUnit : Fˣ :=
    rationalPrimeFinitePlaceFieldUnit q
  let integralUnit : 𝒪[F]ˣ :=
    rationalPrimeUnitFinitePlaceIntegerUnit x q
  let unitPart : Fˣ :=
    IsNonarchimedeanLocalField.integerUnitsToFieldUnits
      F integralUnit
  have hInput :
      rationalPrincipalFinitePlaceInput x q =
        embed x := by
    exact rationalPrincipalFinitePlaceInput_eq_algebraMap x q
  have hPrime :
      embed (rationalPrimeGeneratorUnit q) =
        primeUnit := by
    apply Units.ext
    exact
      (rationalPrimeFinitePlaceInteger_coe q).symm
  have hUnit :
      embed (rationalPrimeUnit x q) =
        unitPart := by
    apply Units.ext
    exact
      (rationalPrimeUnitFinitePlaceIntegerUnit_coe
        x q).symm
  change
    IsNonarchimedeanLocalField.valuationMap F
        (Additive.ofMul
          (rationalPrincipalFinitePlaceInput x q)) =
      -padicValRat q.1 (x : ℚ)
  rw [hInput]
  conv_lhs =>
    rw [← rationalPrimeGeneratorUnit_zpow_mul_rationalPrimeUnit
      x q]
  rw [map_mul, map_zpow, hPrime, hUnit,
    IsNonarchimedeanLocalField.valuationMap_ofMul_mul,
    IsNonarchimedeanLocalField.valuationMap_ofMul_zpow,
    rationalPrimeFinitePlaceFieldUnit_valuationMap,
    rationalPrimeUnitFinitePlaceField_valuationMap]
  ring

/-- The principal finite component of the rational prime itself has
normalized local exponent `-1`. -/
theorem rationalPrimePrincipalFiniteComponent_valuationMap
    (q : Nat.Primes) :
    IsNonarchimedeanLocalField.valuationMap
        (HeightOneSpectrum.adicAbv ℚ
          (RayClass.rationalPrime q)).Completion
        (Additive.ofMul
          ((finitePlaceCompletionUnitsContinuousMulEquiv
            (RayClass.rationalPrime q)).symm
            (IdeleGroup.finiteComponent
              (RayClass.rationalPrime q)
              (IdeleGroup.principalIdele ℚ
                (rationalPrimeGeneratorUnit q))))) =
      -1 := by
  rw [rationalPrincipalFiniteComponent_valuationMap,
    rationalPrimeGeneratorUnit_coe,
    padicValRat.self q.2.one_lt]

/-- A cyclotomic automorphism which raises the selected primitive root to
the `q`-th power has cyclotomic character equal to the residue-prime unit. -/
theorem rationalCyclotomicLevel_galEquivZMod_eq_unitOfCoprime
    (m : ℕ+) (q : Nat.Primes)
    (hq : ¬ q.1 ∣ (m : ℕ))
    (σ : KummerTheory.rationalCyclotomicLevel m ≃ₐ[ℚ]
      KummerTheory.rationalCyclotomicLevel m)
    (hσ :
      σ (rationalCyclotomicLevelPrimitiveRoot m) =
        rationalCyclotomicLevelPrimitiveRoot m ^ q.1) :
    IsCyclotomicExtension.Rat.galEquivZMod
        (m : ℕ) (KummerTheory.rationalCyclotomicLevel m) σ =
      ZMod.unitOfCoprime q.1
        (q.2.coprime_iff_not_dvd.mpr hq) := by
  let ζ := rationalCyclotomicLevelPrimitiveRoot m
  have hζ : IsPrimitiveRoot ζ (m : ℕ) :=
    rationalCyclotomicLevelPrimitiveRoot_isPrimitiveRoot m
  have hCharacterRoot :
      σ ζ =
        ζ ^
          (IsCyclotomicExtension.Rat.galEquivZMod
            (m : ℕ) (KummerTheory.rationalCyclotomicLevel m) σ).val.val :=
    IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq
      (m : ℕ) (KummerTheory.rationalCyclotomicLevel m) σ
      hζ.pow_eq_one
  have hPowers :
      ζ ^
          (IsCyclotomicExtension.Rat.galEquivZMod
            (m : ℕ) (KummerTheory.rationalCyclotomicLevel m) σ).val.val =
        ζ ^ q.1 :=
    hCharacterRoot.symm.trans hσ
  rw [(hζ.isOfFinOrder m.ne_zero).pow_inj_mod,
    ← hζ.eq_orderOf,
    ← ZMod.natCast_eq_natCast_iff',
    ZMod.natCast_val] at hPowers
  apply Units.ext
  simpa using hPowers


end Reciprocity
end GlobalClassFieldTheory
