import ArithmeticSupplyRayBridge
import Entry002.ArithmeticLocalCongruence
import Entry002.ArithmeticSupplyElementary
import Entry002.ArithmeticPrimeIdealCounting
import Entry002.ArithmeticConductorConjugation
import ClassFieldTheory.AlgebraicNumberTheory.SUnit.Rank
import ClassFieldTheory.AlgebraicNumberTheory.RayClass.Topology

set_option autoImplicit false
open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain ClassFieldTheory
namespace Entry002

noncomputable def integralRayUnit (K : Type) [Field K] [NumberField K]
    (d : 𝓞 K) (hd : d ≠ 0) : Kˣ :=
  Units.mk0 (d : K) (RingOfIntegers.coe_ne_zero_iff.mpr hd)

/-- The actual finite ideal modulus of the nonzero integral denominator d. -/
noncomputable def integralRayModulus (K : Type) [Field K] [NumberField K]
    (d : 𝓞 K) (hd : d ≠ 0) : RayClassModulus K where
  finitePart := (FractionalIdealGroup.countVector
    (toPrincipalIdeal (𝓞 K) K (integralRayUnit K d hd))).mapRange
      Int.toNat (by simp)
  infinitePart := ∅

theorem integralRayModulus_apply (K : Type) [Field K] [NumberField K]
    (d : 𝓞 K) (hd : d ≠ 0) (v : HeightOneSpectrum (𝓞 K)) :
    (integralRayModulus K d hd).finitePart v =
      (FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (d : K))).toNat := by
  simp [integralRayModulus, integralRayUnit]

theorem integralRayModulus_valuation (K : Type) [Field K] [NumberField K]
    (d : 𝓞 K) (hd : d ≠ 0) (v : HeightOneSpectrum (𝓞 K)) :
    v.valuation K (d : K) =
      WithZero.exp (-((integralRayModulus K d hd).finitePart v : ℤ)) := by
  have hv := SUnitGroup.valuation_eq_exp_neg_count (integralRayUnit K d hd) v
  change v.valuation K (d : K) = WithZero.exp
    (-FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (d : K))) at hv
  have hc : 0 ≤ FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ (d : K)) := by
    have hle := v.valuation_le_one (K := K) d
    rw [hv, ← WithZero.exp_zero, WithZero.exp_le_exp] at hle
    omega
  rw [integralRayModulus_apply, Int.toNat_of_nonneg hc]
  exact hv

/-- An actual ray higher-unit condition on an integral field unit reflects
back to the corresponding completed integer ideal. -/
theorem integralRay_local_congruence (K : Type) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) (x : Kˣ) (a : 𝓞 K)
    (ha : (a : K) = (x : K))
    (hx : finitePlaceUnitEmbedding v x ∈ rayLocalHigherUnitGroup v n) :
    algebraMap (𝓞 K) (v.adicCompletionIntegers K) (a - 1) ∈
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n := by
  change finitePlaceUnitEmbedding v x ∈ RayClass.localHigherUnitGroup v n at hx
  obtain ⟨y, hy, hmap⟩ := (RayClass.mem_localHigherUnitGroup_iff v n _).mp hx
  have hval : RayClass.localIntegralValue v y =
      algebraMap (𝓞 K) (v.adicCompletionIntegers K) a := by
    apply Subtype.ext
    have hh := congrArg Units.val hy
    change ((RayClass.localIntegralValue v y : v.adicCompletionIntegers K) :
      v.adicCompletion K) = algebraMap K (v.adicCompletion K) (x : K) at hh
    change _ = algebraMap K (v.adicCompletion K) (a : K)
    rw [ha]
    exact hh
  have hcong := (RayClass.localHigherUnitMap_eq_one_iff v n y).mp hmap
  simpa only [hval, map_sub, map_one] using hcong

/-- The actual local ray congruences for the ideal (d) imply the global
integral divisibility d ∣ a − 1. -/
theorem integralRayModulus_dvd_sub_one (K : Type) [Field K] [NumberField K]
    (d : 𝓞 K) (hd : d ≠ 0) (x : Kˣ) (a : 𝓞 K)
    (ha : (a : K) = (x : K))
    (hx : IsRayCongruent (integralRayModulus K d hd) x) : d ∣ a - 1 := by
  apply arithmeticSupply_dvd_of_local_valuation_bounds K d (a - 1) hd
  intro v
  rw [integralRayModulus_valuation K d hd v]
  by_cases hn : (integralRayModulus K d hd).finitePart v = 0
  · simpa only [hn, Nat.cast_zero, neg_zero, WithZero.exp_zero] using
      v.valuation_le_one (K := K) (a - 1)
  · have hl := hx.1 v (Finsupp.mem_support_iff.mpr hn)
    have hc := integralRay_local_congruence K v
      ((integralRayModulus K d hd).finitePart v) x a ha hl
    have hb := arithmeticSupply_completed_pow_valuation_bound K v
      ((integralRayModulus K d hd).finitePart v)
      (algebraMap (𝓞 K) (v.adicCompletionIntegers K) (a - 1)) hc
    change Valued.v (((a - 1 : 𝓞 K) : K) : v.adicCompletion K) ≤ _ at hb
    rw [v.valuedAdicCompletion_eq_valuation'] at hb
    exact hb

/-- For every positive conductor, the actual ray-congruent integral
unit has a representative in the actual conductor order. -/
theorem integralRayModulus_conductor_lift (K : Type) [Field K] [NumberField K]
    (f : ℕ) (hf : 0 < f) (x : Kˣ) (a : 𝓞 K)
    (ha : (a : K) = (x : K))
    (hx : IsRayCongruent
      (integralRayModulus K (f : 𝓞 K) (by exact_mod_cast hf.ne')) x) :
    ∃ A : conductorOrder K f, conductorOrderToIntegers K f A = a := by
  apply arithmeticSupply_congruenceOne_order_lift K f a
  exact integralRayModulus_dvd_sub_one K (f : 𝓞 K) (by exact_mod_cast hf.ne') x a ha hx

/-- Actual splitting in the conductor ray field supplies a principal
prime generator in the nonmaximal order, with its precise maximal-order ideal. -/
theorem arithmeticSupply_ray_split_conductor_generator (K : Type)
    [Field K] [NumberField K] (f : ℕ) (hf : 0 < f)
    (R : RayClassFieldRealization K
      (integralRayModulus K (f : 𝓞 K) (by exact_mod_cast hf.ne')))
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ (integralRayModulus K (f : 𝓞 K) (by exact_mod_cast hf.ne')).finitePart.support)
    (hsplit : FinitePrimeSplitsCompletely K R.extension v) :
    ∃ A : conductorOrder K f,
      Ideal.span ({conductorOrderToIntegers K f A} : Set (𝓞 K)) = v.asIdeal ∧
      (f : 𝓞 K) ∣ conductorOrderToIntegers K f A - 1 := by
  obtain ⟨x, a, ha, hspan, hx, _⟩ :=
    (arithmeticSupply_ray_split_integral_generator_iff K _ R v hv).mp hsplit
  obtain ⟨A, hA⟩ := integralRayModulus_conductor_lift K f hf x a ha hx
  refine ⟨A, ?_, ?_⟩
  · simpa only [hA] using hspan
  · rw [hA]
    exact integralRayModulus_dvd_sub_one K (f : 𝓞 K)
      (by exact_mod_cast hf.ne') x a ha hx

/-- Every conductor admits an actual finite abelian number-field ray
extension with the conductor generator consequence. This asserts no density. -/
theorem arithmeticSupply_exists_conductor_ray_extension (K : Type)
    [Field K] [NumberField K] (f : ℕ) (hf : 0 < f) :
    ∃ R : RayClassFieldRealization K
        (integralRayModulus K (f : 𝓞 K) (by exact_mod_cast hf.ne')),
      ∀ (v : HeightOneSpectrum (𝓞 K))
        (hv : v ∉ (integralRayModulus K (f : 𝓞 K) (by exact_mod_cast hf.ne')).finitePart.support),
        FinitePrimeSplitsCompletely K R.extension v →
          ∃ A : conductorOrder K f,
            Ideal.span ({conductorOrderToIntegers K f A} : Set (𝓞 K)) = v.asIdeal ∧
            (f : 𝓞 K) ∣ conductorOrderToIntegers K f A - 1 := by
  obtain ⟨R⟩ := rayClassField_reciprocity K
    (integralRayModulus K (f : 𝓞 K) (by exact_mod_cast hf.ne'))
  exact ⟨R, fun v hv hs => arithmeticSupply_ray_split_conductor_generator K f hf R v hv hs⟩

/-- At an actual degree-one prime above p, the ray generator has actual
integer determinant norm of absolute value p even in the conductor order. -/
theorem arithmeticSupply_ray_split_conductor_norm (K : Type)
    [Field K] [NumberField K] (f : ℕ) (hf : 0 < f)
    (R : RayClassFieldRealization K
      (integralRayModulus K (f : 𝓞 K) (by exact_mod_cast hf.ne')))
    (v : HeightOneSpectrum (𝓞 K)) (p : ℕ)
    [v.asIdeal.LiesOver (Ideal.span {(p : ℤ)})]
    (hdegree : v.asIdeal.inertiaDeg ℤ = 1)
    (hv : v ∉ (integralRayModulus K (f : 𝓞 K) (by exact_mod_cast hf.ne')).finitePart.support)
    (hsplit : FinitePrimeSplitsCompletely K R.extension v) :
    ∃ A : conductorOrder K f,
      Ideal.span ({conductorOrderToIntegers K f A} : Set (𝓞 K)) = v.asIdeal ∧
      (Algebra.norm ℤ A).natAbs = p ∧
      (f : 𝓞 K) ∣ conductorOrderToIntegers K f A - 1 := by
  obtain ⟨A, hA, hcong⟩ := arithmeticSupply_ray_split_conductor_generator K f hf R v hv hsplit
  refine ⟨A, hA, ?_, hcong⟩
  rw [arithmeticSupply_conductor_norm_eq_maximal_norm K f hf]
  exact arithmeticSupply_degree_one_generator_norm K p v.asIdeal hdegree
    (conductorOrderToIntegers K f A) hA

/-- Actual ray splitting, together with rational unramified degree-one
splitting, gives both conjugate conductor generators and residue maps.
The pair intersection and the distinctness of the underlying ideals are derived. -/
theorem arithmeticSupply_ray_split_conductor_residue_pair (K : Type)
    [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2)
    (f : ℕ) (hf : 0 < f) (τ : K ≃ₐ[ℚ] K) (hτ : τ ≠ AlgEquiv.refl)
    (R : RayClassFieldRealization K
      (integralRayModulus K (f : 𝓞 K) (by exact_mod_cast hf.ne')))
    (v : HeightOneSpectrum (𝓞 K)) (p : ℕ) (hp : p.Prime)
    [v.asIdeal.LiesOver (Ideal.span {(p : ℤ)})]
    (he : v.asIdeal.ramificationIdx ℤ = 1) (hd : v.asIdeal.inertiaDeg ℤ = 1)
    (hv : v ∉ (integralRayModulus K (f : 𝓞 K) (by exact_mod_cast hf.ne')).finitePart.support)
    (hsplit : FinitePrimeSplitsCompletely K R.extension v) :
    ∃ A : conductorOrder K f,
      Ideal.span ({conductorOrderToIntegers K f A} : Set (𝓞 K)) = v.asIdeal ∧
      (Algebra.norm ℤ A).natAbs = p ∧
      (Algebra.norm ℤ (arithmeticSupply_conductorAutomorphism K f τ A)).natAbs = p ∧
      ∃ ψPlus ψMinus : conductorOrder K f →+* ZMod p,
        Function.Surjective ψPlus ∧ Function.Surjective ψMinus ∧
        (∀ x, ψPlus x = 0 ↔ A ∣ x) ∧
        (∀ x, ψMinus x = 0 ↔ arithmeticSupply_conductorAutomorphism K f τ A ∣ x) ∧
        ∀ x, (ψPlus x = 0 ∧ ψMinus x = 0) ↔ ∃ y, x = (p : ℤ) • y := by
  obtain ⟨A, hspan, _⟩ := arithmeticSupply_ray_split_conductor_generator K f hf R v hv hsplit
  exact ⟨A, hspan, arithmeticSupply_split_conductor_residue_pair K f hK hf τ hτ
    p hp v.asIdeal he hd A hspan⟩

end Entry002
