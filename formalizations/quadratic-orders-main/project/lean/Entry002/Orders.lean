import Entry002.Targets
import Entry002.Algebra
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dimension.Localization

/-! Algebraic infrastructure for the literal orders `ℤ + f 𝓞_K`. -/

namespace Entry002

open Module

variable (K : Type*) [Field K] [NumberField K] (f : ℕ)

theorem conductorOrder_isIntegral (x : conductorOrder K f) : IsIntegral ℤ (x : K) := by
  obtain ⟨n, y, hx⟩ := x.property
  rw [hx]
  have hn : IsIntegral ℤ (n : K) := isIntegral_algebraMap
  have hf : IsIntegral ℤ (f : K) := by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := K) (x := (f : ℤ)))
  exact hn.add (hf.mul y.isIntegral_coe)

/-- The actual conductor order injects into the maximal order. -/
def conductorOrderToIntegers : conductorOrder K f →+* NumberField.RingOfIntegers K where
  toFun x := ⟨(x : K), conductorOrder_isIntegral K f x⟩
  map_zero' := Subtype.ext rfl
  map_one' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

theorem conductorOrderToIntegers_injective :
    Function.Injective (conductorOrderToIntegers K f) := by
  intro x y h
  exact Subtype.ext (congrArg (fun z : NumberField.RingOfIntegers K => (z : K)) h)

instance conductorOrder_finite : Module.Finite ℤ (conductorOrder K f) :=
  Module.Finite.of_injective (conductorOrderToIntegers K f).toAddMonoidHom.toIntLinearMap
    (conductorOrderToIntegers_injective K f)

instance conductorOrder_free : Module.Free ℤ (conductorOrder K f) :=
  Module.free_of_finite_type_torsion_free'

/-- Multiplication by the conductor embeds the maximal order into the order
whenever the conductor is positive. -/
def integersMulConductor : NumberField.RingOfIntegers K →+ conductorOrder K f where
  toFun y := ⟨(f : K) * (y : K), 0, y, by simp⟩
  map_zero' := Subtype.ext (by simp)
  map_add' y z := Subtype.ext (by simp [mul_add])

theorem integersMulConductor_injective (hf : 0 < f) :
    Function.Injective (integersMulConductor K f) := by
  intro y z h
  apply NumberField.RingOfIntegers.coe_injective
  have hmul : (f : K) * (y : K) = (f : K) * (z : K) :=
    congrArg (fun x : conductorOrder K f => (x : K)) h
  exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hf)) hmul

/-- All positive conductor orders have the full degree of the number field. -/
theorem conductorOrder_finrank (hf : 0 < f) :
    Module.finrank ℤ (conductorOrder K f) = Module.finrank ℚ K := by
  rw [← NumberField.RingOfIntegers.rank]
  apply Nat.le_antisymm
  · exact LinearMap.finrank_le_finrank_of_injective
      (f := (conductorOrderToIntegers K f).toAddMonoidHom.toIntLinearMap)
      (conductorOrderToIntegers_injective K f)
  · exact LinearMap.finrank_le_finrank_of_injective
      (f := (integersMulConductor K f).toIntLinearMap)
      (integersMulConductor_injective K f hf)

/-- Every actual positive conductor order in a quadratic field has an integral
two-element basis, rather than merely a conditional basis parameter. -/
noncomputable def conductorOrderBasis (hK : Module.finrank ℚ K = 2) (hf : 0 < f) :
    Basis (Fin 2) ℤ (conductorOrder K f) :=
  Module.finBasisOfFinrankEq ℤ (conductorOrder K f)
    ((conductorOrder_finrank K f hf).trans hK)

open scoped nonZeroDivisors

/-- Inverting the nonzero integers in any positive conductor order gives the
ambient number field. Numerators and denominators in the maximal order are
both multiplied by the conductor. -/
theorem conductorOrder_localization (hf : 0 < f) :
    IsLocalization (Algebra.algebraMapSubmonoid (conductorOrder K f)
      (nonZeroDivisors ℤ)) K := by
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨a, n, hn, rfl⟩
    apply isUnit_iff_ne_zero.mpr
    simpa using (Int.cast_ne_zero.mpr (mem_nonZeroDivisors_iff_ne_zero.mp hn) :
      (n : K) ≠ 0)
  · intro x
    obtain ⟨⟨y, s⟩, hxy⟩ := IsLocalization.surj
      (Algebra.algebraMapSubmonoid (NumberField.RingOfIntegers K)
        (nonZeroDivisors ℤ)) x
    rcases s with ⟨s, n, hn, rfl⟩
    have hn0 : n ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hn
    have hfn0 : (f : ℤ) * n ≠ 0 :=
      mul_ne_zero (Int.natCast_ne_zero.mpr (Nat.ne_of_gt hf)) hn0
    let d : Algebra.algebraMapSubmonoid (conductorOrder K f) (nonZeroDivisors ℤ) :=
      ⟨algebraMap ℤ (conductorOrder K f) ((f : ℤ) * n),
        (f : ℤ) * n, mem_nonZeroDivisors_iff_ne_zero.mpr hfn0, rfl⟩
    refine ⟨⟨integersMulConductor K f y, d⟩, ?_⟩
    have hxy' : x * (n : K) = (y : K) := by simpa using hxy
    change x * (((f : ℤ) * n : ℤ) : K) = (f : K) * (y : K)
    rw [Int.cast_mul, Int.cast_natCast, ← hxy']
    ring
  · intro x y hxy
    refine ⟨1, ?_⟩
    have h : x = y := Subtype.ext hxy
    simp [h]

theorem conductorOrder_norm_eq_field_norm (hf : 0 < f) (x : conductorOrder K f) :
    Algebra.norm ℚ (x : K) = (Algebra.norm ℤ x : ℚ) := by
  have := conductorOrder_localization K f hf
  exact order_norm_eq_field_norm x

/-- Enumerate the two genuine Galois conjugates of a quadratic number field. -/
noncomputable def quadraticConjugates (hK : Module.finrank ℚ K = 2) :
    Fin 2 ≃ (K ≃ₐ[ℚ] K) := by
  letI : Algebra.IsQuadraticExtension ℚ K := ⟨hK⟩
  exact (Fintype.equivFinOfCardEq (by
    rw [← Nat.card_eq_fintype_card]
    exact (IsGalois.card_aut_eq_finrank ℚ K).trans hK)).symm

/-- The product of the actual real conjugate coordinates is the actual
integer norm of the conductor-order element. -/
theorem conductorOrder_real_embedding_product (hK : Module.finrank ℚ K = 2)
    (hf : 0 < f) (σ : K →ₐ[ℚ] ℝ) (e : Fin 2 ≃ (K ≃ₐ[ℚ] K))
    (x : conductorOrder K f) :
    σ (e 0 (x : K)) * σ (e 1 (x : K)) = (Algebra.norm ℤ x : ℝ) := by
  have : Algebra.IsQuadraticExtension ℚ K := ⟨hK⟩
  rw [← field_norm_eq_product_embeddings σ e,
    conductorOrder_norm_eq_field_norm K f hf x]
  simp

/-- This supplies the nonzero integral-difference hypothesis required by the
real Minkowski bounded-norm isolation theorem for every conductor order. -/
theorem conductorOrder_real_difference_integral (hK : Module.finrank ℚ K = 2)
    (hf : 0 < f) (σ : K →ₐ[ℚ] ℝ) (e : Fin 2 ≃ (K ≃ₐ[ℚ] K))
    (x y : conductorOrder K f) (hxy : x ≠ y) :
    ∃ n : ℤ,
      (σ (e 0 (y : K)) - σ (e 0 (x : K))) *
        (σ (e 1 (y : K)) - σ (e 1 (x : K))) = (n : ℝ) ∧ n ≠ 0 := by
  refine ⟨Algebra.norm ℤ (y - x), ?_, ?_⟩
  · have h := conductorOrder_real_embedding_product K f hK hf σ e (y - x)
    change σ (e 0 ((y : K) - (x : K))) *
      σ (e 1 ((y : K) - (x : K))) = _ at h
    simpa only [map_sub] using h
  · exact order_norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy.symm)

section NormEstimates

variable {O : Type*} [CommRing O] [IsDomain O]
  [Module.Free ℤ O] [Module.Finite ℤ O]

/-- The A3 collision estimate follows from norm divisibility and a quadratic
geometric upper bound. The upper bound is displayed as an input. -/
theorem norm_collision_lower_bound {x : O} (hx : x ≠ 0) {p : ℕ}
    (hp : p ∣ (Algebra.norm ℤ x).natAbs) {C r : ℝ} (hC : 0 < C) (hr : 0 ≤ r)
    (hbound : ((Algebra.norm ℤ x).natAbs : ℝ) ≤ C * r ^ 2) :
    Real.sqrt (p : ℝ) / Real.sqrt C ≤ r := by
  have hpN : p ≤ (Algebra.norm ℤ x).natAbs :=
    Nat.le_of_dvd (Int.natAbs_pos.mpr (order_norm_ne_zero_iff.mpr hx)) hp
  have hpR : (p : ℝ) ≤ C * r ^ 2 :=
    (by exact_mod_cast hpN : (p : ℝ) ≤ ((Algebra.norm ℤ x).natAbs : ℝ)).trans hbound
  have hs := Real.sqrt_le_sqrt hpR
  rw [Real.sqrt_mul hC.le, Real.sqrt_sq_eq_abs, abs_of_nonneg hr] at hs
  exact (div_le_iff₀ (Real.sqrt_pos.mpr hC)).mpr (by simpa [mul_comm] using hs)

/-- The arithmetic part of A4 is valid for all finite selections of distinct
eligible primes. The geometric quadratic norm estimate remains explicit. -/
theorem norm_prime_product_bound (S : Finset ℕ) {x : O} (hx : x ≠ 0)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hdiv : ∀ p ∈ S, p ∣ (Algebra.norm ℤ x).natAbs) {C r : ℝ}
    (hbound : ((Algebra.norm ℤ x).natAbs : ℝ) ≤ C * r ^ 2) :
    S.prod (fun p => (p : ℝ)) ≤ C * r ^ 2 := by
  have hN := distinct_primes_prod_le_order_norm S hx hprime hdiv
  have hR : ((S.prod id : ℕ) : ℝ) ≤ ((Algebra.norm ℤ x).natAbs : ℝ) := by
    exact_mod_cast hN
  simpa using hR.trans hbound

end NormEstimates

end Entry002
