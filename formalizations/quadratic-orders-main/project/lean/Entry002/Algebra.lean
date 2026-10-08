import Mathlib.RingTheory.Localization.NormTrace
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.Data.Int.Associated
import Mathlib.Data.Nat.GCD.BigOperators

/-!
# Algebraic links for the quadratic-order moat argument

These lemmas formalize the irreducible-divisor and norm steps in Sections 8--9
of entry 002, version 3. The norm is mathlib's determinant norm. No assertion
about the supply or density of principal split primes is made here.
-/

namespace Entry002

section Divisors

variable {O : Type*} [Monoid O]

/-- A nonunit divisor of an irreducible is an associate of that irreducible.
This does not require unique factorization or primality. -/
theorem associated_of_nonunit_dvd_irreducible {a x : O}
    (hx : Irreducible x) (ha : ¬ IsUnit a) (hax : a ∣ x) : Associated x a :=
  (hx.dvd_iff.mp hax).resolve_left ha

end Divisors

section IntegerNormHom

variable {O : Type*} [Monoid O] (N : O →* ℤ)

/-- Any multiplicative integer norm sends a unit to an integer of absolute
norm one. -/
theorem natAbs_normHom_unit {u : O} (hu : IsUnit u) : (N u).natAbs = 1 := by
  obtain ⟨v, hv⟩ := hu.map N
  rw [← hv]
  obtain rfl | rfl := Int.units_eq_one_or v <;> simp

/-- Associates have equal absolute integer norm. -/
theorem natAbs_normHom_associated {x y : O} (hxy : Associated x y) :
    (N x).natAbs = (N y).natAbs :=
  Int.natAbs_eq_iff_associated.mpr (hxy.map N)

theorem nonunit_of_natAbs_normHom_ne_one {a : O} (ha : (N a).natAbs ≠ 1) :
    ¬ IsUnit a := by
  intro hu
  exact ha (natAbs_normHom_unit N hu)

theorem natAbs_normHom_eq_of_nonunit_dvd_irreducible {a x : O}
    (hx : Irreducible x) (ha : ¬ IsUnit a) (hax : a ∣ x) :
    (N x).natAbs = (N a).natAbs :=
  natAbs_normHom_associated N (associated_of_nonunit_dvd_irreducible hx ha hax)

end IntegerNormHom

section IntegralAlgebraNorm

variable {O : Type*} [CommRing O]

/-- The integer determinant norm of an order element is zero exactly at zero. -/
theorem order_norm_ne_zero_iff [IsDomain O] [Module.Free ℤ O] [Module.Finite ℤ O]
    {x : O} : Algebra.norm ℤ x ≠ 0 ↔ x ≠ 0 :=
  Algebra.norm_ne_zero_iff (R := ℤ) (S := O)

theorem natAbs_order_norm_unit {u : O} (hu : IsUnit u) :
    (Algebra.norm ℤ u).natAbs = 1 :=
  natAbs_normHom_unit (Algebra.norm ℤ) hu

theorem natAbs_order_norm_associated {x y : O} (hxy : Associated x y) :
    (Algebra.norm ℤ x).natAbs = (Algebra.norm ℤ y).natAbs :=
  natAbs_normHom_associated (Algebra.norm ℤ) hxy

/-- The actual integer norm gives the norm-value restriction on exceptional
irreducibles in the restoration argument. -/
theorem natAbs_order_norm_eq_of_nonunit_dvd_irreducible {a x : O}
    (hx : Irreducible x) (ha : ¬ IsUnit a) (hax : a ∣ x) :
    (Algebra.norm ℤ x).natAbs = (Algebra.norm ℤ a).natAbs :=
  natAbs_normHom_eq_of_nonunit_dvd_irreducible (Algebra.norm ℤ) hx ha hax

theorem order_norm_dvd_of_dvd {a x : O} (hax : a ∣ x) :
    Algebra.norm ℤ a ∣ Algebra.norm ℤ x :=
  map_dvd (Algebra.norm ℤ) hax

theorem natAbs_order_norm_dvd_of_dvd {a x : O} (hax : a ∣ x) :
    (Algebra.norm ℤ a).natAbs ∣ (Algebra.norm ℤ x).natAbs :=
  Int.natAbs_dvd_natAbs.mpr (order_norm_dvd_of_dvd hax)

/-- Distinct eligible rational primes divide the norm simultaneously. -/
theorem distinct_primes_prod_dvd (S : Finset ℕ) (n : ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p) (hdiv : ∀ p ∈ S, p ∣ n) :
    S.prod id ∣ n := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    rw [Finset.prod_insert ha]
    have hpa := hprime a (Finset.mem_insert_self a S)
    have hpS : ∀ p ∈ S, Nat.Prime p :=
      fun p hp => hprime p (Finset.mem_insert_of_mem hp)
    have hc : Nat.Coprime a (S.prod id) := Nat.coprime_prod_right_iff.mpr
      (fun p hp => (Nat.coprime_primes hpa (hpS p hp)).mpr
        (fun hap => ha (hap ▸ hp)))
    exact hc.mul_dvd_of_dvd_of_dvd (hdiv a (Finset.mem_insert_self a S))
      (ih hpS (fun p hp => hdiv p (Finset.mem_insert_of_mem hp)))

/-- The A4 arithmetic bound before the geometric quadratic norm estimate. -/
theorem distinct_primes_prod_le_order_norm [IsDomain O] [Module.Free ℤ O]
    [Module.Finite ℤ O] (S : Finset ℕ) {x : O} (hx : x ≠ 0)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hdiv : ∀ p ∈ S, p ∣ (Algebra.norm ℤ x).natAbs) :
    S.prod id ≤ (Algebra.norm ℤ x).natAbs :=
  Nat.le_of_dvd (Int.natAbs_pos.mpr (order_norm_ne_zero_iff.mpr hx))
    (distinct_primes_prod_dvd S _ hprime hdiv)

/-- Exceptional irreducibles for a selected family of principal generators. -/
def irreducibleExceptions (generators : Set O) : Set O :=
  {x | Irreducible x ∧ ∃ a ∈ generators, a ∣ x}

/-- Exceptions have one of the absolute norm values of the supplied nonunit
generators, even when a generator is itself reducible. -/
theorem exception_has_selected_norm (generators : Set O)
    (hgen : ∀ a ∈ generators, ¬ IsUnit a) {x : O}
    (hx : x ∈ irreducibleExceptions generators) :
    ∃ a ∈ generators, (Algebra.norm ℤ x).natAbs = (Algebra.norm ℤ a).natAbs := by
  obtain ⟨hxirr, a, ha, hax⟩ := hx
  exact ⟨a, ha, natAbs_order_norm_eq_of_nonunit_dvd_irreducible hxirr (hgen a ha) hax⟩

/-- This is precisely the bounded-norm inclusion used before exceptional
component restoration. -/
theorem exception_norm_bounds [IsDomain O] [Module.Free ℤ O] [Module.Finite ℤ O]
    (generators : Set O) (M : ℕ)
    (hgen : ∀ a ∈ generators, ¬ IsUnit a)
    (hbound : ∀ a ∈ generators, (Algebra.norm ℤ a).natAbs ≤ M) {x : O}
    (hx : x ∈ irreducibleExceptions generators) :
    0 < (Algebra.norm ℤ x).natAbs ∧ (Algebra.norm ℤ x).natAbs ≤ M := by
  obtain ⟨a, ha, hnorm⟩ := exception_has_selected_norm generators hgen hx
  constructor
  · exact Int.natAbs_pos.mpr (order_norm_ne_zero_iff.mpr hx.1.ne_zero)
  · rw [hnorm]
    exact hbound a ha

end IntegralAlgebraNorm

section FieldNormBridge

open scoped nonZeroDivisors

variable {O K : Type*} [CommRing O] [Field K]
  [Algebra O K] [Algebra ℚ K] [IsScalarTower ℤ O K]
  [IsLocalization (Algebra.algebraMapSubmonoid O (nonZeroDivisors ℤ)) K]
  [Module.Free ℤ O] [Module.Finite ℤ O]

/-- For an order whose rational localization is the ambient field, the
determinant norm agrees with the usual rational field norm. The localization
assumption is the standard mathlib predicate, not a norm-equality premise. -/
theorem order_norm_eq_field_norm (x : O) :
    Algebra.norm ℚ (algebraMap O K x) = (Algebra.norm ℤ x : ℚ) :=
  Algebra.norm_localization ℤ (nonZeroDivisors ℤ) x

end FieldNormBridge

section TwoEmbeddings

variable {K E : Type*} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
  [IsGalois ℚ K] [Field E] [Algebra ℚ E]

/-- Enumerating the two Galois conjugates gives the actual field norm as the
product of the two embedding coordinates. -/
theorem field_norm_eq_product_embeddings (σ : K →ₐ[ℚ] E)
    (e : Fin 2 ≃ (K ≃ₐ[ℚ] K)) (x : K) :
    algebraMap ℚ E (Algebra.norm ℚ x) = σ (e 0 x) * σ (e 1 x) := by
  calc
    algebraMap ℚ E (Algebra.norm ℚ x) =
        ∏ τ : K ≃ₐ[ℚ] K, σ (τ x) := by
      simpa only [map_prod, AlgHom.commutes] using
        congrArg σ (Algebra.norm_eq_prod_automorphisms (K := ℚ) (L := K) x)
    _ = ∏ i : Fin 2, σ (e i x) :=
      (Fintype.prod_equiv e _ _ (fun _ => rfl)).symm
    _ = σ (e 0 x) * σ (e 1 x) := by simp [Fin.prod_univ_two]

end TwoEmbeddings

end Entry002
