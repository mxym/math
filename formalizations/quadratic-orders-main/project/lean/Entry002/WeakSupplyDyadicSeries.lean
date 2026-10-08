import Entry002.WeakSupplyDyadicChebyshev
import Mathlib.Data.Nat.Log
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! A genuine dyadic upper decomposition of the supplied-prime Dirichlet series. -/

namespace Entry002

open scoped BigOperators Classical

theorem supply_dyadicPrimeBatch_card_le_all (P : Set ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (j : ℕ) :
    ((dyadicPrimeBatch P j).card : ℝ) ≤ 8 * (2 : ℝ) ^ j / ((j : ℝ) + 1) := by
  by_cases hj : 1 ≤ j
  · exact supply_dyadicPrimeBatch_card_le P hP hj
  · have hj0 : j = 0 := by omega
    subst j
    have hc : (dyadicPrimeBatch P 0).card ≤ 3 := by
      unfold dyadicPrimeBatch
      exact (Finset.card_filter_le _ _).trans (by norm_num)
    norm_num
    exact_mod_cast hc.trans (by norm_num : 3 ≤ 8)

theorem supply_dyadicPrimeBatch_ratio_le (P : Set ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (j : ℕ) :
    ((dyadicPrimeBatch P j).card : ℝ) / (2 : ℝ) ^ j ≤ 8 / ((j : ℝ) + 1) := by
  calc
    _ ≤ (8 * (2 : ℝ) ^ j / ((j : ℝ) + 1)) / (2 : ℝ) ^ j :=
      div_le_div_of_nonneg_right (supply_dyadicPrimeBatch_card_le_all P hP j) (by positivity)
    _ = _ := by field_simp

theorem supply_dyadic_discount_nonneg {ε : ℝ} : 0 ≤ (2 : ℝ) ^ (-ε) := by positivity

theorem supply_dyadic_discount_lt_one {ε : ℝ} (hε : 0 < ε) :
    (2 : ℝ) ^ (-ε) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)

theorem supply_dyadicPrimeBatch_ratio_discount_summable (P : Set ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) {ε : ℝ} (hε : 0 < ε) :
    Summable (fun j : ℕ =>
      ((dyadicPrimeBatch P j).card / (2 : ℝ) ^ j) * ((2 : ℝ) ^ (-ε)) ^ j) := by
  have hg := (summable_geometric_of_lt_one
    (supply_dyadic_discount_nonneg (ε := ε)) (supply_dyadic_discount_lt_one hε)).mul_left 8
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ hg
  intro j
  have hratio := supply_dyadicPrimeBatch_ratio_le P hP j
  have hrat8 : 8 / ((j : ℝ) + 1) ≤ 8 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (j : ℝ) + 1)).mpr
    nlinarith [show (0 : ℝ) ≤ (j : ℝ) by positivity]
  exact mul_le_mul_of_nonneg_right (hratio.trans hrat8) (by positivity)

theorem supply_prime_mem_log_dyadic (P : Set ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) {p : ℕ} (hp : p ∈ P) :
    p ∈ dyadicPrimeBatch P (Nat.log 2 p) := by
  apply (mem_dyadicPrimeBatch P _ p).mpr
  refine ⟨hp, ?_, ?_⟩
  · exact_mod_cast Nat.pow_log_le_self 2 (hP p hp).ne_zero
  · exact_mod_cast (Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) p).le

theorem supplyPrimeDirichletSeries_le_dyadic (P : Set ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) {ε : ℝ} (hε : 0 < ε) :
    supplyPrimeDirichletSeries P (1 + ε) ≤
      ∑' j : ℕ, ((dyadicPrimeBatch P j).card / (2 : ℝ) ^ j) *
        ((2 : ℝ) ^ (-ε)) ^ j := by
  have hs := supply_dyadicPrimeBatch_ratio_discount_summable P hP hε
  unfold supplyPrimeDirichletSeries
  apply Real.tsum_le_of_sum_le
  · intro p
    apply div_nonneg
    · unfold supplyPrimeCoefficient
      split_ifs <;> norm_num
    · positivity
  · intro S
    let T := S.filter (fun p => p ∈ P)
    let B := T.image (Nat.log 2)
    calc
      (∑ p ∈ S, supplyPrimeCoefficient P p / (p : ℝ) ^ (1 + ε)) =
          ∑ p ∈ T, 1 / (p : ℝ) ^ (1 + ε) := by
        simp [T, Finset.sum_filter, supplyPrimeCoefficient, ite_div]
      _ = ∑ j ∈ B, ∑ p ∈ T with Nat.log 2 p = j, 1 / (p : ℝ) ^ (1 + ε) := by
        exact (Finset.sum_fiberwise_of_maps_to
          (fun p hp => Finset.mem_image_of_mem (Nat.log 2) hp) _).symm
      _ ≤ ∑ j ∈ B, ∑ p ∈ dyadicPrimeBatch P j, 1 / (p : ℝ) ^ (1 + ε) := by
        apply Finset.sum_le_sum
        intro j _
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          obtain ⟨hpT, hlog⟩ := Finset.mem_filter.mp hp
          rw [← hlog]
          exact supply_prime_mem_log_dyadic P hP (Finset.mem_filter.mp hpT).2
        · intro p _ _
          positivity
      _ ≤ ∑ j ∈ B, ((dyadicPrimeBatch P j).card / (2 : ℝ) ^ j) *
          ((2 : ℝ) ^ (-ε)) ^ j :=
        Finset.sum_le_sum (fun j _ => supply_dyadicPrimeBatch_dirichlet_le P j hε.le)
      _ ≤ _ := hs.sum_le_tsum B (fun _ _ => by positivity)

end Entry002
