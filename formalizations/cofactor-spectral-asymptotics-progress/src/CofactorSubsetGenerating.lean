import CofactorSubsetWeight
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-! Finite weighted subset generating sums and their exponential upper bound. -/
set_option autoImplicit false
open scoped BigOperators
namespace CofactorSpectral
noncomputable section
variable {K : Type*} [DecidableEq K]

def subsetWeightedMoment (s : Finset K) (w ρ : K → ℝ) : ℝ :=
  ∑ t ∈ s.powerset, (∑ i ∈ t, w i)*(∏ i ∈ t, ρ i)

theorem subsetWeightedMoment_insert (s : Finset K) (a : K) (ha : a ∉ s)
    (w ρ : K → ℝ) :
    subsetWeightedMoment (insert a s) w ρ =
      (1+ρ a)*subsetWeightedMoment s w ρ +
        w a*ρ a*(∏ i ∈ s, (1+ρ i)) := by
  unfold subsetWeightedMoment
  rw [Finset.sum_powerset_insert ha]
  have he : (∑ t ∈ s.powerset, (∑ i ∈ insert a t, w i)*(∏ i ∈ insert a t, ρ i)) =
      ρ a*(∑ t ∈ s.powerset, (∑ i ∈ t, w i)*(∏ i ∈ t, ρ i)) +
        w a*ρ a*(∑ t ∈ s.powerset, ∏ i ∈ t, ρ i) := by
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    have hat : a ∉ t := fun h => ha ((Finset.mem_powerset.mp ht) h)
    rw [Finset.sum_insert hat,Finset.prod_insert hat]
    ring
  rw [he,← Finset.prod_one_add]
  ring

theorem subsetWeightedMoment_product_bound (s : Finset K) (w ρ : K → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hρ : ∀ i, 0 ≤ ρ i) :
    subsetWeightedMoment s w ρ ≤ (∏ i ∈ s, (1+ρ i))*(∑ i ∈ s, w i*ρ i) := by
  induction s using Finset.induction_on with
  | empty => simp [subsetWeightedMoment]
  | @insert a s ha ih =>
    rw [subsetWeightedMoment_insert s a ha,Finset.prod_insert ha,Finset.sum_insert ha]
    have hp : 0 ≤ ∏ i ∈ s, (1+ρ i) := Finset.prod_nonneg (fun i _ => by linarith [hρ i])
    have he : 0 ≤ ρ a*((∏ i ∈ s, (1+ρ i))*(w a*ρ a)) :=
      mul_nonneg (hρ a) (mul_nonneg hp (mul_nonneg (hw a) (hρ a)))
    calc
      _ ≤ (1+ρ a)*((∏ i ∈ s, (1+ρ i))*(∑ i ∈ s, w i*ρ i)) +
          w a*ρ a*(∏ i ∈ s, (1+ρ i)) :=
        add_le_add (mul_le_mul_of_nonneg_left ih (by linarith [hρ a])) le_rfl
      _ ≤ _ := by nlinarith only [he]

theorem subsetWeightedMoment_exponential_bound (s : Finset K) (w ρ : K → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hρ : ∀ i, 0 ≤ ρ i) :
    subsetWeightedMoment s w ρ ≤ Real.exp (∑ i ∈ s, ρ i)*(∑ i ∈ s, w i*ρ i) := by
  have hp : (∏ i ∈ s, (1+ρ i)) ≤ Real.exp (∑ i ∈ s, ρ i) := by
    calc
      _ ≤ ∏ i ∈ s, Real.exp (ρ i) := by
        apply Finset.prod_le_prod₀ (fun i _ => by linarith [hρ i])
        intro i _
        simpa only [add_comm] using Real.add_one_le_exp (ρ i)
      _ = _ := by rw [Real.exp_sum]
  exact (subsetWeightedMoment_product_bound s w ρ hw hρ).trans
    (mul_le_mul_of_nonneg_right hp (Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (hρ i))))

theorem geometric_subset_weighted_sum_bound [Fintype K] (d : K → ℕ) (q : ℝ) (hq : 0 ≤ q) :
    (∑ s : Finset K, (∑ i ∈ s, d i : ℕ)*q^(∑ i ∈ s, d i)) ≤
      Real.exp (∑ i, q^(d i))*(∑ i, (d i : ℝ)*q^(d i)) := by
  have h := subsetWeightedMoment_exponential_bound Finset.univ (fun i => (d i : ℝ))
    (fun i => q^(d i)) (fun _ => Nat.cast_nonneg _) (fun _ => pow_nonneg hq _)
  have he : subsetWeightedMoment Finset.univ (fun i => (d i : ℝ)) (fun i => q^(d i)) =
      ∑ s : Finset K, (∑ i ∈ s, d i : ℕ)*q^(∑ i ∈ s, d i) := by
    unfold subsetWeightedMoment
    simp only [Finset.powerset_univ]
    apply Finset.sum_congr rfl
    intro s _
    rw [Finset.prod_pow_eq_pow_sum,← Nat.cast_sum]
  rw [he] at h
  exact h

end
end CofactorSpectral
