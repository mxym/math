import CofactorSubsetGenerating
import Mathlib.Analysis.SpecificLimits.Normed

/-! Actual infinite integer tails bound every finite family of distinct degrees. -/
set_option autoImplicit false
open scoped BigOperators Topology
open Filter
namespace CofactorSpectral
noncomputable section

def geometricTail (q : ℝ) (m : ℕ) : ℝ := ∑' i : ℕ, q^(i+m)
def weightedGeometricTail (q : ℝ) (m : ℕ) : ℝ := ∑' i : ℕ, ((i+m : ℕ) : ℝ)*q^(i+m)
def ringTailBound (q : ℝ) (m : ℕ) : ℝ :=
  2*Real.exp 1*Real.exp (geometricTail q m)*weightedGeometricTail q m

theorem finite_distinct_tail_le {K : Type*} [Fintype K] [DecidableEq K]
    (f : ℕ → ℝ) (hf : Summable f) (hfn : ∀ i, 0 ≤ f i)
    (m : ℕ) (d : K → ℕ) (hd : Function.Injective d) (hm : ∀ i, m ≤ d i) :
    (∑ i, f (d i)) ≤ ∑' j : ℕ, f (j+m) := by
  classical
  let e : K → ℕ := fun i => d i-m
  have he : Function.Injective e := by
    intro i j hij
    apply hd
    have hi := Nat.sub_add_cancel (hm i)
    have hj := Nat.sub_add_cancel (hm j)
    dsimp [e] at hij
    omega
  have h := Summable.sum_le_tsum (Finset.univ.image e)
    (fun j _ => hfn (j+m)) ((summable_nat_add_iff m).mpr hf)
  have hs : (∑ j ∈ Finset.univ.image e, f (j+m)) = ∑ i, f (d i) := by
    rw [Finset.sum_image (fun i _ j _ h => he h)]
    apply Finset.sum_congr rfl
    intro i _
    rw [show e i+m = d i from Nat.sub_add_cancel (hm i)]
  rw [hs] at h
  exact h

theorem geometricTail_nonneg (q : ℝ) (hq : 0 ≤ q) (m : ℕ) : 0 ≤ geometricTail q m :=
  tsum_nonneg (fun _ => pow_nonneg hq _)

theorem weightedGeometricTail_nonneg (q : ℝ) (hq : 0 ≤ q) (m : ℕ) :
    0 ≤ weightedGeometricTail q m :=
  tsum_nonneg (fun _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hq _))

theorem geometric_distinct_sum_le_tail {K : Type*} [Fintype K] [DecidableEq K]
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) (m : ℕ) (d : K → ℕ)
    (hd : Function.Injective d) (hm : ∀ i, m ≤ d i) :
    (∑ i, q^(d i)) ≤ geometricTail q m :=
  finite_distinct_tail_le (fun i => q^i) (summable_geometric_of_lt_one hq hq1)
    (fun _ => pow_nonneg hq _) m d hd hm

theorem weighted_geometric_distinct_sum_le_tail {K : Type*} [Fintype K] [DecidableEq K]
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) (m : ℕ) (d : K → ℕ)
    (hd : Function.Injective d) (hm : ∀ i, m ≤ d i) :
    (∑ i, (d i : ℝ)*q^(d i)) ≤ weightedGeometricTail q m := by
  have hn : ‖q‖ < 1 := by simpa only [Real.norm_eq_abs,abs_of_nonneg hq] using hq1
  have hs : Summable (fun i : ℕ => (i : ℝ)*q^i) := by
    simpa only [pow_one] using summable_pow_mul_geometric_of_norm_lt_one 1 hn
  exact finite_distinct_tail_le _ hs
    (fun _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hq _)) m d hd hm

theorem geometric_subset_integer_tail_bound {K : Type*} [Fintype K] [DecidableEq K]
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) (m : ℕ) (d : K → ℕ)
    (hd : Function.Injective d) (hm : ∀ i, m ≤ d i) :
    2*Real.exp 1*(∑ s : Finset K, (∑ i ∈ s, d i : ℕ)*q^(∑ i ∈ s, d i)) ≤
      ringTailBound q m := by
  have hs := geometric_subset_weighted_sum_bound d q hq
  have h0 := geometric_distinct_sum_le_tail q hq hq1 m d hd hm
  have h1 := weighted_geometric_distinct_sum_le_tail q hq hq1 m d hd hm
  have hsum : 0 ≤ ∑ i, (d i : ℝ)*q^(d i) :=
    Finset.sum_nonneg (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hq _))
  have htotal := hs.trans (mul_le_mul (Real.exp_le_exp.mpr h0) h1 hsum (Real.exp_pos _).le)
  have h := mul_le_mul_of_nonneg_left htotal (by positivity : 0 ≤ 2*Real.exp 1)
  simpa only [ringTailBound,mul_assoc] using h

theorem ringTailBound_tendsto_zero (q : ℝ) (_hq : 0 ≤ q) (_hq1 : q < 1) :
    Tendsto (ringTailBound q) atTop (𝓝 0) := by
  have h0 := tendsto_sum_nat_add (fun i : ℕ => q^i)
  have h1 := tendsto_sum_nat_add (fun i : ℕ => (i : ℝ)*q^i)
  have hc : Tendsto (fun _ : ℕ => 2*Real.exp 1) atTop (𝓝 (2*Real.exp 1)) := tendsto_const_nhds
  have he : Tendsto (fun m => Real.exp (∑' i : ℕ, q^(i+m))) atTop (𝓝 (Real.exp 0)) :=
    Real.continuous_exp.continuousAt.tendsto.comp h0
  have h := ((hc.mul he).mul h1)
  change Tendsto (fun m => 2*Real.exp 1*Real.exp (∑' i : ℕ, q^(i+m))*
    (∑' i : ℕ, ((i+m : ℕ) : ℝ)*q^(i+m))) atTop (𝓝 0)
  simpa only [mul_zero] using h

theorem exists_small_ringTailBound (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) (η : ℝ) (hη : 0 < η) :
    ∃ m : ℕ, 2 ≤ m ∧ ringTailBound q m ≤ η := by
  have h := (ringTailBound_tendsto_zero q hq hq1).eventually (eventually_le_nhds hη)
  obtain ⟨m,hm⟩ := (eventually_atTop.mp h)
  exact ⟨max m 2,le_max_right _ _,hm _ (le_max_left _ _)⟩

end
end CofactorSpectral
