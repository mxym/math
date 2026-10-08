import Entry002.Sieve
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! Exact conversion from actual cumulative counts to the inclusive real
dyadic count in `Sieve.lean`. No prime-number or splitting-density theorem is
asserted. The cumulative asymptotic is an explicit input.

The two generic analytic conversion proofs below replay the mathlib-only
arguments in the separately audited ArithmeticSupplyDensityConversions.lean
(lines 25--61), without importing its external PNT dependency or any theorem
from that project. The finite endpoint identification and negligible-endpoint
proofs are new. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace Entry002

/-- Actual elements of `P` at or below a real endpoint. -/
noncomputable def cumulativePrimeSet (P : Set ℕ) (x : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range (⌊x⌋₊ + 1)).filter (fun p => p ∈ P ∧ (p : ℝ) ≤ x)

noncomputable def cumulativePrimeCount (P : Set ℕ) (x : ℝ) : ℕ :=
  (cumulativePrimeSet P x).card

@[simp] theorem mem_cumulativePrimeSet (P : Set ℕ) (x : ℝ) (p : ℕ) :
    p ∈ cumulativePrimeSet P x ↔ p ∈ P ∧ (p : ℝ) ≤ x := by
  classical
  simp only [cumulativePrimeSet, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    have hp := Nat.le_floor h.2
    exact ⟨by omega, h⟩

theorem cumulativePrimeCount_mono (P : Set ℕ) : Monotone (cumulativePrimeCount P) := by
  intro x y hxy
  apply Finset.card_le_card
  intro p hp
  obtain ⟨hpP,hpx⟩ := (mem_cumulativePrimeSet P x p).mp hp
  exact (mem_cumulativePrimeSet P y p).mpr ⟨hpP, hpx.trans hxy⟩

/-- The literal inclusive dyadic set whose cardinality is `dyadicPrimeCount`. -/
noncomputable def inclusiveDyadicPrimes (P : Set ℕ) (T : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range (⌊2*T⌋₊ + 1)).filter
    (fun p => p ∈ P ∧ T ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*T)

@[simp] theorem inclusiveDyadicPrimes_card (P : Set ℕ) (T : ℝ) :
    (inclusiveDyadicPrimes P T).card = dyadicPrimeCount P T := rfl

@[simp] theorem mem_inclusiveDyadicPrimes (P : Set ℕ) (T : ℝ) (p : ℕ) :
    p ∈ inclusiveDyadicPrimes P T ↔ p ∈ P ∧ T ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*T := by
  classical
  simp only [inclusiveDyadicPrimes, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    have hp := Nat.le_floor h.2.2
    exact ⟨by omega, h⟩

/-- At most one actual element can equal a prescribed real endpoint. -/
noncomputable def cumulativeEndpointSet (P : Set ℕ) (T : ℝ) : Finset ℕ := by
  classical
  exact (cumulativePrimeSet P T).filter (fun p => (p : ℝ) = T)

noncomputable def cumulativeEndpointCount (P : Set ℕ) (T : ℝ) : ℕ :=
  (cumulativeEndpointSet P T).card

@[simp] theorem mem_cumulativeEndpointSet (P : Set ℕ) (T : ℝ) (p : ℕ) :
    p ∈ cumulativeEndpointSet P T ↔ p ∈ P ∧ (p : ℝ) = T := by
  classical
  simp only [cumulativeEndpointSet, Finset.mem_filter, mem_cumulativePrimeSet]
  constructor
  · exact fun h => ⟨h.1.1,h.2⟩
  · exact fun h => ⟨⟨h.1,h.2.le⟩,h.2⟩

theorem cumulativeEndpointCount_le_one (P : Set ℕ) (T : ℝ) :
    cumulativeEndpointCount P T ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro p hp q hq
  have hpT := (mem_cumulativeEndpointSet P T p).mp hp
  have hqT := (mem_cumulativeEndpointSet P T q).mp hq
  exact_mod_cast hpT.2.trans hqT.2.symm

/-- Exact inclusive-endpoint correction. This uses the actual unchanged
`dyadicPrimeCount`, not an asymptotically substituted count definition. -/
theorem dyadicPrimeCount_cumulative_identity (P : Set ℕ) {T : ℝ} (hT : 0 ≤ T) :
    dyadicPrimeCount P T + cumulativePrimeCount P T =
      cumulativePrimeCount P (2*T) + cumulativeEndpointCount P T := by
  classical
  have hu : inclusiveDyadicPrimes P T ∪ cumulativePrimeSet P T = cumulativePrimeSet P (2*T) := by
    ext p
    simp only [Finset.mem_union, mem_inclusiveDyadicPrimes, mem_cumulativePrimeSet]
    constructor
    · rintro (⟨hp,_,hhi⟩ | ⟨hp,hlo⟩)
      · exact ⟨hp,hhi⟩
      · exact ⟨hp,by linarith⟩
    · rintro ⟨hp,hhi⟩
      rcases le_total T (p : ℝ) with hlo | hlo
      · exact Or.inl ⟨hp,hlo,hhi⟩
      · exact Or.inr ⟨hp,hlo⟩
  have hi : inclusiveDyadicPrimes P T ∩ cumulativePrimeSet P T = cumulativeEndpointSet P T := by
    ext p
    simp only [Finset.mem_inter, mem_inclusiveDyadicPrimes, mem_cumulativePrimeSet,
      mem_cumulativeEndpointSet]
    constructor
    · rintro ⟨⟨hp,hlo,_⟩,⟨_,hhi⟩⟩
      exact ⟨hp,le_antisymm hhi hlo⟩
    · rintro ⟨hp,he⟩
      exact ⟨⟨hp,he.ge,by linarith⟩,⟨hp,he.le⟩⟩
  have hc := Finset.card_union_add_card_inter (inclusiveDyadicPrimes P T) (cumulativePrimeSet P T)
  rw [hu,hi,inclusiveDyadicPrimes_card] at hc
  exact hc.symm

/-- The inclusive dyadic count differs from the cumulative difference by
zero or one, including every real lower endpoint. -/
theorem dyadicPrimeCount_cumulative_error (P : Set ℕ) {T : ℝ} (hT : 0 ≤ T) :
    cumulativePrimeCount P (2*T) - cumulativePrimeCount P T ≤ dyadicPrimeCount P T ∧
      dyadicPrimeCount P T ≤ cumulativePrimeCount P (2*T) - cumulativePrimeCount P T + 1 := by
  have hid := dyadicPrimeCount_cumulative_identity P hT
  have hε := cumulativeEndpointCount_le_one P T
  have hm := cumulativePrimeCount_mono P (show T ≤ 2*T by linarith)
  omega

theorem dyadicPrimeCount_cumulative_real_identity (P : Set ℕ) {T : ℝ} (hT : 0 ≤ T) :
    (dyadicPrimeCount P T : ℝ) -
      ((cumulativePrimeCount P (2*T) : ℝ) - (cumulativePrimeCount P T : ℝ)) =
        (cumulativeEndpointCount P T : ℝ) := by
  have h : (dyadicPrimeCount P T : ℝ) + cumulativePrimeCount P T =
      cumulativePrimeCount P (2*T) + cumulativeEndpointCount P T := by
    exact_mod_cast dyadicPrimeCount_cumulative_identity P hT
  linarith

theorem dyadicPrimeCount_cumulative_real_error (P : Set ℕ) {T : ℝ} (hT : 0 ≤ T) :
    |(dyadicPrimeCount P T : ℝ) -
      ((cumulativePrimeCount P (2*T) : ℝ) - (cumulativePrimeCount P T : ℝ))| ≤ 1 := by
  rw [dyadicPrimeCount_cumulative_real_identity P hT, abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast cumulativeEndpointCount_le_one P T

/-- Pure analytic comparison of the cumulative normalizers at `T` and `2T`. -/
theorem cumulative_dyadic_normalizer_ratio :
    Tendsto (fun x : ℝ => ((2*x) / Real.log (2*x)) / (x / Real.log x)) atTop (nhds 2) := by
  have hsmall : Tendsto (fun x : ℝ => Real.log 2 / Real.log x) atTop (nhds 0) :=
    Real.isLittleO_const_log_atTop.tendsto_div_nhds_zero
  have h := ((tendsto_const_nhds.add hsmall).inv₀
    (by norm_num : (1 : ℝ) + 0 ≠ 0)).const_mul 2
  norm_num only [add_zero, inv_one, mul_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx)
  have hlog : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  have hlog2 : Real.log (2*x) ≠ 0 := (Real.log_pos (by linarith : (1 : ℝ) < 2*x)).ne'
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hx0] at hlog2 ⊢
  have hrew : 1 + Real.log 2 / Real.log x =
      (Real.log 2 + Real.log x) / Real.log x := by
    rw [add_div, div_self hlog, add_comm]
  rw [hrew, inv_div]
  field_simp [hlog2]

/-- A supplied cumulative-count asymptotic gives its dyadic difference limit.
This is generic analysis and does not supply an arithmetic density. -/
theorem cumulative_dyadic_difference_ratio (F : ℝ → ℝ) (ρ : ℝ)
    (hF : Tendsto (fun x => F x / (x / Real.log x)) atTop (nhds ρ)) :
    Tendsto (fun x => (F (2*x) - F x) / (x / Real.log x)) atTop (nhds ρ) := by
  have htwice := hF.comp (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have h := (htwice.mul cumulative_dyadic_normalizer_ratio).sub hF
  have hlim : ρ * 2 - ρ = ρ := by ring
  rw [hlim] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx)
  have hlog : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  have hlog2 : Real.log (2*x) ≠ 0 := (Real.log_pos (by linarith : (1 : ℝ) < 2*x)).ne'
  dsimp only [Function.comp_def, id]
  field_simp

/-- The actual inclusive lower-endpoint correction is negligible. -/
theorem cumulativeEndpointCount_ratio_tendsto_zero (P : Set ℕ) :
    Tendsto (fun T : ℝ => (cumulativeEndpointCount P T : ℝ) / (T / Real.log T)) atTop (nhds 0) := by
  have hlog : Tendsto (fun T : ℝ => Real.log T / T) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  apply squeeze_zero' _ _ hlog
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    exact div_nonneg (Nat.cast_nonneg _) (div_pos (by linarith) (Real.log_pos hT)).le
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    have hp : (cumulativeEndpointCount P T : ℝ) ≤ 1 := by
      exact_mod_cast cumulativeEndpointCount_le_one P T
    calc
      _ ≤ 1 / (T / Real.log T) := div_le_div_of_nonneg_right hp
        (div_pos (by linarith) (Real.log_pos hT)).le
      _ = _ := by simp only [one_div_div]

/-- A supplied cumulative density implies the literal inclusive A5 dyadic
limit, with the endpoint correction proved rather than suppressed. -/
theorem dyadicPrimeCount_tendsto_of_cumulative (P : Set ℕ) (ρ : ℝ)
    (hF : Tendsto (fun x => (cumulativePrimeCount P x : ℝ) / (x / Real.log x)) atTop (nhds ρ)) :
    Tendsto (fun T : ℝ => (dyadicPrimeCount P T : ℝ) / (T / Real.log T)) atTop (nhds ρ) := by
  have hdiff := cumulative_dyadic_difference_ratio (fun x => (cumulativePrimeCount P x : ℝ)) ρ hF
  have hsum := hdiff.add (cumulativeEndpointCount_ratio_tendsto_zero P)
  simp only [add_zero] at hsum
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  rw [← add_div]
  congr 1
  have h := dyadicPrimeCount_cumulative_real_identity P hT
  linarith

end Entry002
