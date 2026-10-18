import APPTApplications.SpikeCapacity
import APPTReview.SharpAspectLimit

open scoped BigOperators ComplexOrder Topology
open Matrix Filter
namespace ExtractionAPPT
noncomputable section

/-- Two elementary tangent bounds, valid on every positive real argument. -/
theorem log_tangent_bounds (x : ℝ) (hx : 0 < x) :
    1 - 1/x ≤ Real.log x ∧ Real.log x ≤ x-1 := by
  have h := Real.log_le_sub_one_of_pos (one_div_pos.mpr hx)
  rw [Real.log_div one_ne_zero hx.ne', Real.log_one, zero_sub] at h
  exact ⟨by linarith, Real.log_le_sub_one_of_pos hx⟩

/-- An explicit finite remainder strengthens the first-order example expansion
and in particular implies the manuscript's O(D^-2) error. -/
theorem spike_rate_error_bounds (D : ℝ) (hD : 0 < D) :
    0 ≤ (3*Real.log 3-2)/(2*D) -
      (Real.log (D/(D+2))+3*Real.log 3/(D+2))/2 ∧
    (3*Real.log 3-2)/(2*D) -
      (Real.log (D/(D+2))+3*Real.log 3/(D+2))/2 ≤ 3*Real.log 3/(D*(D+2)) := by
  have hZ : 0 < D+2 := by linarith
  obtain ⟨hl,hu⟩ := log_tangent_bounds (D/(D+2)) (div_pos hD hZ)
  have hlo : 1-1/(D/(D+2)) = -2/D := by field_simp [hD.ne',hZ.ne'] <;> ring
  have hhi : D/(D+2)-1 = -2/(D+2) := by field_simp [hZ.ne'] <;> ring
  rw [hlo] at hl
  rw [hhi] at hu
  have hc : 0 ≤ (3*Real.log 3-2)/2 := by
    have hh := (log_tangent_bounds 3 (by norm_num)).1
    norm_num at hh
    linarith
  have hupper : (Real.log (D/(D+2))+3*Real.log 3/(D+2))/2 ≤
      (3*Real.log 3-2)/(2*D) := by
    have h1 : (Real.log (D/(D+2))+3*Real.log 3/(D+2))/2 ≤
        ((3*Real.log 3-2)/2)/(D+2) := by
      calc
        _ ≤ ((-2/(D+2))+3*Real.log 3/(D+2))/2 := by linarith
        _ = _ := by ring
    have h2 := div_le_div_of_nonneg_left hc hD (show D ≤ D+2 by linarith)
    have he : ((3*Real.log 3-2)/2)/D = (3*Real.log 3-2)/(2*D) := by ring
    exact h1.trans (he ▸ h2)
  have hlower : (3*Real.log 3-2)/(2*D)-3*Real.log 3/(D*(D+2)) ≤
      (Real.log (D/(D+2))+3*Real.log 3/(D+2))/2 := by
    have he : (3*Real.log 3-2)/(2*D)-3*Real.log 3/(D*(D+2)) =
        ((-2/D)+3*Real.log 3/(D+2))/2 := by field_simp [hD.ne',hZ.ne'] <;> ring
    rw [he]
    linarith
  exact ⟨sub_nonneg.mpr hupper,by linarith⟩

theorem spikeState_capacity_error_bounds {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n)
    (v : Fin m × Fin n → ℂ) (hv : (∑ p, star (v p)*v p)=1) :
    0 ≤ (3*Real.log 3-2)/(2*((m:ℝ)*n)) - physicalCapacity m n (spikeState m n v) ∧
    (3*Real.log 3-2)/(2*((m:ℝ)*n)) - physicalCapacity m n (spikeState m n v) ≤
      3*Real.log 3/(((m:ℝ)*n)*((m:ℝ)*n+2)) := by
  rw [spikeState_capacity hm hmn v hv]
  exact spike_rate_error_bounds _ (mul_pos (by exact_mod_cast (show 0<m by omega))
    (by exact_mod_cast (show 0<n by omega)))

theorem quotient_add_two_limit (D : ℕ → ℝ) (hD : Tendsto D atTop atTop) :
    Tendsto (fun k => D k/(D k+2)) atTop (𝓝 1) := by
  have hZ : Tendsto (fun k => D k+2) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [tendsto_atTop.1 hD (b-2)] with k hk
    linarith
  have ht := hZ.const_div_atTop 2
  have hh := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1)).sub ht
  apply (show Tendsto (fun k => 1-2/(D k+2)) atTop (𝓝 (1:ℝ)) by simpa using hh).congr'
  filter_upwards [tendsto_atTop.1 hD 1] with k hk
  have hz : D k+2 ≠ 0 := by linarith
  field_simp [hz]
  <;> ring

/-- The logarithmic part of the explicit example has its exact leading
coefficient by a two-sided squeeze, without a derivative certificate. -/
theorem log_quotient_scaled_limit (D : ℕ → ℝ) (hD : Tendsto D atTop atTop) :
    Tendsto (fun k => D k * Real.log (D k/(D k+2))) atTop (𝓝 (-2)) := by
  have hb : ∀ᶠ k in atTop,
      -2 ≤ D k*Real.log (D k/(D k+2)) ∧
      D k*Real.log (D k/(D k+2)) ≤ -2*(D k/(D k+2)) := by
    filter_upwards [tendsto_atTop.1 hD 1] with k hk
    have hp : 0 < D k := by linarith
    have hz : 0 < D k+2 := by linarith
    have hx : 0 < D k/(D k+2) := div_pos hp hz
    obtain ⟨hl,hu⟩ := log_tangent_bounds _ hx
    constructor
    · have hh := mul_le_mul_of_nonneg_left hl hp.le
      have he : D k*(1-1/(D k/(D k+2))) = -2 := by
        field_simp [hp.ne',hz.ne']
        <;> ring
      rwa [he] at hh
    · have hh := mul_le_mul_of_nonneg_left hu hp.le
      have he : D k*(D k/(D k+2)-1) = -2*(D k/(D k+2)) := by
        field_simp [hz.ne']
        <;> ring
      rwa [he] at hh
  have hu : Tendsto (fun k => -2*(D k/(D k+2))) atTop (𝓝 (-2)) := by
    simpa using (quotient_add_two_limit D hD).const_mul (-2)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
    (hb.mono fun _ h => h.1) (hb.mono fun _ h => h.2)

theorem spike_capacity_coefficient_limit (D : ℕ → ℝ) (hD : Tendsto D atTop atTop) :
    Tendsto (fun k => D k *
      ((Real.log (D k/(D k+2)) + 3*Real.log 3/(D k+2))/2)) atTop
      (𝓝 ((3*Real.log 3-2)/2)) := by
  have h := ((log_quotient_scaled_limit D hD).add
    ((quotient_add_two_limit D hD).const_mul (3*Real.log 3))).div_const 2
  convert h using 1
  · ext k; ring
  · congr 1
    ring

/-- General conversion of a normalized second-moment excess into the exact
first-order logarithmic budget. -/
theorem normalized_log_budget_limit (D E : ℕ → ℝ) (γ : ℝ)
    (hD : Tendsto D atTop atTop) (hE : Tendsto E atTop (𝓝 γ)) :
    Tendsto (fun k => D k*Real.log (1+E k/D k)) atTop (𝓝 γ) := by
  have hx : Tendsto (fun k => 1+E k/D k) atTop (𝓝 (1:ℝ)) := by
    simpa using tendsto_const_nhds.add (hE.div_atTop hD)
  have hl : Tendsto (fun k => E k/(1+E k/D k)) atTop (𝓝 γ) := by
    have hh := hE.div hx (by norm_num : (1:ℝ)≠0)
    change Tendsto (fun k => E k/(1+E k/D k)) atTop (𝓝 (γ/1)) at hh
    simpa only [div_one] using hh
  have hb : ∀ᶠ k in atTop, E k/(1+E k/D k) ≤ D k*Real.log (1+E k/D k) ∧
      D k*Real.log (1+E k/D k) ≤ E k := by
    filter_upwards [tendsto_atTop.1 hD 1, hx.eventually_const_lt (by norm_num : (0:ℝ)<1)] with k hk hkx
    have hp : 0 < D k := by linarith
    obtain ⟨hlo,hhi⟩ := log_tangent_bounds _ hkx
    have hden : D k+E k ≠ 0 := by
      have he : D k*(1+E k/D k) = D k+E k := by field_simp [hp.ne']
      have hh := mul_pos hp hkx
      rw [he] at hh
      exact hh.ne'
    constructor
    · have hh := mul_le_mul_of_nonneg_left hlo hp.le
      have he : D k*(1-1/(1+E k/D k)) = E k/(1+E k/D k) := by
        field_simp [hp.ne',hden]
        <;> ring
      rwa [he] at hh
    · have hh := mul_le_mul_of_nonneg_left hhi hp.le
      have he : D k*((1+E k/D k)-1) = E k := by field_simp [hp.ne'] <;> ring
      rwa [he] at hh
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hE
    (hb.mono fun _ h => h.1) (hb.mono fun _ h => h.2)

def purityCapacityBudget (m n : ℕ) : ℝ :=
  Real.log ((m:ℝ)*n*APPTReview.apptPuritySup m n)/2

theorem balanced_purity_excess_limit (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) :
    Tendsto (fun k => APPTReview.excessPuritySup (m k) (m k)) atTop (𝓝 (8:ℝ)) := by
  have hr : Tendsto (fun k => (m k:ℝ)/(m k)) atTop (𝓝 (1:ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [tendsto_atTop.1 hm 1] with k hk
    simp [div_self (by exact_mod_cast (show m k≠0 by omega) : (m k:ℝ)≠0)]
  simpa only [show max (8:ℝ) (4+1) = 8 by norm_num] using
    APPTReview.appt_all_aspect_purity_limit m m 1 (by norm_num) hm
    (Eventually.of_forall (fun _ => le_rfl)) hr

/-- The old actual APPT purity-eight law gives a true upper budget
4/D+o(1/D) in square systems. -/
theorem balanced_purity_capacity_budget_limit (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) :
    Tendsto (fun k => ((m k:ℝ)*m k)*purityCapacityBudget (m k) (m k))
      atTop (𝓝 (4:ℝ)) := by
  have hmr : Tendsto (fun k => (m k:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hm
  have hD := hmr.atTop_mul_atTop₀ hmr
  have h := (normalized_log_budget_limit (fun k => (m k:ℝ)*m k)
    (fun k => APPTReview.excessPuritySup (m k) (m k)) 8 hD (balanced_purity_excess_limit m hm)).div_const 2
  apply (show Tendsto (fun k => ((m k:ℝ)*m k)*
      Real.log (1+APPTReview.excessPuritySup (m k) (m k)/((m k:ℝ)*m k))/2)
        atTop (𝓝 (4:ℝ)) by simpa only [show (8:ℝ)/2 = 4 by norm_num] using h).congr'
  filter_upwards [tendsto_atTop.1 hm 1] with k hk
  have hp : (m k:ℝ) ≠ 0 := by exact_mod_cast (show m k≠0 by omega)
  have he : 1+APPTReview.excessPuritySup (m k) (m k)/((m k:ℝ)*m k) =
      (m k:ℝ)*m k*APPTReview.apptPuritySup (m k) (m k) := by
    unfold APPTReview.excessPuritySup
    field_simp [hp]
    <;> ring
  rw [he]
  unfold purityCapacityBudget
  ring

/-- Concrete first-order upper comparison for the actual maximum capacity. -/
theorem balanced_apptMaxCapacity_upper (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, ((m k:ℝ)*m k)*apptMaxCapacity (m k) (m k) ≤ 4+ε := by
  filter_upwards [tendsto_atTop.1 hm 2,
    (balanced_purity_capacity_budget_limit m hm).eventually_lt_const (by linarith : (4:ℝ)<4+ε)] with k hk hb
  have hcap := apptMaxCapacity_le_puritySup hk (le_rfl : m k ≤ m k)
  exact (mul_le_mul_of_nonneg_left hcap (by positivity : (0:ℝ)≤(m k:ℝ)*m k)).trans hb.le

/-- Explicit vanishing remainder form of the actual capacity upper bound.
The term e(k)/D(k) is o(1/D(k)) because e(k) tends to zero. -/
theorem balanced_apptMaxCapacity_upper_remainder (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) :
    ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧
      ∀ᶠ k in atTop, apptMaxCapacity (m k) (m k) ≤
        4/((m k:ℝ)*m k) + e k/((m k:ℝ)*m k) := by
  let e := fun k => ((m k:ℝ)*m k)*purityCapacityBudget (m k) (m k)-4
  have he : Tendsto e atTop (𝓝 0) := by
    simpa only [sub_self] using
      (balanced_purity_capacity_budget_limit m hm).sub_const 4
  refine ⟨e,he,?_⟩
  filter_upwards [tendsto_atTop.1 hm 2] with k hk
  have hp : (m k:ℝ) ≠ 0 := by exact_mod_cast (show m k ≠ 0 by omega)
  have heq : 4/((m k:ℝ)*m k) + e k/((m k:ℝ)*m k) = purityCapacityBudget (m k) (m k) := by
    dsimp only [e]
    field_simp [hp]
    <;> ring
  rw [heq]
  exact apptMaxCapacity_le_puritySup hk (le_rfl : m k ≤ m k)

/-- The first-order coefficient belongs to the capacity of the actual physical
spike states, along arbitrary growing product dimensions and unit vectors. -/
theorem spikeState_scaled_capacity_limit (m n : ℕ → ℕ)
    (hm : ∀ k, 2 ≤ m k) (hmn : ∀ k, m k ≤ n k)
    (hD : Tendsto (fun k => (m k:ℝ)*n k) atTop atTop)
    (v : (k : ℕ) → Fin (m k) × Fin (n k) → ℂ)
    (hv : ∀ k, (∑ p, star (v k p)*v k p)=1) :
    Tendsto (fun k => ((m k:ℝ)*n k)*physicalCapacity (m k) (n k)
      (spikeState (m k) (n k) (v k))) atTop (𝓝 ((3*Real.log 3-2)/2)) := by
  apply (spike_capacity_coefficient_limit (fun k => (m k:ℝ)*n k) hD).congr'
  exact Eventually.of_forall (fun k => by dsimp only; rw [spikeState_capacity (hm k) (hmn k) (v k) (hv k)])

/-- A concrete actual APPT state supplies the lower first-order comparison;
no statement that the APPT entropy optimum is identified is made. -/
theorem balanced_apptMaxCapacity_lower (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, (3*Real.log 3-2)/2-ε ≤
      ((m k:ℝ)*m k)*apptMaxCapacity (m k) (m k) := by
  have hmr : Tendsto (fun k => (m k:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hm
  have hD := hmr.atTop_mul_atTop₀ hmr
  filter_upwards [tendsto_atTop.1 hm 2,
    (spike_capacity_coefficient_limit (fun k => (m k:ℝ)*m k) hD).eventually_const_lt
      (sub_lt_self _ hε)] with k hk hb
  letI : NeZero (m k) := ⟨by omega⟩
  let v : Fin (m k) × Fin (m k) → ℂ := fun p => if p=(0,0) then 1 else 0
  have hv : (∑ p, star (v p)*v p)=1 := by simp [v]
  have hc := spike_capacity_le_apptMax hk (le_rfl : m k ≤ m k) v hv
  exact hb.le.trans (mul_le_mul_of_nonneg_left hc (by positivity : (0:ℝ)≤(m k:ℝ)*m k))

/-- The manuscript's two self-contained first-order comparisons for the true
balanced APPT capacity maximum, with quantitative eventual epsilon bounds. -/
theorem balanced_apptMaxCapacity_first_order_bounds (m : ℕ → ℕ)
    (hm : Tendsto m atTop atTop) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, (3*Real.log 3-2)/2-ε ≤
      ((m k:ℝ)*m k)*apptMaxCapacity (m k) (m k) ∧
      ((m k:ℝ)*m k)*apptMaxCapacity (m k) (m k) ≤ 4+ε :=
  (balanced_apptMaxCapacity_lower m hm ε hε).and (balanced_apptMaxCapacity_upper m hm ε hε)

end
end ExtractionAPPT
