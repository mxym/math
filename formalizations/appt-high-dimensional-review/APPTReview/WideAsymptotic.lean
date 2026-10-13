import APPTReview.TotalBranchLower
import APPTReview.AllDimensionUpper

open scoped BigOperators ComplexOrder Topology
open Matrix Filter
namespace APPTReview

noncomputable def excessPuritySup (m n : ℕ) : ℝ :=
  ((m:ℝ)*n)^2*(apptPuritySup m n-1/((m:ℝ)*n))

noncomputable def broadBranchCoefficient (m n : ℕ) : ℝ :=
  4+((m:ℝ)*n)/((m:ℝ)^2-1)

/-- The constructive lower bound is transported to the original physical maximum. -/
theorem appt_total_branch_sup_lower (ε : ℝ) (hε : 0<ε) :
    ∃ N : ℕ, ∀ (m n : ℕ), 2≤m → m≤n → N≤m*n →
      (1-ε)*broadBranchCoefficient m n≤excessPuritySup m n := by
  obtain ⟨N,hN⟩ := appt_total_dimension_branch_lower ε hε
  refine ⟨N,?_⟩
  intro m n hm hmn hD
  obtain ⟨A,hd,ha,hlo⟩ := hN m n hm hmn hD
  have hmax := appt_purity_sup_isGreatest hm hmn
  have hP : APPT.Quantum.purity A≤apptPuritySup m n := hmax.2 ⟨A,hd,ha,rfl⟩
  exact hlo.trans (mul_le_mul_of_nonneg_left (sub_le_sub_right hP _) (sq_nonneg _))

/-- Both sides of the exact asymptotic coefficient throughout the wide sector.
One total-dimension threshold works also for fixed m and unbounded aspect ratio. -/
theorem appt_wide_sup_two_sided (ε : ℝ) (hε : 0<ε) :
    ∃ N : ℕ, ∀ (m n : ℕ), 2≤m → 4*m≤n → N≤m*n →
      (1-ε)*broadBranchCoefficient m n≤excessPuritySup m n ∧
      excessPuritySup m n≤(1+ε)*broadBranchCoefficient m n := by
  obtain ⟨L,hL⟩ := appt_total_branch_sup_lower ε hε
  obtain ⟨U,hU⟩ := appt_total_dimension_uniform_upper ε hε
  refine ⟨max L U,?_⟩
  intro m n hm hwide hD
  have hmn : m≤n := by omega
  refine ⟨hL m n hm hmn ((le_max_left _ _).trans hD),?_⟩
  obtain ⟨A,hd,ha,hmax⟩ := exists_appt_purity_eq_sup hm hmn
  have hup := hU m n hm hmn ((le_max_right _ _).trans hD) A hd ha
  have hmR : (2:ℝ)≤m := by exact_mod_cast hm
  have hnR : 4*(m:ℝ)≤n := by exact_mod_cast hwide
  have hden : (0:ℝ)<(m:ℝ)^2-1 := by nlinarith
  have hcoeff : (8:ℝ)≤4+((m:ℝ)*n)/((m:ℝ)^2-1) := by
    have hx : (4:ℝ)≤((m:ℝ)*n)/((m:ℝ)^2-1) := (le_div_iff₀ hden).2 (by nlinarith)
    linarith
  rw [max_eq_right hcoeff,hmax] at hup
  exact hup

theorem appt_wide_relative_error (ε : ℝ) (hε : 0<ε) :
    ∃ N : ℕ, ∀ (m n : ℕ), 2≤m → 4*m≤n → N≤m*n →
      |excessPuritySup m n/broadBranchCoefficient m n-1|≤ε := by
  obtain ⟨N,hN⟩ := appt_wide_sup_two_sided ε hε
  refine ⟨N,?_⟩
  intro m n hm hw hD
  have hb := hN m n hm hw hD
  have hmR : (2:ℝ)≤m := by exact_mod_cast hm
  have hden : (0:ℝ)<(m:ℝ)^2-1 := by nlinarith
  have hC : 0<broadBranchCoefficient m n := by unfold broadBranchCoefficient; positivity
  have hlo : 1-ε≤excessPuritySup m n/broadBranchCoefficient m n := (le_div_iff₀ hC).2 hb.1
  have hhi : excessPuritySup m n/broadBranchCoefficient m n≤1+ε := (div_le_iff₀ hC).2 hb.2
  exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- A genuine filter limit along every dimension sequence in the wide sector.
The smaller dimension need not tend to infinity or stay fixed. -/
theorem appt_wide_purity_asymptotic (m n : ℕ → ℕ)
    (hm : ∀ᶠ k in atTop,2≤m k) (hw : ∀ᶠ k in atTop,4*m k≤n k)
    (hD : Tendsto (fun k => m k*n k) atTop atTop) :
    Tendsto (fun k => excessPuritySup (m k) (n k)/broadBranchCoefficient (m k) (n k))
      atTop (𝓝 (1:ℝ)) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨N,hN⟩ := appt_wide_relative_error (ε/2) (by positivity)
  have hev : ∀ᶠ k in atTop,2≤m k ∧ 4*m k≤n k ∧ N≤m k*n k := by
    filter_upwards [hm,hw,(Filter.tendsto_atTop.1 hD) N] with k h1 h2 h3
    exact ⟨h1,h2,h3⟩
  obtain ⟨K,hK⟩ := Filter.eventually_atTop.1 hev
  refine ⟨K,?_⟩
  intro k hk
  have hx := hK k hk
  have hb := hN (m k) (n k) hx.1 hx.2.1 hx.2.2
  rw [Real.dist_eq]
  linarith

end APPTReview
