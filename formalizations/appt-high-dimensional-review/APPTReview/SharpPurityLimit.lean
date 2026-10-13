import APPTReview.SharpPurityLower

open scoped BigOperators ComplexOrder Topology
open Matrix Filter
namespace APPTReview

theorem sharpPurityCoefficient_pos (m n : ℕ) : 0<sharpPurityCoefficient m n :=
  lt_of_lt_of_le (by norm_num : (0:ℝ)<8) (le_max_left _ _)

/-- Quantified uniform relative error for the first nonzero purity excess.
The bound is simultaneous in every admissible dimension pair, not a fixed-ratio limit. -/
theorem appt_sharp_purity_relative_error (ε : ℝ) (hε : 0<ε) :
    ∃ N : ℕ, ∀ m n : ℕ, 2≤m → m≤n → N≤m*n →
      |excessPuritySup m n/sharpPurityCoefficient m n-1|≤ε := by
  obtain ⟨N,hN⟩ := appt_sharp_sup_two_sided ε hε
  refine ⟨N,?_⟩
  intro m n hm hmn hD
  obtain ⟨hl,hu⟩ := hN m n hm hmn hD
  have hC := sharpPurityCoefficient_pos m n
  have hlo : 1-ε≤excessPuritySup m n/sharpPurityCoefficient m n :=
    (le_div_iff₀ hC).2 hl
  have hhi : excessPuritySup m n/sharpPurityCoefficient m n≤1+ε :=
    (div_le_iff₀ hC).2 hu
  exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- The complete sharp purity law along every dimension sequence of growing
product. The smaller dimension may be fixed, growing, or oscillating. -/
theorem appt_sharp_purity_asymptotic (m n : ℕ → ℕ)
    (hm : ∀ᶠ k in atTop,2≤m k) (hmn : ∀ᶠ k in atTop,m k≤n k)
    (hD : Tendsto (fun k => m k*n k) atTop atTop) :
    Tendsto (fun k => excessPuritySup (m k) (n k)/sharpPurityCoefficient (m k) (n k))
      atTop (𝓝 (1:ℝ)) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨N,hN⟩ := appt_sharp_purity_relative_error (ε/2) (by positivity)
  have hev : ∀ᶠ k in atTop,2≤m k ∧ m k≤n k ∧ N≤m k*n k := by
    filter_upwards [hm,hmn,(Filter.tendsto_atTop.1 hD) N] with k h1 h2 h3
    exact ⟨h1,h2,h3⟩
  obtain ⟨K,hK⟩ := Filter.eventually_atTop.1 hev
  refine ⟨K,?_⟩
  intro k hk
  obtain ⟨h1,h2,h3⟩ := hK k hk
  have hh := hN (m k) (n k) h1 h2 h3
  rw [Real.dist_eq]
  linarith

/-- Same limit with the full physical formula visible in the final type. -/
theorem appt_purity_excess_equivalent (m n : ℕ → ℕ)
    (hm : ∀ᶠ k in atTop,2≤m k) (hmn : ∀ᶠ k in atTop,m k≤n k)
    (hD : Tendsto (fun k => m k*n k) atTop atTop) :
    Tendsto (fun k =>
      (((m k:ℝ)*n k)^2*(apptPuritySup (m k) (n k)-1/((m k:ℝ)*n k))) /
        max 8 (4+((m k:ℝ)*n k)/((m k:ℝ)^2-1))) atTop (𝓝 (1:ℝ)) :=
  appt_sharp_purity_asymptotic m n hm hmn hD

end APPTReview
