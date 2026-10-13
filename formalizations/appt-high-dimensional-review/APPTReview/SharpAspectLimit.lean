import APPTReview.SharpPurityLimit
import APPTReview.LargeAspectLimit

open scoped BigOperators ComplexOrder Topology
open Matrix Filter
namespace APPTReview

/-- A branch-independent squeeze: the aspect ratio may cross four repeatedly. -/
theorem sharp_aspect_sandwich (r γ δ X : ℝ) (hδ : 0≤δ) (hδ1 : δ≤1)
    (hr : |r-γ|≤δ) (hlo : (1-δ)*max 8 (4+r)≤X)
    (hhi : X≤(1+δ)*max 8 (4+r)) :
    |X-max 8 (4+γ)|≤δ*(max 8 (4+γ)+2) := by
  let C := max (8:ℝ) (4+r)
  let K := max (8:ℝ) (4+γ)
  have hrb := abs_le.mp hr
  have hC8 : 8≤C := le_max_left _ _
  have hCr : 4+r≤C := le_max_right _ _
  have hK8 : 8≤K := le_max_left _ _
  have hKg : 4+γ≤K := le_max_right _ _
  have hCK : C≤K+δ := max_le (by linarith) (by linarith)
  have hKC : K≤C+δ := max_le (by linarith) (by linarith)
  have h0 : 0≤1-δ := by linarith
  have h1 : 0≤1+δ := by linarith
  have hl := (mul_le_mul_of_nonneg_left (show K-δ≤C by linarith) h0).trans hlo
  have hu := hhi.trans (mul_le_mul_of_nonneg_left hCK h1)
  have hs : δ^2≤δ := by nlinarith
  exact abs_le.mpr ⟨by nlinarith,by nlinarith⟩

/-- Sharp unrestricted purity at every finite aspect ratio, including the
previously missing sector 1<=gamma<4 and two-sided approach to gamma=4. -/
theorem appt_all_aspect_purity_limit (m n : ℕ → ℕ) (γ : ℝ) (hγ : 1≤γ)
    (hTm : Tendsto m atTop atTop) (hmn : ∀ᶠ k in atTop,m k≤n k)
    (hratio : Tendsto (fun k => (n k:ℝ)/(m k)) atTop (𝓝 γ)) :
    Tendsto (fun k => excessPuritySup (m k) (n k)) atTop (𝓝 (max 8 (4+γ))) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  let K : ℝ := max 8 (4+γ)
  have hK : 0<K+2 := by have ht : (8:ℝ)≤K := le_max_left _ _; linarith
  let δ := min ((ε/2)/(K+2)) (1/2)
  have hδ : 0<δ := lt_min (by positivity) (by norm_num)
  have hδ1 : δ≤1 := by have ht := min_le_right ((ε/2)/(K+2)) (1/2:ℝ); dsimp [δ]; linarith
  have hprod : δ*(K+2)≤ε/2 := (le_div_iff₀ hK).mp (min_le_left _ _)
  obtain ⟨E,hE2,hE⟩ := appt_growing_dimension_eight_lower (8*δ) (by positivity)
  obtain ⟨L,hL⟩ := appt_growing_branch_lower δ hδ
  obtain ⟨U,hU⟩ := appt_uniform_asymptotic_upper δ hδ
  obtain ⟨K1,hK1⟩ := Metric.tendsto_atTop.1 hratio δ hδ
  have hev : ∀ᶠ k in atTop,2≤m k ∧ E≤m k ∧ L≤m k ∧ U≤m k ∧ m k≤n k := by
    filter_upwards [(Filter.tendsto_atTop.1 hTm) (max E (max L U)),hmn] with k ht hn
    have he : E≤m k := (le_max_left _ _).trans ht
    exact ⟨hE2.trans he,he,(le_trans (le_max_left _ _) (le_max_right _ _)).trans ht,
      (le_trans (le_max_right _ _) (le_max_right _ _)).trans ht,hn⟩
  obtain ⟨K2,hK2⟩ := Filter.eventually_atTop.1 hev
  refine ⟨max K1 K2,?_⟩
  intro k hk
  obtain ⟨hm2,he,hl,hu,hn⟩ := hK2 k ((le_max_right _ _).trans hk)
  have hnear := hK1 k ((le_max_left _ _).trans hk)
  rw [Real.dist_eq] at hnear
  obtain ⟨A,hA,hP,hmax⟩ := exists_appt_purity_eq_sup hm2 hn
  have hub := hU (m k) (n k) hu hn A hA hP
  rw [hmax] at hub
  have lower_of_state (B : Matrix (Fin (m k) × Fin (n k)) (Fin (m k) × Fin (n k)) ℂ)
      (hB : APPT.Quantum.IsDensity B) (hQ : APPT.Quantum.AbsolutelyPPT B) :
      ((m k:ℝ)*n k)^2*(APPT.Quantum.purity B-1/((m k:ℝ)*n k))≤excessPuritySup (m k) (n k) :=
    mul_le_mul_of_nonneg_left (sub_le_sub_right
      ((appt_purity_sup_isGreatest hm2 hn).2 ⟨B,hB,hQ,rfl⟩) _) (sq_nonneg _)
  have hlower : (1-δ)*max 8 (4+(n k:ℝ)/(m k))≤excessPuritySup (m k) (n k) := by
    by_cases hb : (8:ℝ)≤4+(n k:ℝ)/(m k)
    · obtain ⟨B,hB,hQ,hv⟩ := hL (m k) (n k) hl hn
      rw [max_eq_right hb]
      exact hv.trans (lower_of_state B hB hQ)
    · obtain ⟨B,hB,hQ,hv⟩ := hE (m k) (n k) he hn
      rw [max_eq_left (le_of_not_ge hb)]
      have hh := hv.trans (lower_of_state B hB hQ)
      linarith
  have hh := sharp_aspect_sandwich ((n k:ℝ)/(m k)) γ δ (excessPuritySup (m k) (n k))
    hδ.le hδ1 hnear.le hlower hub
  rw [Real.dist_eq]
  exact hh.trans_lt (hprod.trans_lt (by linarith))

end APPTReview
