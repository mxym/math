import APPTReview.WideAsymptotic

open scoped BigOperators ComplexOrder Topology
open Matrix Filter
namespace APPTReview

/-- Finite scalar squeeze, valid also when the approaching ratio is below four. -/
theorem large_aspect_sandwich (r γ δ X : ℝ) (hγ : 4≤γ) (hδ : 0≤δ) (hδ1 : δ≤1)
    (hr : |r-γ|≤δ) (hlo : (1-δ)*(4+r)≤X)
    (hhi : X≤(1+δ)*max 8 (4+r)) : |X-(4+γ)|≤δ*(γ+6) := by
  have hrb := abs_le.mp hr
  have h0 : 0≤1-δ := by linarith
  have h1 : 0≤1+δ := by linarith
  have hl := (mul_le_mul_of_nonneg_left (show 4+γ-δ≤4+r by linarith) h0).trans hlo
  have hm : max (8:ℝ) (4+r)≤4+γ+δ := max_le (by linarith) (by linarith)
  have hu := hhi.trans (mul_le_mul_of_nonneg_left hm h1)
  have hsq : δ^2≤δ := by nlinarith
  exact abs_le.mpr ⟨by nlinarith,by nlinarith⟩

/-- Sharp unrestricted excess-purity limit for every fixed aspect ratio γ>=4.
In particular γ=4 may be approached from either side; no eventual n>=4m is assumed. -/
theorem appt_large_aspect_purity_limit (m n : ℕ → ℕ) (γ : ℝ) (hγ : 4≤γ)
    (hTm : Tendsto m atTop atTop) (hmn : ∀ᶠ k in atTop,m k≤n k)
    (hratio : Tendsto (fun k => (n k:ℝ)/(m k)) atTop (𝓝 γ)) :
    Tendsto (fun k => excessPuritySup (m k) (n k)) atTop (𝓝 (4+γ)) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  have hgp : 0<γ+6 := by linarith
  let δ := min ((ε/2)/(γ+6)) (1/2)
  have hδ : 0<δ := lt_min (by positivity) (by norm_num)
  have hδ1 : δ≤1 := by have ht := min_le_right ((ε/2)/(γ+6)) (1/2:ℝ); dsimp [δ]; linarith
  have hprod : δ*(γ+6)≤ε/2 := (le_div_iff₀ hgp).mp (min_le_left _ _)
  obtain ⟨L,hL⟩ := appt_growing_branch_lower δ hδ
  obtain ⟨U,hU⟩ := appt_uniform_asymptotic_upper δ hδ
  obtain ⟨K1,hK1⟩ := Metric.tendsto_atTop.1 hratio δ hδ
  have hev : ∀ᶠ k in atTop,2≤m k ∧ L≤m k ∧ U≤m k ∧ m k≤n k := by
    filter_upwards [(Filter.tendsto_atTop.1 hTm) (max 2 (max L U)),hmn] with k ht hn
    exact ⟨(le_max_left _ _).trans ht,
      (le_trans (le_max_left _ _) (le_max_right _ _)).trans ht,
      (le_trans (le_max_right _ _) (le_max_right _ _)).trans ht,hn⟩
  obtain ⟨K2,hK2⟩ := Filter.eventually_atTop.1 hev
  refine ⟨max K1 K2,?_⟩
  intro k hk
  obtain ⟨hm2,hl,hu,hn⟩ := hK2 k ((le_max_right _ _).trans hk)
  have hratioNear := hK1 k ((le_max_left _ _).trans hk)
  rw [Real.dist_eq] at hratioNear
  obtain ⟨A,hd,ha,hp⟩ := exists_appt_purity_eq_sup hm2 hn
  have hub := hU (m k) (n k) hu hn A hd ha
  rw [hp] at hub
  obtain ⟨B,hBd,hBa,hlb⟩ := hL (m k) (n k) hl hn
  have hBsup : APPT.Quantum.purity B≤apptPuritySup (m k) (n k) :=
    (appt_purity_sup_isGreatest hm2 hn).2 ⟨B,hBd,hBa,rfl⟩
  have hlower : (1-δ)*(4+(n k:ℝ)/(m k))≤excessPuritySup (m k) (n k) :=
    hlb.trans (mul_le_mul_of_nonneg_left (sub_le_sub_right hBsup _) (sq_nonneg _))
  have he := large_aspect_sandwich ((n k:ℝ)/(m k)) γ δ (excessPuritySup (m k) (n k))
    hγ hδ.le hδ1 hratioNear.le hlower hub
  rw [Real.dist_eq]
  exact he.trans_lt (hprod.trans_lt (by linarith))

end APPTReview
