import APPTReview.EntropyNormalizerLimit

open scoped BigOperators ComplexOrder Topology
open Matrix Filter
namespace APPTReview

/-- Unrestricted upper half of the von Neumann entropy-deficit law at every
fixed finite aspect ratio. It applies to any sequence of actual APPT states. -/
theorem appt_vonNeumann_fixed_aspect_upper (k n : ℕ → ℕ) (γ : ℝ)
    (A : (j : ℕ) → Matrix (Fin (k j+2) × Fin (n j)) (Fin (k j+2) × Fin (n j)) ℂ)
    (hmn : ∀ j,k j+2≤n j) (hρ : ∀ j,APPT.Quantum.IsDensity (A j))
    (hP : ∀ j,APPT.Quantum.AbsolutelyPPT (A j))
    (hk : Tendsto k atTop atTop)
    (hratio : Tendsto (fun j => (n j:ℝ)/((k j+2:ℕ):ℝ)) atTop (𝓝 γ)) :
    ∀ ε : ℝ,0<ε → ∀ᶠ j in atTop,
      (Fintype.card (Fin (k j+2) × Fin (n j)):ℝ)*vonNeumannDeficit (hρ j)≤max 8 (4+γ)/2+ε := by
  obtain ⟨hd,hC,hδ,hν,herr⟩ := entropy_dimension_limits k n γ hk hratio
  have ht := appt_paperNormalization_tendsto k n γ A hmn hρ hP hk hratio
  have hB := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (4:ℝ)) atTop (𝓝 4)).max hd
  have hupper := ((((hB.div_const 2).add_const 2).add herr).div ht (by norm_num : (1:ℝ)≠0))
  have hlim : (max 4 γ/2+2+0)/(1:ℝ)=max 8 (4+γ)/2 := by
    simp only [add_zero,div_one,entropy_tail_cap_identity]
  rw [hlim] at hupper
  intro ε hε
  have hnear := (tendsto_order.mp hupper).2 (max 8 (4+γ)/2+ε) (by linarith)
  filter_upwards [(tendsto_order.mp hδ).2 1 (by norm_num),
    (tendsto_order.mp hν).2 1 (by norm_num),hnear] with j hjδ hjν hjnear
  have hraw := density_appt_dimension_entropy_bound (hmn j) (hρ j) (hP j) hjδ hjν
  have hdef := (density_appt_paper_head_stability (hmn j) (hρ j) (hP j)).1
  have hpos := paperNormalization_pos (hmn j) (hρ j) (hP j)
  have he := entropy_deficit_normalization (hmn j) (hρ j) (hP j)
  have hb : (Fintype.card (Fin (k j+2) × Fin (n j)):ℝ)*vonNeumannDeficit (hρ j)≤
      (max 4 ((Fintype.card (Fin (k j+2) × Fin (n j)):ℝ)/((k j+1:ℕ):ℝ)^2)/2+2+
        entropyTaylorError (k j) (n j))/paperNormalization (hmn j) (hρ j) := by
    apply (le_div_iff₀ hpos).2
    rw [he]
    dsimp only at hraw
    linarith
  exact hb.trans hjnear.le

/-- The missing rigidity bridge: saturation of the FULL physical von Neumann
entropy coefficient forces saturation of the exceptional head. No tail estimate,
head-saturation assumption or flatness assumption is supplied by the caller. -/
theorem appt_full_entropy_head_saturation (k n : ℕ → ℕ) (γ : ℝ)
    (A : (j : ℕ) → Matrix (Fin (k j+2) × Fin (n j)) (Fin (k j+2) × Fin (n j)) ℂ)
    (hmn : ∀ j,k j+2≤n j) (hρ : ∀ j,APPT.Quantum.IsDensity (A j))
    (hP : ∀ j,APPT.Quantum.AbsolutelyPPT (A j))
    (hk : Tendsto k atTop atTop)
    (hratio : Tendsto (fun j => (n j:ℝ)/((k j+2:ℕ):ℝ)) atTop (𝓝 γ))
    (hentropy : Tendsto (fun j => (Fintype.card (Fin (k j+2) × Fin (n j)):ℝ)*vonNeumannDeficit (hρ j))
      atTop (𝓝 (max 8 (4+γ)/2))) :
    Tendsto (fun j => paperHeadDeficit (hmn j) (hρ j)) atTop (𝓝 (0:ℝ)) := by
  obtain ⟨hd,hC,hδ,hν,herr⟩ := entropy_dimension_limits k n γ hk hratio
  have ht := appt_paperNormalization_tendsto k n γ A hmn hρ hP hk hratio
  have hE : Tendsto (fun j => vonNeumannDeficit (hρ j)/
      (hρ j).1.isHermitian.eigenvalues₀ (paperPivot (hmn j))) atTop (𝓝 (max 8 (4+γ)/2)) := by
    have hh := hentropy.mul ht
    convert hh using 1
    · funext j
      exact (entropy_deficit_normalization (hmn j) (hρ j) (hP j)).symm
    · norm_num
  have hB := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (4:ℝ)) atTop (𝓝 4)).max hd
  have hdiff := (((hB.div_const 2).add_const 2).add herr).sub hE
  have hzero : max 4 γ/2+2+0-max 8 (4+γ)/2=0 := by rw [entropy_tail_cap_identity];ring
  rw [hzero] at hdiff
  apply Metric.tendsto_atTop.2
  intro ε hε
  have hnear := (tendsto_order.mp hdiff).2 ε hε
  have hev := ((tendsto_order.mp hδ).2 1 (by norm_num)).and
    (((tendsto_order.mp hν).2 1 (by norm_num)).and hnear)
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.1 hev
  refine ⟨N,?_⟩
  intro j hj
  obtain ⟨hjδ,hjν,hjr⟩ := hN j hj
  have hraw := density_appt_dimension_entropy_bound (hmn j) (hρ j) (hP j) hjδ hjν
  have hdef := (density_appt_paper_head_stability (hmn j) (hρ j) (hP j)).1
  rw [Real.dist_eq,sub_zero,abs_of_pos hdef]
  dsimp only at hraw hjr
  linarith

/-- All normalized eigenvalues become uniformly flat when the full entropy
coefficient saturates. This does not assert existence of saturating families. -/
theorem appt_full_entropy_saturation_flat (k n : ℕ → ℕ) (γ : ℝ)
    (A : (j : ℕ) → Matrix (Fin (k j+2) × Fin (n j)) (Fin (k j+2) × Fin (n j)) ℂ)
    (hmn : ∀ j,k j+2≤n j) (hρ : ∀ j,APPT.Quantum.IsDensity (A j))
    (hP : ∀ j,APPT.Quantum.AbsolutelyPPT (A j))
    (hk : Tendsto k atTop atTop)
    (hratio : Tendsto (fun j => (n j:ℝ)/((k j+2:ℕ):ℝ)) atTop (𝓝 γ))
    (hentropy : Tendsto (fun j => (Fintype.card (Fin (k j+2) × Fin (n j)):ℝ)*vonNeumannDeficit (hρ j))
      atTop (𝓝 (max 8 (4+γ)/2))) :
    ∀ ε : ℝ,0<ε → ∀ᶠ j in atTop,∀ i,
      |(Fintype.card (Fin (k j+2) × Fin (n j)):ℝ)*(hρ j).1.isHermitian.eigenvalues₀ i-1|<ε :=
  appt_entropy_head_saturation_flat k n A hmn hρ hP
    (appt_full_entropy_head_saturation k n γ A hmn hρ hP hk hratio hentropy)

end APPTReview
