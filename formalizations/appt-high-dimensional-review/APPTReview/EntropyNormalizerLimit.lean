import APPTReview.EntropyDimensionLimits

open scoped BigOperators ComplexOrder Topology
open Matrix Filter
namespace APPTReview

noncomputable def paperNormalization {k n : ℕ} (hmn : k+2≤n)
    {A : Matrix (Fin (k+2) × Fin n) (Fin (k+2) × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) : ℝ :=
  1/((Fintype.card (Fin (k+2) × Fin n):ℝ)*hρ.1.isHermitian.eigenvalues₀ (paperPivot hmn))

theorem paperNormalization_pos {k n : ℕ} (hmn : k+2≤n)
    {A : Matrix (Fin (k+2) × Fin n) (Fin (k+2) × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) (hP : APPT.Quantum.AbsolutelyPPT A) : 0<paperNormalization hmn hρ := by
  have hb := paper_head_pivot_positive hmn hρ hP
  have hD : (0:ℝ)<Fintype.card (Fin (k+2) × Fin n) := by
    simp only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul]
    have hn : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
    positivity
  unfold paperNormalization
  positivity

/-- Exact change between trace normalization and the physical paper pivot. -/
theorem entropy_deficit_normalization {k n : ℕ} (hmn : k+2≤n)
    {A : Matrix (Fin (k+2) × Fin n) (Fin (k+2) × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) (hP : APPT.Quantum.AbsolutelyPPT A) :
    ((Fintype.card (Fin (k+2) × Fin n):ℝ)*vonNeumannDeficit hρ)*paperNormalization hmn hρ=
      vonNeumannDeficit hρ/hρ.1.isHermitian.eigenvalues₀ (paperPivot hmn) := by
  have hb := ne_of_gt (paper_head_pivot_positive hmn hρ hP)
  have hD : (Fintype.card (Fin (k+2) × Fin n):ℝ)≠0 := by
    exact_mod_cast (ne_of_gt (show 0<Fintype.card (Fin (k+2) × Fin n) by
      simp only [Fintype.card_prod,Fintype.card_fin];exact Nat.mul_pos (by omega) (by omega)))
  unfold paperNormalization
  field_simp

/-- Uniform control from actual spectra, not a substituted pivot 1/D. -/
theorem appt_paperNormalization_tendsto (k n : ℕ → ℕ) (γ : ℝ)
    (A : (j : ℕ) → Matrix (Fin (k j+2) × Fin (n j)) (Fin (k j+2) × Fin (n j)) ℂ)
    (hmn : ∀ j,k j+2≤n j) (hρ : ∀ j,APPT.Quantum.IsDensity (A j))
    (hP : ∀ j,APPT.Quantum.AbsolutelyPPT (A j))
    (hk : Tendsto k atTop atTop)
    (hratio : Tendsto (fun j => (n j:ℝ)/((k j+2:ℕ):ℝ)) atTop (𝓝 γ)) :
    Tendsto (fun j => paperNormalization (hmn j) (hρ j)) atTop (𝓝 (1:ℝ)) := by
  have hν := (entropy_dimension_limits k n γ hk hratio).2.2.2.1
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨N,hN⟩ := ((tendsto_order.mp hν).2 ε hε).exists_forall_of_atTop
  refine ⟨N,?_⟩
  intro j hj
  have hb := density_appt_entropy_mean_smallness (hmn j) (hρ j) (hP j)
  rw [Real.dist_eq]
  exact hb.trans_lt (hN j hj)

theorem entropy_tail_cap_identity (γ : ℝ) : max 4 γ/2+2=max 8 (4+γ)/2 := by
  by_cases h : γ≤4
  · rw [max_eq_left h,max_eq_left (by linarith : 4+γ≤8)]
    norm_num
  · rw [max_eq_right (le_of_not_ge h),max_eq_right (by linarith : 8≤4+γ)]
    ring

end APPTReview
