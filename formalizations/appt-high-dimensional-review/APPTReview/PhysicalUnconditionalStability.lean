import APPTReview.UnconditionalHeadStability

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

/-- A global contrast cap for every actual APPT eigenvalue, including zero.
This uses the physical rank-two upper bound, not an imposed spectral interval. -/
theorem density_appt_normalized_contrast_le_two {k n : ℕ} (hmn : k+2≤n)
    {A : Matrix (Fin (k+2) × Fin n) (Fin (k+2) × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) (hP : APPT.Quantum.AbsolutelyPPT A) :
    ∀ i, |(Fintype.card (Fin (k+2) × Fin n):ℝ)*hρ.1.isHermitian.eigenvalues₀ i-1|≤2 := by
  let D := Fintype.card (Fin (k+2) × Fin n)
  let f := hρ.1.isHermitian.eigenvalues₀
  have hD : 4≤D := by dsimp [D];simp only [Fintype.card_prod,Fintype.card_fin];nlinarith
  have htop : f (rankTwoLabels hD (1,0))≤3/((D:ℝ)+2) := by
    simpa only [D,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul] using
      appt_largest_eigenvalue_bound (m:=k+2) (by omega) hmn hρ hP hD
  intro i
  have hi : 0≤f i := by
    have hh:=hρ.1.eigenvalues_nonneg (spectralLabel _ i)
    simpa only [eigenvalues_spectralLabel] using hh
  have hfi : f i≤3/((D:ℝ)+2) :=
    (hρ.1.isHermitian.eigenvalues₀_antitone (show rankTwoLabels hD (1,0)≤ i by change 0≤ i.val;omega)).trans htop
  have hp : 0<(D:ℝ)+2 := by positivity
  have hu:=(le_div_iff₀ hp).mp hfi
  have hn:=mul_nonneg (Nat.cast_nonneg D : (0:ℝ)≤D) hi
  change |(D:ℝ)*f i-1|≤2
  exact abs_le.mpr ⟨by nlinarith,by nlinarith⟩

/-- Dimension-independent stability for the entire actual spectrum, with no
small-deficit, full-rank, or flatness hypothesis. -/
theorem density_appt_head_spectral_unconditional {k n : ℕ} (hmn : k+2≤n)
    {A : Matrix (Fin (k+2) × Fin n) (Fin (k+2) × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) (hP : APPT.Quantum.AbsolutelyPPT A) :
    ∀ i, |(Fintype.card (Fin (k+2) × Fin n):ℝ)*hρ.1.isHermitian.eigenvalues₀ i-1|^3
      ≤300*paperHeadDeficit hmn hρ := by
  let f := hρ.1.isHermitian.eigenvalues₀
  let b := f (paperPivot hmn)
  let a := paperHeadA hmn hρ
  let β := paperHeadBeta hmn hρ
  have h:=paper_head_conditions hmn hρ hP
  have hi:=paper_head_entire_interval hmn hρ hP
  have hc:=density_appt_normalized_contrast_le_two hmn hρ hP
  intro i
  apply entropyHead_unconditional_contrast h _ (abs_nonneg _) (hc i)
  intro hβ
  exact trace_normalized_contrast f b (a 0) (β 0)
    (paper_head_pivot_positive hmn hρ hP) (h.a_nonneg 0) (h.beta_nonneg 0) hβ
    (ordered_eigenvalues_sum hρ.1.isHermitian hρ.2) (fun j => (hi j).1) (fun j => (hi j).2) i

end APPTReview
