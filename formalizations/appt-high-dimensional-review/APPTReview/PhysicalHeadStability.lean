import APPTReview.PhysicalHeadConditions
import APPTReview.NormalizedHeadStability

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

/-- The actual high-end deviations at the exact paper pivot. -/
noncomputable def paperHeadA {k n : ℕ} (hmn : k+2 ≤ n)
    {A : Matrix (Fin (k+2) × Fin n) (Fin (k+2) × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) : Fin (k+1) → ℝ :=
  sortedHeadA (show 3*(k+1)+1 ≤ Fintype.card (Fin (k+2) × Fin n) by
    simp only [Fintype.card_prod,Fintype.card_fin];nlinarith)
    hρ.1.isHermitian.eigenvalues₀ (hρ.1.isHermitian.eigenvalues₀ (paperPivot hmn))

noncomputable def paperHeadBeta {k n : ℕ} (hmn : k+2 ≤ n)
    {A : Matrix (Fin (k+2) × Fin n) (Fin (k+2) × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) : Fin (k+2) → ℝ :=
  sortedHeadBeta (show 3*(k+1)+1 ≤ Fintype.card (Fin (k+2) × Fin n) by
    simp only [Fintype.card_prod,Fintype.card_fin];nlinarith)
    hρ.1.isHermitian.eigenvalues₀ (hρ.1.isHermitian.eigenvalues₀ (paperPivot hmn))

noncomputable def paperHeadDeficit {k n : ℕ} (hmn : k+2 ≤ n)
    {A : Matrix (Fin (k+2) × Fin n) (Fin (k+2) × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) : ℝ :=
  2-entropyHead (paperHeadA hmn hρ) (paperHeadBeta hmn hρ)

theorem paper_head_conditions {k n : ℕ} (hmn : k+2 ≤ n)
    {A : Matrix (Fin (k+2) × Fin n) (Fin (k+2) × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) (hP : APPT.Quantum.AbsolutelyPPT A) :
    EntropyHeadConditions (paperHeadA hmn hρ) (paperHeadBeta hmn hρ) :=
  density_appt_paper_head_conditions hmn hρ hP

/-- The normalization pivot is proved strictly positive from physical APPT. -/
theorem paper_head_pivot_positive {k n : ℕ} (hmn : k+2 ≤ n)
    {A : Matrix (Fin (k+2) × Fin n) (Fin (k+2) × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) (hP : APPT.Quantum.AbsolutelyPPT A) :
    0 < hρ.1.isHermitian.eigenvalues₀ (paperPivot hmn) := by
  have hD : 4 ≤ Fintype.card (Fin (k+2) × Fin n) := by
    simp only [Fintype.card_prod,Fintype.card_fin];nlinarith
  apply ordered_pivot_positive hD _ hρ.1.isHermitian.eigenvalues₀_antitone
    (ordered_eigenvalues_sum hρ.1.isHermitian hρ.2)
    (appt_sorted_rankTwo_linear (by omega) hmn hρ.1.isHermitian hP hD)
  have hp := (paper_pivot_rank_bounds hmn).2.1
  dsimp [paperPivot]
  simp only [Fintype.card_prod,Fintype.card_fin] at *
  omega

/-- Uniform quantitative control of both extreme eigenvalues from actual APPT. -/
theorem density_appt_paper_head_stability {k n : ℕ} (hmn : k+2 ≤ n)
    {A : Matrix (Fin (k+2) × Fin n) (Fin (k+2) × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) (hP : APPT.Quantum.AbsolutelyPPT A) :
    0 < paperHeadDeficit hmn hρ ∧
    (paperHeadA hmn hρ 0)^3 ≤ 300*paperHeadDeficit hmn hρ ∧
    paperHeadBeta hmn hρ 0 ≤ 72*paperHeadDeficit hmn hρ := by
  have hh := paper_head_conditions hmn hρ hP
  exact ⟨sub_pos.mpr (entropyHead_lt_two hh),entropyHead_outlier_bounds hh⟩

/-- All eigenvalues lie between the same two actual extreme values. -/
theorem paper_head_entire_interval {k n : ℕ} (hmn : k+2 ≤ n)
    {A : Matrix (Fin (k+2) × Fin n) (Fin (k+2) × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) (hP : APPT.Quantum.AbsolutelyPPT A) :
    let f := hρ.1.isHermitian.eigenvalues₀
    let b := f (paperPivot hmn)
    ∀ i, b*(1-paperHeadBeta hmn hρ 0) ≤ f i ∧
      f i ≤ b*(1+paperHeadA hmn hρ 0) := by
  dsimp only
  let f := hρ.1.isHermitian.eigenvalues₀
  let D := Fintype.card (Fin (k+2) × Fin n)
  let b := f (paperPivot hmn)
  have hb : 0 < b := paper_head_pivot_positive hmn hρ hP
  have hD : 0 < D := by dsimp [D];simp only [Fintype.card_prod,Fintype.card_fin];nlinarith
  have hb' : hρ.1.isHermitian.eigenvalues₀ (paperPivot hmn) ≠ 0 :=
    ne_of_gt (paper_head_pivot_positive hmn hρ hP)
  have htop : b*(1+paperHeadA hmn hρ 0)=f ⟨0,hD⟩ := by
    dsimp [paperHeadA,sortedHeadA,starSlotLabel,b,f]
    field_simp [hb']
    ring
  have hbottom : b*(1-paperHeadBeta hmn hρ 0)=f ⟨D-1,by omega⟩ := by
    dsimp [paperHeadBeta,sortedHeadBeta,b,f,D]
    field_simp [hb']
    ring
  intro i
  rw [htop,hbottom]
  exact ⟨hρ.1.isHermitian.eigenvalues₀_antitone (by change i.val ≤ D-1;omega),
    hρ.1.isHermitian.eigenvalues₀_antitone (by change 0 ≤ i.val;omega)⟩

/-- The cubic modulus controls every normalized eigenvalue, not just a bulk
measure. The head deficit and all signs are derived from the actual matrix. -/
theorem density_appt_head_spectral_cubic {k n : ℕ} (hmn : k+2 ≤ n)
    {A : Matrix (Fin (k+2) × Fin n) (Fin (k+2) × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) (hP : APPT.Quantum.AbsolutelyPPT A)
    (hsmall : paperHeadDeficit hmn hρ ≤ 1/144) :
    ∀ i, |(Fintype.card (Fin (k+2) × Fin n):ℝ)*hρ.1.isHermitian.eigenvalues₀ i-1|^3
      ≤ 11904*paperHeadDeficit hmn hρ := by
  have hh := paper_head_conditions hmn hρ hP
  have hbounds := density_appt_paper_head_stability hmn hρ hP
  have hi := paper_head_entire_interval hmn hρ hP
  exact normalized_spectrum_cubic_stability _ _ _ _ _
    (paper_head_pivot_positive hmn hρ hP) (hh.a_nonneg 0) (hh.beta_nonneg 0) hh.beta_le_one
    (ordered_eigenvalues_sum hρ.1.isHermitian hρ.2) (fun i => (hi i).1) (fun i => (hi i).2)
    hbounds.1.le hsmall hbounds.2.1 hbounds.2.2

end APPTReview
