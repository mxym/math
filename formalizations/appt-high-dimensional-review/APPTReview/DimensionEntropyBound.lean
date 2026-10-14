import APPTReview.EntropyBulkSmallness

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

noncomputable def entropyMeanRadius (k n : ℕ) : ℝ :=
  Real.sqrt (4*entropyVarianceCap k n/((k+2:ℕ):ℝ)^2)

noncomputable def entropyMomentCap (k n : ℕ) : ℝ :=
  (1+4*(Fintype.card (Fin (k+2) × Fin n):ℝ)/((k+2:ℕ):ℝ)^2)*entropyVarianceCap k n

noncomputable def entropyTaylorError (k n : ℕ) : ℝ :=
  (entropyBulkRadius k/(2*(1-entropyBulkRadius k))+entropyMeanRadius k n/2)*entropyMomentCap k n

theorem entropyVarianceCap_nonneg (k n : ℕ) : 0≤entropyVarianceCap k n :=
  le_trans (by norm_num : (0:ℝ)≤8) (le_max_left _ _)

theorem density_appt_entropy_mean_smallness {k n : ℕ} (hmn : k+2≤n)
    {A : Matrix (Fin (k+2) × Fin n) (Fin (k+2) × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) (hP : APPT.Quantum.AbsolutelyPPT A) :
    |1/((Fintype.card (Fin (k+2) × Fin n):ℝ)*hρ.1.isHermitian.eigenvalues₀ (paperPivot hmn))-1|≤
      entropyMeanRadius k n := by
  have hh := (density_appt_entropy_normalization_budget hmn hρ hP).1
  have hs := Real.sq_sqrt (show 0≤4*entropyVarianceCap k n/((k+2:ℕ):ℝ)^2 by
    exact div_nonneg (mul_nonneg (by norm_num) (entropyVarianceCap_nonneg k n)) (sq_nonneg _))
  have hn := Real.sqrt_nonneg (4*entropyVarianceCap k n/((k+2:ℕ):ℝ)^2)
  have ha := sq_abs (1/((Fintype.card (Fin (k+2) × Fin n):ℝ)*hρ.1.isHermitian.eigenvalues₀ (paperPivot hmn))-1)
  unfold entropyMeanRadius
  nlinarith [abs_nonneg (1/((Fintype.card (Fin (k+2) × Fin n):ℝ)*hρ.1.isHermitian.eigenvalues₀ (paperPivot hmn))-1)]

/-- Dimension-only remainder bound for the full entropy argument. No head
saturation, flat spectrum, or unproved tail estimate is assumed. -/
theorem density_appt_dimension_entropy_bound {k n : ℕ} (hmn : k+2≤n)
    {A : Matrix (Fin (k+2) × Fin n) (Fin (k+2) × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) (hP : APPT.Quantum.AbsolutelyPPT A)
    (hδ : entropyBulkRadius k<1) (hν : entropyMeanRadius k n<1) :
    let D := Fintype.card (Fin (k+2) × Fin n)
    let b := hρ.1.isHermitian.eigenvalues₀ (paperPivot hmn)
    vonNeumannDeficit hρ/b≤max 4 ((D:ℝ)/((k+1:ℕ):ℝ)^2)/2+2-
      paperHeadDeficit hmn hρ+entropyTaylorError k n := by
  dsimp only
  let D := (Fintype.card (Fin (k+2) × Fin n):ℝ)
  let f := hρ.1.isHermitian.eigenvalues₀
  let b := f (paperPivot hmn)
  let δ := entropyBulkRadius k
  let ν := entropyMeanRadius k n
  let Q := entropyMomentCap k n
  have hδ0 : 0≤δ := Real.sqrt_nonneg _
  have hν0 : 0≤ν := Real.sqrt_nonneg _
  have hraw := density_appt_full_entropy_taylor_bound hmn hρ hP δ ν hδ0 hδ hν0 hν
    (density_appt_entropy_bulk_smallness hmn hρ hP)
    (density_appt_entropy_mean_smallness hmn hρ hP)
  have hb := density_appt_entropy_normalization_budget hmn hρ hP
  have hQ : (∑ i,(f i/b-1)^2)≤Q := hb.2
  have hM : D*(1/(D*b)-1)^2≤Q := by
    have hh := mul_le_mul_of_nonneg_left hb.1 (show 0≤D by dsimp [D];positivity)
    have hC := entropyVarianceCap_nonneg k n
    have he : D*(4*entropyVarianceCap k n/((k+2:ℕ):ℝ)^2)+entropyVarianceCap k n=Q := by
      dsimp [Q,entropyMomentCap,D];ring
    change D*(1/(D*b)-1)^2≤Q
    change D*(1/(D*b)-1)^2≤D*(4*entropyVarianceCap k n/((k+2:ℕ):ℝ)^2) at hh
    linarith
  have hQ0 : 0≤Q := (Finset.sum_nonneg (fun i _ => sq_nonneg _)).trans hQ
  have hcδ : 0≤δ/(2*(1-δ)) := by positivity
  have hcν : 0≤ν/(2*(1+ν)) := by positivity
  have hcν' : ν/(2*(1+ν))≤ν/2 := (div_le_iff₀ (by positivity : 0<2*(1+ν))).2 (by nlinarith)
  have ht := mul_le_mul_of_nonneg_left hQ hcδ
  have hm1 := mul_le_mul_of_nonneg_left hM hcν
  have hm2 := mul_le_mul_of_nonneg_right hcν' hQ0
  change vonNeumannDeficit hρ/b≤max 4 (D/((k+1:ℕ):ℝ)^2)/2+2-paperHeadDeficit hmn hρ+
    (δ/(2*(1-δ))+ν/2)*Q
  dsimp only at hraw
  change vonNeumannDeficit hρ/b≤max 4 (D/((k+1:ℕ):ℝ)^2)/2+2-paperHeadDeficit hmn hρ+
    (δ/(2*(1-δ)))*(∑ i,(f i/b-1)^2)+(ν/(2*(1+ν)))*D*(1/(D*b)-1)^2 at hraw
  nlinarith

end APPTReview
