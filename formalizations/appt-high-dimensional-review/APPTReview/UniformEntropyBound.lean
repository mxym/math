import APPTReview.EntropyUniformMoment

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

noncomputable def entropyUniformFactor (k : ℕ) : ℝ :=
  (((k+2:ℕ):ℝ)/((k+1:ℕ):ℝ))^2*
    ((1+10*entropyBulkRadius k/(1-entropyBulkRadius k)+10*entropyUniformMeanRadius k)/
      (1-entropyUniformMeanRadius k))

theorem entropyVarianceCap_ratio_bound (k n : ℕ) :
    entropyVarianceCap k n≤(((k+2:ℕ):ℝ)/((k+1:ℕ):ℝ))^2*
      max 8 (4+(n:ℝ)/((k+2:ℕ):ℝ)) := by
  let q : ℝ := ((k+2:ℕ):ℝ)/((k+1:ℕ):ℝ)
  let K : ℝ := max 8 (4+(n:ℝ)/((k+2:ℕ):ℝ))
  have hhP : (0:ℝ)<((k+1:ℕ):ℝ) := by positivity
  have hmP : (0:ℝ)<((k+2:ℕ):ℝ) := by positivity
  have hq : 1≤q := (le_div_iff₀ hhP).2 (by push_cast;linarith)
  have hq2 : 1≤q^2 := by nlinarith
  have hrel : (Fintype.card (Fin (k+2) × Fin n):ℝ)/((k+1:ℕ):ℝ)^2=
      q^2*((n:ℝ)/((k+2:ℕ):ℝ)) := by
    simp only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul]
    dsimp [q];field_simp
  have h1 : (8:ℝ)≤q^2*K := by
    have hh:=mul_le_mul_of_nonneg_left (show (8:ℝ)≤K from le_max_left _ _) (sq_nonneg q)
    nlinarith
  have h2 : 4+q^2*((n:ℝ)/((k+2:ℕ):ℝ))≤q^2*K := by
    have hh:=mul_le_mul_of_nonneg_left (show 4+(n:ℝ)/((k+2:ℕ):ℝ)≤K from le_max_right _ _) (sq_nonneg q)
    nlinarith
  unfold entropyVarianceCap
  rw [hrel]
  exact max_le h1 h2

/-- The full physical entropy bound has a multiplicative error depending only
on the smaller dimension. The larger dimension and spectrum are unrestricted. -/
theorem density_appt_uniform_dimension_entropy_bound {k n : ℕ} (hmn : k+2≤n)
    {A : Matrix (Fin (k+2) × Fin n) (Fin (k+2) × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) (hP : APPT.Quantum.AbsolutelyPPT A)
    (hδ : entropyBulkRadius k<1) (hν : entropyUniformMeanRadius k<1) :
    2*(Fintype.card (Fin (k+2) × Fin n):ℝ)*vonNeumannDeficit hρ≤
      max 8 (4+(n:ℝ)/((k+2:ℕ):ℝ))*entropyUniformFactor k := by
  let D := (Fintype.card (Fin (k+2) × Fin n):ℝ)
  let b := hρ.1.isHermitian.eigenvalues₀ (paperPivot hmn)
  let C := entropyVarianceCap k n
  let δ := entropyBulkRadius k
  let ν := entropyUniformMeanRadius k
  let t := paperNormalization hmn hρ
  let L := 1+10*δ/(1-δ)+10*ν
  let K := max 8 (4+(n:ℝ)/((k+2:ℕ):ℝ))
  let q : ℝ := ((k+2:ℕ):ℝ)/((k+1:ℕ):ℝ)
  have hδ0 : 0≤δ := Real.sqrt_nonneg _
  have hν0 : 0≤ν := by dsimp [ν,entropyUniformMeanRadius];positivity
  have hC0 : 0≤C := entropyVarianceCap_nonneg k n
  have hL0 : 0≤L := by dsimp [L];positivity
  have htP : 0<t := paperNormalization_pos hmn hρ hP
  have hden : 0<1-ν := by linarith
  have hmean:=density_appt_uniform_mean_radius hmn hρ hP
  have htlow : 1-ν≤t := by
    change |t-1|≤ν at hmean
    linarith [(abs_le.mp hmean).1]
  have hraw:=density_appt_uniform_entropy_pivot_bound hmn hρ hP hδ hν
  have hdef:=(density_appt_paper_head_stability hmn hρ hP).1
  have he:=entropy_deficit_normalization hmn hρ hP
  have hscaled : (2*D*vonNeumannDeficit hρ)*t≤C*L := by
    change (D*vonNeumannDeficit hρ)*t=vonNeumannDeficit hρ/b at he
    change vonNeumannDeficit hρ/b≤C/2*L-paperHeadDeficit hmn hρ at hraw
    nlinarith
  have hcap : C≤q^2*K := entropyVarianceCap_ratio_bound k n
  calc
    2*D*vonNeumannDeficit hρ≤C*L/t := (le_div_iff₀ htP).2 hscaled
    _ ≤ C*L/(1-ν) := div_le_div_of_nonneg_left (mul_nonneg hC0 hL0) hden htlow
    _ ≤ (q^2*K)*L/(1-ν) := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcap hL0) hden.le
    _ = K*entropyUniformFactor k := by dsimp [entropyUniformFactor,q,L,δ,ν];ring

end APPTReview
