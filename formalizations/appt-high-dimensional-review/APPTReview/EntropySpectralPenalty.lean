import APPTReview.UniformEntropyLimit
import APPTReview.PhysicalUnconditionalStability
import APPTReview.EntropyDeficitNonnegative

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

/-- A finite full-entropy/spectral certificate, valid for every eigenvalue.
There is no small head-deficit or a priori flatness hypothesis. -/
theorem density_appt_entropy_spectral_penalty {k n : ℕ} (hmn : k+2≤n)
    {A : Matrix (Fin (k+2) × Fin n) (Fin (k+2) × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) (hP : APPT.Quantum.AbsolutelyPPT A)
    (hδ : entropyBulkRadius k<1) (hν : entropyUniformMeanRadius k<1) :
    ∀ i, (Fintype.card (Fin (k+2) × Fin n):ℝ)*vonNeumannDeficit hρ+
      |(Fintype.card (Fin (k+2) × Fin n):ℝ)*hρ.1.isHermitian.eigenvalues₀ i-1|^3/300≤
      (max 8 (4+(n:ℝ)/((k+2:ℕ):ℝ))/2)*entropyUniformFactor k := by
  let D := (Fintype.card (Fin (k+2) × Fin n):ℝ)
  let b := hρ.1.isHermitian.eigenvalues₀ (paperPivot hmn)
  let C := entropyVarianceCap k n
  let δ := entropyBulkRadius k
  let ν := entropyUniformMeanRadius k
  let t := paperNormalization hmn hρ
  let E := D*vonNeumannDeficit hρ
  let L := 1+10*δ/(1-δ)+10*ν
  let K := max 8 (4+(n:ℝ)/((k+2:ℕ):ℝ))
  let q : ℝ := ((k+2:ℕ):ℝ)/((k+1:ℕ):ℝ)
  have hδ0 : 0≤δ := Real.sqrt_nonneg _
  have hν0 : 0≤ν := by dsimp [ν,entropyUniformMeanRadius];positivity
  have hL0 : 0≤L := by dsimp [L];positivity
  have hden : 0<1-ν := by linarith
  have hE0 : 0≤E := mul_nonneg (Nat.cast_nonneg _) (density_vonNeumannDeficit_nonnegative (by omega) (by omega) hρ)
  have hm:=density_appt_uniform_mean_radius hmn hρ hP
  have ht : 1-ν≤t := by change |t-1|≤ν at hm;linarith [(abs_le.mp hm).1]
  have hr:=density_appt_uniform_entropy_pivot_bound hmn hρ hP hδ hν
  have he:=entropy_deficit_normalization hmn hρ hP
  change E*t=vonNeumannDeficit hρ/b at he
  change vonNeumannDeficit hρ/b≤C/2*L-paperHeadDeficit hmn hρ at hr
  have hcap : C≤q^2*K := entropyVarianceCap_ratio_bound k n
  intro i
  let x := |D*hρ.1.isHermitian.eigenvalues₀ i-1|
  have hx : 0≤x^3 := pow_nonneg (abs_nonneg _) 3
  have hc : x^3≤300*paperHeadDeficit hmn hρ := density_appt_head_spectral_unconditional hmn hρ hP i
  have hmean:=mul_le_mul_of_nonneg_left ht hE0
  have hνx:=mul_nonneg hν0 hx
  have hh : (E+x^3/300)*(1-ν)≤C*L/2 := by nlinarith
  change E+x^3/300≤K/2*entropyUniformFactor k
  calc
    _ ≤ (C*L/2)/(1-ν) := (le_div_iff₀ hden).2 hh
    _ ≤ ((q^2*K)*L/2)/(1-ν) := div_le_div_of_nonneg_right
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcap hL0) (by norm_num)) hden.le
    _ = _ := by dsimp [entropyUniformFactor,q,L,δ,ν];ring

/-- A simple sufficient finite dimension condition for all denominators. -/
theorem entropy_uniform_radii_admissible {k : ℕ} (hk : 8≤k) :
    entropyBulkRadius k<1 ∧ entropyUniformMeanRadius k<1 := by
  have hh : (9:ℝ)≤((k+1:ℕ):ℝ) := by exact_mod_cast (show 9≤k+1 by omega)
  have hp : (0:ℝ)<((k+1:ℕ):ℝ) := by positivity
  have hf : (8:ℝ)/((k+1:ℕ):ℝ)<1 := (div_lt_one hp).2 (by linarith)
  have hs:=Real.sq_sqrt (show (0:ℝ)≤8/((k+1:ℕ):ℝ) by positivity)
  have hn:=Real.sqrt_nonneg (8/((k+1:ℕ):ℝ))
  constructor
  · unfold entropyBulkRadius;nlinarith
  · unfold entropyUniformMeanRadius
    exact (div_lt_one hp).2 (by linarith)

/-- The final all-dimensional finite statement, with only dimension, actual
density and all-global-unitary APPT assumptions. -/
theorem density_appt_finite_entropy_contrast {m n : ℕ} (hm : 10≤m) (hmn : m≤n)
    {A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) (hP : APPT.Quantum.AbsolutelyPPT A) :
    ∀ i, ((m:ℝ)*n)*vonNeumannDeficit hρ+
      |((m:ℝ)*n)*hρ.1.isHermitian.eigenvalues₀ i-1|^3/300≤
      (max 8 (4+(n:ℝ)/(m:ℝ))/2)*entropyUniformFactor (m-2) := by
  obtain ⟨k,rfl⟩ : ∃ k,m=k+2 := ⟨m-2,by omega⟩
  have hk : 8≤k := by omega
  have hr:=entropy_uniform_radii_admissible hk
  simpa only [Nat.add_sub_cancel,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul] using
    density_appt_entropy_spectral_penalty hmn hρ hP hr.1 hr.2

/-- A directly usable bound on each normalized eigenvalue from the gap of
FULL entropy to its asymptotic coefficient. The dimension error is explicit. -/
theorem density_appt_entropy_gap_controls_spectrum {m n : ℕ} (hm : 10≤m) (hmn : m≤n)
    {A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) (hP : APPT.Quantum.AbsolutelyPPT A)
    (η : ℝ) (hnear : max 8 (4+(n:ℝ)/(m:ℝ))/2-η≤((m:ℝ)*n)*vonNeumannDeficit hρ) :
    ∀ i, |((m:ℝ)*n)*hρ.1.isHermitian.eigenvalues₀ i-1|^3≤
      300*η+150*max 8 (4+(n:ℝ)/(m:ℝ))*(entropyUniformFactor (m-2)-1) := by
  intro i
  have hh:=density_appt_finite_entropy_contrast hm hmn hρ hP i
  nlinarith

end APPTReview
