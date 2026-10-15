import APPTReview.EntropyMeanPhysical

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

noncomputable def entropyUniformMeanRadius (k : ℕ) : ℝ := 3/((k+1:ℕ):ℝ)

/-- Uniform second-moment control relative to the exact paper pivot.
The constant is independent of the aspect ratio, even when n/m diverges. -/
theorem density_appt_uniform_moment_budget {k n : ℕ} (hmn : k+2≤n)
    {A : Matrix (Fin (k+2) × Fin n) (Fin (k+2) × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) (hP : APPT.Quantum.AbsolutelyPPT A) :
    let D := (Fintype.card (Fin (k+2) × Fin n):ℝ)
    let f := hρ.1.isHermitian.eigenvalues₀
    let b := f (paperPivot hmn)
    (∑ i,(f i/b-1)^2)≤10*entropyVarianceCap k n ∧
    D*(1/(D*b)-1)^2≤9*entropyVarianceCap k n := by
  dsimp only
  let D := Fintype.card (Fin (k+2) × Fin n)
  let f := hρ.1.isHermitian.eigenvalues₀
  let b := f (paperPivot hmn)
  let C := entropyVarianceCap k n
  have hb : 0<b := paper_head_pivot_positive hmn hρ hP
  have hD : 0<D := by dsimp [D];simp only [Fintype.card_prod,Fintype.card_fin];exact Nat.mul_pos (by omega) (by omega)
  have hh : ((k+1:ℕ):ℝ)≠0 := by positivity
  have hmean := density_appt_uniform_mean_radius hmn hρ hP
  change |1/((D:ℝ)*b)-1|≤3/((k+1:ℕ):ℝ) at hmean
  have hsq : (1/((D:ℝ)*b)-1)^2≤(3/((k+1:ℕ):ℝ))^2 := by
    have hx:=pow_le_pow_left₀ (abs_nonneg (1/((D:ℝ)*b)-1)) hmean 2
    simpa only [sq_abs] using hx
  have hcap : (D:ℝ)/((k+1:ℕ):ℝ)^2≤C := by
    have hx : 4+(D:ℝ)/((k+1:ℕ):ℝ)^2≤C := le_max_right _ _
    linarith
  have hbound : (D:ℝ)*(1/((D:ℝ)*b)-1)^2≤9*C := by
    have h1:=mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg D)
    have he : (D:ℝ)*(3/((k+1:ℕ):ℝ))^2=9*((D:ℝ)/((k+1:ℕ):ℝ)^2) := by field_simp <;> ring
    rw [he] at h1
    linarith
  refine ⟨?_,hbound⟩
  have hquad:=spectrum_quadratic_centering hD f (ordered_eigenvalues_sum hρ.1.isHermitian hρ.2) b hb
  have hv:=density_appt_ordered_variance_bound (h:=k+1) (by omega) hmn hρ hP
  rw [pairedPivot_eq_paperPivot hmn] at hv
  have hv' : ((∑ i,(f i)^2)-1/(D:ℝ))/b^2≤C := (div_le_iff₀ (sq_pos_of_pos hb)).2 hv
  change (∑ i,(f i/b-1)^2)≤10*C
  linarith

/-- Uniform finite entropy remainder bound, still retaining the entire actual
head deficit. No reference to a fixed aspect ratio occurs in this theorem. -/
theorem density_appt_uniform_entropy_pivot_bound {k n : ℕ} (hmn : k+2≤n)
    {A : Matrix (Fin (k+2) × Fin n) (Fin (k+2) × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) (hP : APPT.Quantum.AbsolutelyPPT A)
    (hδ : entropyBulkRadius k<1) (hν : entropyUniformMeanRadius k<1) :
    vonNeumannDeficit hρ/hρ.1.isHermitian.eigenvalues₀ (paperPivot hmn)≤
      entropyVarianceCap k n/2*(1+10*entropyBulkRadius k/(1-entropyBulkRadius k)+
        10*entropyUniformMeanRadius k)-paperHeadDeficit hmn hρ := by
  let δ := entropyBulkRadius k
  let ν := entropyUniformMeanRadius k
  let C := entropyVarianceCap k n
  let D := Fintype.card (Fin (k+2) × Fin n)
  let f := hρ.1.isHermitian.eigenvalues₀
  let b := f (paperPivot hmn)
  have hδ0 : 0≤δ := Real.sqrt_nonneg _
  have hν0 : 0≤ν := by dsimp [ν,entropyUniformMeanRadius];positivity
  have hC0 : 0≤C := entropyVarianceCap_nonneg k n
  have hm:=density_appt_uniform_mean_radius hmn hρ hP
  have hr:=density_appt_full_entropy_taylor_bound hmn hρ hP δ ν hδ0 hδ hν0 hν
    (density_appt_entropy_bulk_smallness hmn hρ hP) hm
  obtain ⟨hQ,hM⟩:=density_appt_uniform_moment_budget hmn hρ hP
  have hM' : (D:ℝ)*(1/((D:ℝ)*b)-1)^2≤10*C := by change _≤9*C at hM;linarith
  have ha : 0≤δ/(2*(1-δ)) := by positivity
  have hb : 0≤ν/(2*(1+ν)) := by positivity
  have hb' : ν/(2*(1+ν))≤ν/2 := (div_le_iff₀ (by positivity : 0<2*(1+ν))).2 (by nlinarith)
  have H1:=mul_le_mul_of_nonneg_left hQ ha
  have H2:=mul_le_mul_of_nonneg_left hM' hb
  have H3:=mul_le_mul_of_nonneg_right hb' (show 0≤10*C by positivity)
  have hid : max 4 ((D:ℝ)/((k+1:ℕ):ℝ)^2)/2+2=C/2 := entropy_tail_cap_identity _
  have he : C/2+(δ/(2*(1-δ)))*(10*C)+(ν/2)*(10*C)=C/2*(1+10*δ/(1-δ)+10*ν) := by
    have hp : 1-δ≠0 := by linarith
    field_simp <;> ring
  dsimp only at hr
  change vonNeumannDeficit hρ/b≤C/2*(1+10*δ/(1-δ)+10*ν)-paperHeadDeficit hmn hρ
  change vonNeumannDeficit hρ/b≤max 4 ((D:ℝ)/((k+1:ℕ):ℝ)^2)/2+2-paperHeadDeficit hmn hρ+
    (δ/(2*(1-δ)))*(∑ i,(f i/b-1)^2)+(ν/(2*(1+ν)))*(D:ℝ)*(1/((D:ℝ)*b)-1)^2 at hr
  rw [hid] at hr
  nlinarith

end APPTReview
