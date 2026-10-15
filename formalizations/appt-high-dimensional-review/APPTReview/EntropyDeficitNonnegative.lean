import APPTReview.FullEntropyBound

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

/-- The exact logarithmic kernel is nonnegative on its full spectral domain,
including a zero eigenvalue. -/
theorem entropyKernel_nonnegative_domain {x : ℝ} (hx : -1≤x) : 0≤entropyKernel x := by
  by_cases hz : 1+x=0
  · have he : x=-1 := by linarith
    rw [he];norm_num [entropyKernel]
  have hp : 0<1+x := lt_of_le_of_ne (by linarith) (Ne.symm hz)
  have hl:=mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hp) hp.le
  have he : (1+x)*(1-(1+x)⁻¹)=x := by field_simp <;> ring
  rw [he] at hl
  unfold entropyKernel
  linarith

/-- Nonnegativity of the actual von Neumann entropy deficit, with trace one
and every possible zero eigenvalue retained. APPT is not required. -/
theorem density_vonNeumannDeficit_nonnegative {m n : ℕ} (hm : 0<m) (hn : 0<n)
    {A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) : 0≤vonNeumannDeficit hρ := by
  let D := Fintype.card (Fin m × Fin n)
  let f := hρ.1.isHermitian.eigenvalues₀
  have hDN : 0<D := by dsimp [D];simpa using Nat.mul_pos hm hn
  have hD : (0:ℝ)<D := by exact_mod_cast hDN
  have hb : (0:ℝ)<1/(D:ℝ) := by positivity
  have hf (i) : 0≤f i := by
    have hh:=hρ.1.eigenvalues_nonneg (spectralLabel _ i)
    simpa only [eigenvalues_spectralLabel] using hh
  have he:=spectrum_entropy_centering hDN f hf (ordered_eigenvalues_sum hρ.1.isHermitian hρ.2) (1/(D:ℝ)) hb
  have hz : 1/((D:ℝ)*(1/(D:ℝ)))-1=0 := by field_simp <;> ring
  have hk : entropyKernel 0=0 := by norm_num [entropyKernel]
  rw [hz,hk,mul_zero,sub_zero] at he
  have hs : 0≤∑ i,entropyKernel (f i/(1/(D:ℝ))-1) := by
    apply Finset.sum_nonneg
    intro i _
    apply entropyKernel_nonnegative_domain
    have hi:=div_nonneg (hf i) hb.le
    linarith
  rw [← he] at hs
  have hpos := (le_div_iff₀ hb).mp hs
  simp only [zero_mul] at hpos
  simpa only [vonNeumannDeficit,spectralVonNeumannEntropy,sub_neg_eq_add] using hpos

end APPTReview
