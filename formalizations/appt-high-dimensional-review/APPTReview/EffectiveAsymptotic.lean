import APPTReview.EffectiveState
import APPTReview.CompactMaximum

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

/-- A rational, explicit approximation rate for the construction parameter. -/
theorem effective_ratio_error (h ε : ℝ) (hh : 0<h) (hε : 0<ε) (hsize : 4/ε≤h) :
    1-ε≤(h/(h+2))^2 := by
  have hp : 0<h+2 := by linarith
  have hs : 4≤h*ε := (div_le_iff₀ hε).mp hsize
  have ht := mul_le_mul_of_nonneg_right hs hp.le
  rw [div_pow]
  apply (le_div_iff₀ (sq_pos_of_pos hp)).2
  nlinarith

/-- Every sufficiently large smaller dimension admits an actual APPT density
with the whole spike-plus-broad-plateau coefficient, uniformly in the other dimension. -/
theorem appt_growing_branch_lower (ε : ℝ) (hε : 0<ε) :
    ∃ M : ℕ, ∀ (m n : ℕ), M≤m → m≤n →
      ∃ A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ,
        APPT.Quantum.IsDensity A ∧ APPT.Quantum.AbsolutelyPPT A ∧
        (1-ε)*(4+(n:ℝ)/m) ≤ ((m:ℝ)*n)^2*(APPT.Quantum.purity A-1/((m:ℝ)*n)) := by
  obtain ⟨h,hh⟩ := exists_nat_gt (max (1:ℝ) (4/ε))
  have hhR : (1:ℝ)≤h := (le_max_left _ _).trans hh.le
  have hhN : 1≤h := by exact_mod_cast hhR
  have herr := effective_ratio_error (h:ℝ) ε (by linarith) hε ((le_max_right _ _).trans hh.le)
  refine ⟨max 2 (2*h^2+4*h),?_⟩
  intro m n hm hmn
  have hm2 : 2≤m := (le_max_left _ _).trans hm
  have hsize : 2*h^2+4*h≤m := (le_max_right _ _).trans hm
  obtain ⟨A,hd,ha,hlo⟩ := exists_effective_lower hm2 hmn hhN hsize
  refine ⟨A,hd,ha,?_⟩
  exact (mul_le_mul_of_nonneg_right herr (by positivity : (0:ℝ)≤4+(n:ℝ)/m)).trans hlo

/-- A physical projection-state lower estimate usable also when m remains fixed. -/
theorem exists_projection_excess_lower {m n : ℕ} (hm : 2≤m) (hmn : m≤n) :
    ∃ A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ,
      APPT.Quantum.IsDensity A ∧ APPT.Quantum.AbsolutelyPPT A ∧
      ((m:ℝ)*n)/((m:ℝ)^2-1)-(m:ℝ)/n ≤
        ((m:ℝ)*n)^2*(APPT.Quantum.purity A-1/((m:ℝ)*n)) := by
  obtain ⟨A,hd,ha,hlo,hhi⟩ := exists_appt_fixed_local_lower hm hmn
  refine ⟨A,hd,ha,?_⟩
  have hmP : (0:ℝ)<m := by exact_mod_cast (show 0<m by omega)
  have hnP : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hden : (0:ℝ)<(m:ℝ)^2-1 := by
    have hh : (2:ℝ)≤m := by exact_mod_cast hm
    nlinarith
  have hx := mul_le_mul_of_nonneg_left (sub_le_sub_right hlo 1) (mul_pos hmP hnP).le
  have hleft : ((m:ℝ)*n)*((m:ℝ)^2/((m:ℝ)^2-1)-1/(n:ℝ)^2-1)=
      ((m:ℝ)*n)/((m:ℝ)^2-1)-(m:ℝ)/n := by field_simp <;> ring
  have hright : ((m:ℝ)*n)*(((m:ℝ)*n)*APPT.Quantum.purity A-1)=
      ((m:ℝ)*n)^2*(APPT.Quantum.purity A-1/((m:ℝ)*n)) := by field_simp <;> ring
  rwa [hleft,hright] at hx

/-- Exact conversion between the growing-m and all-dimension branch coefficients. -/
theorem branch_coefficient_identity (m D : ℝ) (hm : m≠0) (hden : m^2-1≠0) :
    4+D/m^2=(1-1/m^2)*(4+D/(m^2-1))+4/m^2 := by
  field_simp
  ring

end APPTReview
