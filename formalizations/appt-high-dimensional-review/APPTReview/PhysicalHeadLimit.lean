import APPTReview.PhysicalHeadStability
import Mathlib.Topology.MetricSpace.Pseudo.Defs

open scoped BigOperators ComplexOrder Topology
open Matrix Filter
namespace APPTReview

/-- A sufficiently small head deficit excludes zero eigenvalues quantitatively. -/
theorem density_appt_head_positive_spectrum {k n : ℕ} (hmn : k+2 ≤ n)
    {A : Matrix (Fin (k+2) × Fin n) (Fin (k+2) × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) (hP : APPT.Quantum.AbsolutelyPPT A)
    (hsmall : paperHeadDeficit hmn hρ ≤ 1/144) :
    ∀ i, 0 < hρ.1.isHermitian.eigenvalues₀ i := by
  have hb := paper_head_pivot_positive hmn hρ hP
  have hq := (density_appt_paper_head_stability hmn hρ hP).2.2
  have hy : paperHeadBeta hmn hρ 0 ≤ 1/2 := by linarith
  intro i
  have hl := (paper_head_entire_interval hmn hρ hP i).1
  have hpos : 0 < hρ.1.isHermitian.eigenvalues₀ (paperPivot hmn)*(1-paperHeadBeta hmn hρ 0) :=
    mul_pos hb (by linarith)
  exact hpos.trans_le hl

/-- Uniform spectral flatness under head saturation, with genuinely varying
matrix dimensions. No flatness, eigenvalue convergence, or dimension-dependent
Schmidt decomposition is supplied as a hypothesis. This concerns saturation of
the finite entropy HEAD, not yet extremality of the full von Neumann entropy. -/
theorem appt_entropy_head_saturation_flat (k n : ℕ → ℕ)
    (A : (j : ℕ) → Matrix (Fin (k j+2) × Fin (n j)) (Fin (k j+2) × Fin (n j)) ℂ)
    (hmn : ∀ j, k j+2 ≤ n j)
    (hρ : ∀ j, APPT.Quantum.IsDensity (A j))
    (hP : ∀ j, APPT.Quantum.AbsolutelyPPT (A j))
    (hhead : Tendsto (fun j => paperHeadDeficit (hmn j) (hρ j)) atTop (𝓝 (0:ℝ))) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop,
      ∀ i, |(Fintype.card (Fin (k j+2) × Fin (n j)):ℝ)*(hρ j).1.isHermitian.eigenvalues₀ i-1| < ε := by
  intro ε hε
  let η : ℝ := min (1/144) (ε^3/11904)
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hnear := (tendsto_order.mp hhead).2 η hη
  filter_upwards [hnear] with j hj
  have hsmall : paperHeadDeficit (hmn j) (hρ j) ≤ 1/144 := hj.le.trans (min_le_left _ _)
  have htol : 11904*paperHeadDeficit (hmn j) (hρ j) < ε^3 := by
    have ht := hj.trans_le (min_le_right (1/144:ℝ) (ε^3/11904))
    have hc := (lt_div_iff₀ (by norm_num : (0:ℝ) < 11904)).mp ht
    nlinarith only [hc]
  intro i
  exact nonnegative_lt_of_cube_lt (abs_nonneg _) hε
    ((density_appt_head_spectral_cubic (hmn j) (hρ j) (hP j) hsmall i).trans_lt htol)

end APPTReview
