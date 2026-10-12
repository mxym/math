import GaussianFour.TraceSupport
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! The actual centered four-coordinate trace slice, not a diagonal model. -/
open Matrix
namespace GaussianFour

noncomputable def fourCentering : Matrix (Fin 4) (Fin 4) ℝ :=
  1 - Matrix.of (fun _ _ => (1 / 4 : ℝ))

lemma fourCentering_hermitian : fourCentering.IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp [fourCentering, Matrix.one_apply, eq_comm]

lemma fourCentering_row_sum (i : Fin 4) : (∑ j, fourCentering i j) = 0 := by
  norm_num [fourCentering, Matrix.one_apply, Finset.sum_sub_distrib]

lemma fourCentering_trace : fourCentering.trace = 3 := by
  norm_num [fourCentering, Matrix.trace, Matrix.one_apply]

lemma centered_mul_fourCentering (A : Matrix (Fin 4) (Fin 4) ℝ)
    (hz : ∀ i, (∑ j, A i j) = 0) : A * fourCentering = A := by
  have hzero : A * Matrix.of (fun _ _ : Fin 4 => (1 / 4 : ℝ)) = 0 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
    rw [← Finset.sum_mul, hz, zero_mul]
  rw [fourCentering, Matrix.mul_sub, Matrix.mul_one, hzero, sub_zero]

lemma fourCentering_mulVec (x : Fin 4 → ℝ) (hx : ∑ i, x i = 0) :
    fourCentering *ᵥ x = x := by
  have hzero : Matrix.of (fun _ _ : Fin 4 => (1 / 4 : ℝ)) *ᵥ x = 0 := by
    ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
    rw [← Finset.mul_sum, hx, mul_zero]
  rw [fourCentering, Matrix.sub_mulVec, Matrix.one_mulVec, hzero, sub_zero]

/-- Vanishing against every centered trace-zero direction forces a centered
symmetric matrix to be scalar on the full three-dimensional centered space. -/
theorem centered_trace_stationary_eq_scalar
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : L.IsHermitian)
    (hz : ∀ i, (∑ j, L i j) = 0)
    (horth : ∀ D : Matrix (Fin 4) (Fin 4) ℝ,
      D.IsHermitian → (∀ i, (∑ j, D i j) = 0) → D.trace = 0 → (L*D).trace = 0) :
    L = (L.trace / 3) • fourCentering := by
  let μ : ℝ := L.trace / 3
  let D : Matrix (Fin 4) (Fin 4) ℝ := L - μ • fourCentering
  have hD : D.IsHermitian := hL.sub (fourCentering_hermitian.smul (by simp [IsSelfAdjoint]))
  have hzD : ∀ i, (∑ j, D i j) = 0 := by
    intro i
    simp only [D, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Finset.sum_sub_distrib, ← Finset.mul_sum, hz, fourCentering_row_sum,
      mul_zero, sub_zero]
  have htD : D.trace = 0 := by
    change (L - μ • fourCentering).trace = 0
    rw [Matrix.trace_sub, Matrix.trace_smul, fourCentering_trace]
    dsimp [μ]
    ring
  have hLD : (L*D).trace = 0 := horth D hD hzD htD
  have hPD : (fourCentering*D).trace = 0 := by
    rw [Matrix.trace_mul_comm, centered_mul_fourCentering D hzD, htD]
  have hDD : (D*Dᴴ).trace = 0 := by
    change ((L - μ • fourCentering)*Dᴴ).trace = 0
    rw [hD.eq, Matrix.sub_mul, Matrix.smul_mul, Matrix.trace_sub,
      Matrix.trace_smul, hLD, hPD]
    simp
  have he : D = 0 := Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp hDD
  exact sub_eq_zero.mp he

end GaussianFour
