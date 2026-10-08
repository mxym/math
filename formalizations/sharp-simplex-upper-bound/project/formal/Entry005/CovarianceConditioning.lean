import Entry005.DeterminantMoment
import Mathlib.Analysis.Matrix.Spectrum

/-! Directional first moments imply a quantitative covariance determinant bound.
The spectral decomposition used here is mathlib's kernel-checked theorem.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Entry005

variable {α : Type*} [MeasurableSpace α] {ν : Measure α} [IsProbabilityMeasure ν]

omit [IsProbabilityMeasure ν] in
theorem centered_dot_integral {d : ℕ} (X : α → Fin d → ℝ) (u : Fin d → ℝ)
    (hX : ∀ i, Integrable (fun x => X x i) ν)
    (hcenter : ∀ i, (∫ x, X x i ∂ν) = 0) :
    (∫ x, dotProduct u (X x) ∂ν) = 0 := by
  unfold dotProduct
  rw [integral_finsetSum _ fun i _ => (hX i).const_mul _]
  simp only [integral_const_mul, hcenter, mul_zero, Finset.sum_const_zero]

theorem covariance_direction_lower {d : ℕ} (X : α → Fin d → ℝ) (u : Fin d → ℝ)
    (hX : ∀ i, Integrable (fun x => X x i) ν)
    (hcenter : ∀ i, (∫ x, X x i ∂ν) = 0)
    (hpair : ∀ i j, Integrable (fun x => X x i * X x j) ν)
    {b : ℝ} (hb : 0 ≤ b)
    (hround : 2 * b ≤ negativeIntegral ν (fun x => dotProduct u (X x))) :
    16 * b ^ 2 ≤ dotProduct u ((secondMomentMatrix ν X).mulVec u) := by
  have hdot : Integrable (fun x => dotProduct u (X x)) ν :=
    integrable_finsetSum _ fun i _ => (hX i).const_mul _
  have hm := integral_mean_decomposition hdot
  rw [centered_dot_integral X u hX hcenter] at hm
  have hpos : positiveIntegral ν (fun x => dotProduct u (X x)) =
      negativeIntegral ν (fun x => dotProduct u (X x)) := by linarith
  have habs := integral_absolute_decomposition hdot
  rw [hpos] at habs
  have hfirst : 4 * b ≤ ∫ x, |dotProduct u (X x)| ∂ν := by linarith
  have hintabs : Integrable (fun x => |dotProduct u (X x)|) ν := by
    simpa only [Real.norm_eq_abs] using hdot.norm
  have hintsq : Integrable (fun x => |dotProduct u (X x)| ^ 2) ν := by
    simpa only [sq_abs] using dot_square_integrable X u hpair
  have hjensen := probability_integral_square_le hintabs hintsq
  simp only [sq_abs] at hjensen
  rw [integral_dot_square X u hpair] at hjensen
  nlinarith

omit [IsProbabilityMeasure ν] in
theorem second_moment_hermitian {d : ℕ} (X : α → Fin d → ℝ) :
    (secondMomentMatrix ν X).IsHermitian := by
  ext i j
  simp [Matrix.conjTranspose_apply, secondMomentMatrix, mul_comm]

theorem covariance_determinant_lower {d : ℕ} (X : α → Fin d → ℝ)
    (hX : ∀ i, Integrable (fun x => X x i) ν)
    (hcenter : ∀ i, (∫ x, X x i ∂ν) = 0)
    (hpair : ∀ i j, Integrable (fun x => X x i * X x j) ν)
    {b : ℝ} (hb : 0 ≤ b)
    (hround : ∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 →
      2 * b ≤ negativeIntegral ν (fun x => dotProduct u (X x))) :
    (16 * b ^ 2) ^ d ≤ (secondMomentMatrix ν X).det := by
  let hA := second_moment_hermitian X (ν := ν)
  have heig (i : Fin d) : 16 * b ^ 2 ≤ hA.eigenvalues i := by
    have hu : ‖hA.eigenvectorBasis i‖ = 1 := hA.eigenvectorBasis.orthonormal.norm_eq_one i
    have h := covariance_direction_lower X (hA.eigenvectorBasis i) hX hcenter hpair hb
      (hround _ hu)
    rw [hA.eigenvalues_eq]
    simpa using h
  rw [hA.det_eq_prod_eigenvalues]
  have hprod : (∏ _i : Fin d, (16 * b ^ 2 : ℝ)) ≤ ∏ i : Fin d, hA.eigenvalues i :=
    Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun i _ => heig i)
  simpa using hprod

theorem round_lifted_second_moment_lower {d : ℕ} (hd : 1 ≤ d)
    (X : α → Fin d → ℝ)
    (hX : ∀ i, Integrable (fun x => X x i) ν)
    (hcenter : ∀ i, (∫ x, X x i ∂ν) = 0)
    (hpair : ∀ i j, Integrable (fun x => X x i * X x j) ν)
    {b : ℝ} (hb : 0 ≤ b)
    (hround : ∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 →
      2 * b ≤ negativeIntegral ν (fun x => dotProduct u (X x))) :
    2 * (b ^ d) ^ 2 ≤ ∫ w : Fin (d + 1) → α,
      |liftedDeterminant (fun i => X (w i.succ)) (X (w 0))| ^ 2 ∂iidLaw ν (d + 1) := by
  rw [centered_lifted_determinant_second_moment X hX hcenter hpair]
  have hdet := covariance_determinant_lower X hX hcenter hpair hb hround
  have hfact : (2 : ℝ) ≤ ((d + 1).factorial : ℝ) := by
    have h := Nat.factorial_le (show 2 ≤ d + 1 by omega)
    norm_num at h ⊢
    exact_mod_cast h
  have hp : (b ^ d) ^ 2 ≤ (16 * b ^ 2) ^ d := by
    rw [← pow_mul, Nat.mul_comm d 2, pow_mul]
    exact pow_le_pow_left₀ (sq_nonneg b) (by nlinarith [sq_nonneg b]) d
  calc
    2 * (b ^ d) ^ 2 ≤ 2 * (16 * b ^ 2) ^ d := mul_le_mul_of_nonneg_left hp (by norm_num)
    _ ≤ ((d + 1).factorial : ℝ) * (16 * b ^ 2) ^ d :=
      mul_le_mul_of_nonneg_right hfact (by positivity)
    _ ≤ ((d + 1).factorial : ℝ) * (secondMomentMatrix ν X).det :=
      mul_le_mul_of_nonneg_left hdet (Nat.cast_nonneg _)

end Entry005
