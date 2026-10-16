import SymmetricSupport.GaussianFrame
import SymmetricSupport.ExactEffect

open scoped BigOperators ComplexOrder
open Matrix MeasureTheory Set

namespace SymmetricSupport

noncomputable section

theorem ofReal_mul_re (r : ℝ) (z : ℂ) : ((r : ℂ) * z).re = r * z.re := by
  simp [Complex.mul_re]

theorem exists_unitVector_multiple_of_pos (D : ℕ) (hD : 0 < D) (z : Fin D → ℂ) :
    ∃ (c : ℂ) (u : Fin D → ℂ), IsUnitVector u ∧ z = c • u := by
  classical
  by_cases hz : z = 0
  · let u : Fin D → ℂ := Pi.single ⟨0, hD⟩ 1
    refine ⟨0, u, ?_, ?_⟩
    · simp [IsUnitVector, u, Pi.single_apply]
    · simp [hz]
  · exact exists_unitVector_multiple z hz

theorem purePowerDensity_smul (D k : ℕ) (c : ℂ) (z : Fin D → ℂ) :
    purePowerDensity D k (c • z) = (Complex.normSq c) ^ k • purePowerDensity D k z := by
  ext v w
  simp only [purePowerDensity, Matrix.vecMulVec_apply, purePower_smul,
    Pi.star_apply, Pi.smul_apply, smul_eq_mul, star_mul, star_pow,
    Matrix.smul_apply, Complex.real_smul, Complex.ofReal_pow]
  rw [← Complex.mul_conj c]
  simp only [Complex.star_def]
  ring

theorem pure_guarantee_homogeneous (D k : ℕ) (hD : 0 < D)
    (M : Matrix (Word D k) (Word D k) ℂ) (f : ℝ)
    (hf : ∀ z : Fin D → ℂ, IsUnitVector z →
      f ≤ (M * purePowerDensity D k z).trace.re) (z : Fin D → ℂ) :
    f * (purePowerDensity D k z).trace.re ≤ (M * purePowerDensity D k z).trace.re := by
  obtain ⟨c, u, hu, rfl⟩ := exists_unitVector_multiple_of_pos D hD z
  have h := mul_le_mul_of_nonneg_left (hf u hu) (pow_nonneg (Complex.normSq_nonneg c) k)
  simp only [purePowerDensity_smul, Matrix.mul_smul, Matrix.trace_smul,
    Complex.smul_re, smul_eq_mul, unitVector_trace D k u hu, Complex.one_re] at *
  nlinarith

theorem phaseRadialAverage_eq_real_average (D k L : ℕ) (x : Fin D → ℝ) :
    phaseRadialAverage D k L x =
      ((L ^ D : ℕ) : ℝ)⁻¹ •
        ∑ θ : Fin D → Fin L, purePowerDensity D k (phaseRadialVector D L x θ) := by
  ext v w
  simp [phaseRadialAverage, Matrix.smul_apply, Complex.real_smul]

theorem phaseRadialAverage_guarantee (D k L : ℕ) (hD : 0 < D)
    (M : Matrix (Word D k) (Word D k) ℂ) (f : ℝ)
    (hf : ∀ z : Fin D → ℂ, IsUnitVector z →
      f ≤ (M * purePowerDensity D k z).trace.re) (x : Fin D → ℝ) :
    f * (phaseRadialAverage D k L x).trace.re ≤ (M * phaseRadialAverage D k L x).trace.re := by
  have hs := Finset.sum_le_sum (s := Finset.univ)
    (fun (θ : Fin D → Fin L) _ => pure_guarantee_homogeneous D k hD M f hf
      (phaseRadialVector D L x θ))
  have h := mul_le_mul_of_nonneg_left hs
    (inv_nonneg.mpr (Nat.cast_nonneg (L ^ D) : (0 : ℝ) ≤ ((L ^ D : ℕ) : ℝ)))
  rw [phaseRadialAverage_eq_real_average]
  simp only [Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul,
    Matrix.trace_sum, Matrix.mul_sum, Complex.re_sum] at *
  rw [← Finset.mul_sum] at h
  nlinarith

theorem weighted_trace_expansion (D k L : ℕ) (M : Matrix (Word D k) (Word D k) ℂ)
    (x : Fin D → ℝ) :
    (radialWeight D x : ℂ) * (M * phaseRadialAverage D k L x).trace =
      ∑ v : Word D k, ∑ w : Word D k,
        M v w * ((radialWeight D x : ℂ) * phaseRadialAverage D k L x w v) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro w _
  ring

theorem weighted_trace_integrable (D k L : ℕ) (hL : k < L)
    (M : Matrix (Word D k) (Word D k) ℂ) :
    Integrable (fun x => (radialWeight D x : ℂ) * (M * phaseRadialAverage D k L x).trace)
      (radialMeasure D) := by
  simp_rw [weighted_trace_expansion]
  apply integrable_finsetSum
  intro v _
  apply integrable_finsetSum
  intro w _
  exact (phaseRadialAverage_weighted_integrable D k L hL w v).const_mul _

theorem weighted_trace_integral (D k L : ℕ) (hL : k < L)
    (M : Matrix (Word D k) (Word D k) ℂ) :
    (∫ x, (radialWeight D x : ℂ) * (M * phaseRadialAverage D k L x).trace ∂radialMeasure D) =
      (k.factorial : ℂ) * (M * symmetricProjector D k).trace := by
  simp_rw [weighted_trace_expansion]
  rw [integral_finsetSum Finset.univ (fun v _ =>
    integrable_finsetSum _ (fun w _ =>
      (phaseRadialAverage_weighted_integrable D k L hL w v).const_mul (M v w)))]
  simp_rw [integral_finsetSum Finset.univ (fun w _ =>
    (phaseRadialAverage_weighted_integrable D k L hL w _).const_mul (M _ w))]
  simp_rw [integral_const_mul, phaseRadialAverage_weighted_integral D k L hL]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro w _
  ring

theorem weighted_real_trace_integrable (D k L : ℕ) (hL : k < L)
    (M : Matrix (Word D k) (Word D k) ℂ) :
    Integrable (fun x => radialWeight D x * (M * phaseRadialAverage D k L x).trace.re)
      (radialMeasure D) := by
  simpa only [RCLike.re_eq_complex_re, ofReal_mul_re] using
    (weighted_trace_integrable D k L hL M).re

theorem weighted_real_trace_integral (D k L : ℕ) (hL : k < L)
    (M : Matrix (Word D k) (Word D k) ℂ) :
    (∫ x, radialWeight D x * (M * phaseRadialAverage D k L x).trace.re ∂radialMeasure D) =
      (k.factorial : ℝ) * (M * symmetricProjector D k).trace.re := by
  have h := congrArg Complex.re (weighted_trace_integral D k L hL M)
  have hre := integral_re (weighted_trace_integrable D k L hL M)
  simp only [RCLike.re_eq_complex_re] at hre
  rw [← hre] at h
  simp only [ofReal_mul_re] at h
  simpa only [Complex.natCast_re, Complex.natCast_im, mul_zero,
    zero_mul, sub_zero, Complex.mul_re] using h

/-- A worst-case guarantee on all normalized pure iid inputs cannot exceed the
normalized symmetric-state value. This is established by explicit positive radial
integration and finite phases; no caller supplies a Haar or design identity. -/
theorem pure_guarantee_le_symmetricState (D k : ℕ) (hD : 0 < D)
    (M : Matrix (Word D k) (Word D k) ℂ) (f : ℝ)
    (hf : ∀ z : Fin D → ℂ, IsUnitVector z →
      f ≤ (M * purePowerDensity D k z).trace.re) :
    f ≤ (M * symmetricState D k).trace.re := by
  let L := k + 1
  have hL : k < L := Nat.lt_succ_self k
  have hpoint : ∀ x : Fin D → ℝ,
      f * (radialWeight D x * (1 * phaseRadialAverage D k L x).trace.re) ≤
        radialWeight D x * (M * phaseRadialAverage D k L x).trace.re := by
    intro x
    have h := mul_le_mul_of_nonneg_left (phaseRadialAverage_guarantee D k L hD M f hf x)
      (Finset.prod_nonneg (s := Finset.univ) (fun d _ => (Real.exp_pos (-x d)).le))
    simpa only [Matrix.one_mul, radialWeight, mul_left_comm] using h
  have hint := integral_mono
    ((weighted_real_trace_integrable D k L hL 1).const_mul f)
    (weighted_real_trace_integrable D k L hL M) hpoint
  rw [integral_const_mul, weighted_real_trace_integral D k L hL 1,
    weighted_real_trace_integral D k L hL M,
    Matrix.one_mul, symmetricProjector_trace] at hint
  simp only [Complex.natCast_re] at hint
  have hfpos : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hrpos : (0 : ℝ) < (Fintype.card (Sym (Fin D) k) : ℝ) := by
    exact_mod_cast occupation_card_pos D k hD
  have hmain : f * (Fintype.card (Sym (Fin D) k) : ℝ) ≤
      (M * symmetricProjector D k).trace.re := by nlinarith [hint]
  simp only [symmetricState, Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul]
  rw [mul_comm, ← div_eq_mul_inv]
  exact (le_div_iff₀ hrpos).mpr hmain

end
end SymmetricSupport
