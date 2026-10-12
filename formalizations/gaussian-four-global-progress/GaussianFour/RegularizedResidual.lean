import GaussianFour.NormalCone
import Mathlib.Tactic.Ring

/-! Exact residual identity and bound on the intrinsic three-dimensional
covariance slice. This module does not assume a numerical spectral certificate. -/
open Matrix
open scoped MatrixOrder
namespace GaussianFour

/-- The regularized Gram identity and genuine complementarity imply the exact
squared Frobenius residual formula. -/
theorem regularized_residual_trace_identity {m : Type*} [Fintype m]
    (Q L : Matrix (Fin 3) (Fin 3) ℝ) (M : Matrix (Fin 3) m ℝ) (μ ε : ℝ)
    (hL : L.IsHermitian) (hcomp : (L - μ • 1) * Q = 0)
    (hgram : M * Mᴴ = (1 - ε) • Q + (ε / 3) • 1) :
    ((L * M - μ • M) * (L * M - μ • M)ᴴ).trace =
      (ε / 3) * ((L - μ • 1) * (L - μ • 1)).trace := by
  let R : Matrix (Fin 3) (Fin 3) ℝ := L - μ • 1
  have hR : R.IsHermitian := hL.sub (isHermitian_one.smul (show IsSelfAdjoint μ from rfl))
  have hr : L * M - μ • M = R * M := by
    simp only [R, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul]
  rw [hr, conjTranspose_mul, hR.eq, Matrix.mul_assoc,
    ← Matrix.mul_assoc M Mᴴ R, hgram]
  have hc : R * Q = 0 := hcomp
  have he : R * (((1 - ε) • Q + (ε / 3) • 1) * R) =
      (ε / 3) • (R * R) := by
    rw [← Matrix.mul_assoc, mul_add, Matrix.mul_smul, Matrix.mul_smul,
      hc, smul_zero, zero_add, mul_one, smul_mul]
  rw [he, trace_smul, smul_eq_mul]

/-- The residual spectrum estimate follows from PSD trace pairings, with no
chosen eigenbasis and no commutation assumption between the covariance and L. -/
theorem three_dimensional_slack_trace_bound (L : Matrix (Fin 3) (Fin 3) ℝ) (μ : ℝ)
    (hL : L.PosSemidef) (hμ : 0 ≤ μ) (hslack : (μ • 1 - L).PosSemidef) :
    ((L - μ • 1) * (L - μ • 1)).trace ≤ 3 * μ ^ 2 := by
  have hp := trace_psd_mul_nonneg hL hslack
  rw [mul_sub, Matrix.mul_smul, mul_one, trace_sub, trace_smul, smul_eq_mul] at hp
  have ht := hL.trace_nonneg
  have he : ((L - μ • 1) * (L - μ • 1)).trace =
      (L * L).trace - 2 * μ * L.trace + 3 * μ ^ 2 := by
    rw [mul_sub, sub_mul, sub_mul, Matrix.mul_smul, Matrix.mul_smul,
      smul_mul, mul_one, one_mul, smul_mul, mul_one,
      trace_sub, trace_sub, trace_sub]
    simp only [trace_smul, smul_eq_mul, trace_one, Fintype.card_fin, Nat.cast_ofNat]
    ring
  rw [he]
  nlinarith [mul_nonneg hμ ht]

/-- Normal-cone criticality implies the manuscript's residual estimate for an
actual Gram factor, including non-diagonal singular covariance matrices. -/
theorem upperNormal_regularized_residual_bound {m : Type*} [Fintype m]
    (Q L : Matrix (Fin 3) (Fin 3) ℝ) (M : Matrix (Fin 3) m ℝ) (ε : ℝ)
    (hQ : Q.PosSemidef) (htrace : Q.trace = 1) (hL : L.PosSemidef)
    (hnormal : IsTraceOneUpperNormal Q L) (hε : 0 ≤ ε)
    (hgram : M * Mᴴ = (1 - ε) • Q + (ε / 3) • 1) :
    ((L * M - (L * Q).trace • M) * (L * M - (L * Q).trace • M)ᴴ).trace ≤
      ε * (L * Q).trace ^ 2 := by
  obtain ⟨hs, hp⟩ := (upperNormal_iff_slack_and_product hQ htrace hL.isHermitian).mp hnormal
  have hc : (L - (L * Q).trace • 1) * Q = 0 := by
    rw [sub_mul, smul_mul, one_mul]
    exact sub_eq_zero.mpr hp
  rw [regularized_residual_trace_identity Q L M (L * Q).trace ε hL.isHermitian hc hgram]
  have hb := three_dimensional_slack_trace_bound L (L * Q).trace hL
    (trace_psd_mul_nonneg hL hQ) hs
  have hh := mul_le_mul_of_nonneg_left hb (div_nonneg hε (by norm_num : (0 : ℝ) ≤ 3))
  nlinarith

end GaussianFour
