import Extraction
import APPTReview.SchmidtJointWitness

open scoped BigOperators ComplexOrder
open Matrix
namespace ExtractionLocalCap

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- A real two-sided order interval is preserved by an actual contraction. -/
theorem compression_order_interval (X : Matrix ι ι ℂ) (L : Matrix ι κ ℂ)
    (c : ℝ) (hc : 0 ≤ c) (hL : (1 - L * Lᴴ).PosSemidef)
    (hlo : (c • (1 : Matrix ι ι ℂ) + X).PosSemidef)
    (hhi : (c • (1 : Matrix ι ι ℂ) - X).PosSemidef) :
    (c • (1 : Matrix κ κ ℂ) + Lᴴ * X * L).PosSemidef ∧
    (c • (1 : Matrix κ κ ℂ) - Lᴴ * X * L).PosSemidef := by
  have hs : (1 - Lᴴ * L).PosSemidef := by
    have h := APPT.Quantum.one_sub_mul_conjTranspose_posSemidef Lᴴ
      (by simpa only [Matrix.conjTranspose_conjTranspose] using hL)
    simpa only [Matrix.conjTranspose_conjTranspose] using h
  constructor
  · have h := (hlo.conjTranspose_mul_mul_same L).add (hs.smul hc)
    convert h using 1
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, Matrix.one_mul, smul_sub]
    module
  · have h := (hhi.conjTranspose_mul_mul_same L).add (hs.smul hc)
    convert h using 1
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, Matrix.one_mul, smul_sub]
    module

/-- Real diagonal entries of an actual Hermitian order interval lie in [-c,c]. -/
theorem order_interval_diagonal (B : Matrix κ κ ℂ) (c : ℝ)
    (hlo : (c • (1 : Matrix κ κ ℂ) + B).PosSemidef)
    (hhi : (c • (1 : Matrix κ κ ℂ) - B).PosSemidef) (i : κ) :
    -c ≤ (B i i).re ∧ (B i i).re ≤ c := by
  have hl : 0 ≤ ((c • (1 : Matrix κ κ ℂ) + B) i i).re :=
    (RCLike.nonneg_iff.mp (hlo.diag_nonneg (i := i))).1
  have hh : 0 ≤ ((c • (1 : Matrix κ κ ℂ) - B) i i).re :=
    (RCLike.nonneg_iff.mp (hhi.diag_nonneg (i := i))).1
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    ite_true, Complex.add_re, Complex.sub_re, Complex.smul_re, Complex.one_re,
    smul_eq_mul, mul_one] at hl hh
  constructor <;> linarith

/-- A signed real diagonal is paired against the actual compressed matrix.
The bound depends on its full absolute mass, including negative entries. -/
theorem trace_signed_congruence_le (X : Matrix ι ι ℂ) (L : Matrix ι κ ℂ)
    (d : κ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hL : (1 - L * Lᴴ).PosSemidef)
    (hlo : (c • (1 : Matrix ι ι ℂ) + X).PosSemidef)
    (hhi : (c • (1 : Matrix ι ι ℂ) - X).PosSemidef) :
    (X * (L * Matrix.diagonal (fun i => (d i : ℂ)) * Lᴴ)).trace.re ≤
      c * ∑ i, |d i| := by
  obtain ⟨hl, hh⟩ := compression_order_interval X L c hc hL hlo hhi
  have hi (i : κ) : ((Lᴴ * X * L) i i).re * d i ≤ c * |d i| := by
    obtain ⟨hblo, hbhi⟩ := order_interval_diagonal _ c hl hh i
    rcases le_total 0 (d i) with hd | hd
    · rw [abs_of_nonneg hd]
      exact mul_le_mul_of_nonneg_right hbhi hd
    · rw [abs_of_nonpos hd]
      have h := mul_le_mul_of_nonpos_right hblo hd
      nlinarith
  rw [Extraction.trace_congruence_diagonal]
  simpa only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, Finset.mul_sum] using
      Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)

end ExtractionLocalCap
