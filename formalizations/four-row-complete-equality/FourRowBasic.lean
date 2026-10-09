import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-! Actual complex two-row energies for the four-row sharp tradeoff.
Copyright (c) 2026 Yongxian Zhang. All rights reserved.
AI-assisted research; no external funding. -/

open scoped BigOperators ComplexConjugate
namespace FourRowTradeoff
noncomputable section

abbrev Row := Fin 4 → ℂ
abbrev Mat := Matrix (Fin 4) (Fin 4) ℂ

def rowSq (a : Row) : ℝ := ∑ i, Complex.normSq (a i)
def symPair (a b : Row) : Fin 6 → ℂ :=
  ![a 0*b 1+a 1*b 0, a 0*b 2+a 2*b 0, a 0*b 3+a 3*b 0,
    a 1*b 2+a 2*b 1, a 1*b 3+a 3*b 1, a 2*b 3+a 3*b 2]
def altPair (a b : Row) : Fin 6 → ℂ :=
  ![a 0*b 1-a 1*b 0, a 0*b 2-a 2*b 0, a 0*b 3-a 3*b 0,
    a 1*b 2-a 2*b 1, a 1*b 3-a 3*b 1, a 2*b 3-a 3*b 2]
def symEnergy (a b : Row) : ℝ := ∑ i, Complex.normSq (symPair a b i)
def altEnergy (a b : Row) : ℝ := ∑ i, Complex.normSq (altPair a b i)
def overlap (a b : Row) : ℝ := Complex.normSq (∑ i, a i * conj (b i))
def collision (a b : Row) : ℝ := ∑ i, Complex.normSq (a i)*Complex.normSq (b i)
def sharpConstant (c : ℝ) : ℝ := max (3/2) (1+c)

theorem normSq_as_sq (z : ℂ) : Complex.normSq z = ‖z‖^2 := by
  simpa using (Complex.sq_norm z).symm

theorem norm_sum_mul_sq_le {ι : Type*} [Fintype ι] (a b : ι → ℂ) :
    ‖∑ i, a i * b i‖^2 ≤ (∑ i, ‖a i‖^2) * (∑ i, ‖b i‖^2) := by
  classical
  have h : ‖∑ i, a i*b i‖ ≤ ∑ i, ‖a i‖*‖b i‖ := by
    simpa only [Complex.norm_mul] using (norm_sum_le (s := Finset.univ) (fun i => a i*b i))
  have hn : 0 ≤ ∑ i, ‖a i‖*‖b i‖ :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hsq : ‖∑ i, a i*b i‖^2 ≤ (∑ i, ‖a i‖*‖b i‖)^2 := by
    nlinarith [norm_nonneg (∑ i, a i*b i)]
  exact hsq.trans (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖a i‖) (fun i => ‖b i‖))

theorem rowSq_nonneg (a : Row) : 0 ≤ rowSq a := by
  exact Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg _)
theorem symEnergy_nonneg (a b : Row) : 0 ≤ symEnergy a b := by
  exact Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg _)
theorem altEnergy_nonneg (a b : Row) : 0 ≤ altEnergy a b := by
  exact Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg _)
theorem overlap_nonneg (a b : Row) : 0 ≤ overlap a b := Complex.normSq_nonneg _
theorem collision_nonneg (a b : Row) : 0 ≤ collision a b := by
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))

theorem overlap_le_product (a b : Row) : overlap a b ≤ rowSq a * rowSq b := by
  have h := norm_sum_mul_sq_le a (fun i => conj (b i))
  simpa only [overlap, rowSq, normSq_as_sq, Complex.norm_conj] using h

theorem overlap_le_four_collision (a b : Row) : overlap a b ≤ 4*collision a b := by
  have h := norm_sum_mul_sq_le (fun i : Fin 4 => a i * conj (b i)) (fun _ => (1 : ℂ))
  simp only [mul_one, norm_one, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, Complex.norm_mul, Complex.norm_conj, mul_pow] at h
  simpa [overlap, collision, normSq_as_sq, mul_comm] using h

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
theorem symEnergy_identity (a b : Row) :
    symEnergy a b = rowSq a*rowSq b + overlap a b - 2*collision a b := by
  simp [symEnergy, symPair, rowSq, overlap, collision, Fin.sum_univ_succ,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.conj_re, Complex.conj_im]
  ring

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
theorem altEnergy_identity (a b : Row) :
    altEnergy a b = rowSq a*rowSq b - overlap a b := by
  simp [altEnergy, altPair, rowSq, overlap, Fin.sum_univ_succ,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.conj_re, Complex.conj_im]
  ring

theorem sharpConstant_nonneg (c : ℝ) : 0 ≤ sharpConstant c := by
  have h : (3/2 : ℝ) ≤ sharpConstant c := le_max_left _ _
  linarith

/-- The sharp two-row analytic estimate; no normalization or nonzero-row premise. -/
theorem pair_bound (a b : Row) (c : ℝ) :
    symEnergy a b + c*altEnergy a b ≤ sharpConstant c * (rowSq a*rowSq b) := by
  rw [symEnergy_identity, altEnergy_identity]
  have he0 := overlap_nonneg a b
  have he1 := overlap_le_product a b
  have ht := overlap_le_four_collision a b
  have huv : 0 ≤ rowSq a*rowSq b := mul_nonneg (rowSq_nonneg a) (rowSq_nonneg b)
  by_cases hc : c ≤ 1/2
  · have hm : sharpConstant c = 3/2 := max_eq_left (by linarith)
    rw [hm]
    have h := mul_le_mul_of_nonneg_left he1 (show 0 ≤ 1/2-c by linarith)
    nlinarith
  · have hm : sharpConstant c = 1+c := max_eq_right (by linarith)
    rw [hm]
    have h := mul_nonpos_of_nonpos_of_nonneg (show 1/2-c ≤ 0 by linarith) he0
    nlinarith

#print axioms pair_bound
end
end FourRowTradeoff
