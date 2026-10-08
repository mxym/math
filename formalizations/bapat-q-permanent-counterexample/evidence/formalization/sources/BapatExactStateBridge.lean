import BapatExactCoefficients
import BapatWedgeRecurrence

set_option autoImplicit false

namespace BapatRankTwo.Exact

/-- Both integer coefficient lists follow the proved polynomial recurrences,
with no bound or nonvanishing hypothesis on the input vectors. -/
theorem interpret_state (v : ℕ → GI × GI) (n : ℕ) :
    interpret (state v n).1 =
        FSeq (fun i => toComplex (v i).1) (fun i => toComplex (v i).2) n ∧
      interpret (state v n).2 =
        SSeq (fun i => toComplex (v i).1) (fun i => toComplex (v i).2) n := by
  induction n with
  | zero => simp [state, interpret, FSeq, SSeq]
  | succ n ih =>
      constructor
      · simp only [state, interpret_mulLinear, FSeq, linearFactor]
        rw [ih.1]
      · simp only [state, interpret_sStep, SSeq, linearFactor]
        rw [ih.1, ih.2]

theorem interpret_state_f (v : ℕ → GI × GI) (n : ℕ) :
    interpret (state v n).1 = BapatFischer.twoColorProduct
      (fun i : Fin n => toComplex (v i.val).1)
      (fun i : Fin n => toComplex (v i.val).2) :=
  (interpret_state v n).1.trans (FSeq_eq_twoColorProduct _ _ n)

theorem interpret_state_s (v : ℕ → GI × GI) (n : ℕ) :
    interpret (state v n).2 = wedgePolynomial
      (fun i : Fin n => toComplex (v i.val).1)
      (fun i : Fin n => toComplex (v i.val).2) :=
  (interpret_state v n).2.trans (SSeq_eq_wedgePolynomial _ _ n)

/-- The exact integer norm pair is already the norm pair of the original
full-product F and ordered wedge sum S. -/
theorem fischerInt_state_f (v : ℕ → GI × GI) (n : ℕ) :
    (fischerInt n (state v n).1 : ℝ) =
      BapatFischer.fischerNormSq n (BapatFischer.twoColorProduct
        (fun i : Fin n => toComplex (v i.val).1)
        (fun i : Fin n => toComplex (v i.val).2)) := by
  rw [fischerInt_correct, interpret_state_f]

theorem fischerInt_state_s (v : ℕ → GI × GI) (n : ℕ) :
    (fischerInt (n - 2) (state v n).2 : ℝ) =
      BapatFischer.fischerNormSq (n - 2) (wedgePolynomial
        (fun i : Fin n => toComplex (v i.val).1)
        (fun i : Fin n => toComplex (v i.val).2)) := by
  rw [fischerInt_correct, interpret_state_s]

/-- A positive exact integer gap forces the actual all-permutation
q-permanent's real polynomial to have negative derivative at q=1. -/
theorem derivative_negative_of_gap (v : ℕ → GI × GI) (n : ℕ)
    (hgap : 0 < fischerInt (n - 2) (state v n).2 -
      (n.choose 2 : ℤ) * fischerInt n (state v n).1) :
    (realQPolynomial (gram
      (fun i : Fin n => toComplex (v i.val).1)
      (fun i : Fin n => toComplex (v i.val).2))).derivative.eval 1 < 0 := by
  have hreal : 0 < (fischerInt (n - 2) (state v n).2 : ℝ) -
      (n.choose 2 : ℝ) * (fischerInt n (state v n).1 : ℝ) := by
    exact_mod_cast hgap
  rw [fischerInt_state_s, fischerInt_state_f] at hreal
  have hid := realQPolynomial_derivative_fischer
    (fun i : Fin n => toComplex (v i.val).1)
    (fun i : Fin n => toComplex (v i.val).2)
  linarith

end BapatRankTwo.Exact
