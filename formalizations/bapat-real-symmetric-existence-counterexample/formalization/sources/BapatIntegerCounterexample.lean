import BapatRationalInterior
import Mathlib.LinearAlgebra.Matrix.Integer

set_option autoImplicit false
open BapatFiniteRank

namespace BapatRealExistence
noncomputable section

def realOfIntMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (A i j:ℝ)

theorem realOfInt_num {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    realOfIntMatrix A.num = (A.den:ℝ) • realOfRatMatrix A := by
  ext i j
  have h := (div_eq_iff (show (A.den:ℚ)≠0 by exact_mod_cast A.den_ne_zero)).mp (A.num_div_den i j)
  have hr := congrArg (fun q : ℚ => (q:ℝ)) h
  simpa [realOfIntMatrix,realOfRatMatrix,mul_comm] using hr

theorem exists_integer_posDef_negative_endpoint :
    ∃ (N : ℕ) (B : Matrix (Fin N) (Fin N) ℤ), 4<N ∧ (realOfIntMatrix B).PosDef ∧
      (qPolynomial (realOfIntMatrix B)).derivative.eval 1<0 := by
  obtain ⟨N,A,hN,hpd,hneg⟩ := exists_rational_posDef_negative_endpoint
  have hd : (0:ℝ)<A.den := by exact_mod_cast Nat.pos_of_ne_zero A.den_ne_zero
  refine ⟨N,A.num,hN,?_,?_⟩
  · rw [realOfInt_num]
    exact hpd.smul hd
  · rw [realOfInt_num]
    change (qPolynomial (fun i j => (A.den:ℝ)*realOfRatMatrix A i j)).derivative.eval 1<0
    rw [qPolynomial_derivative_scale]
    exact mul_neg_of_pos_of_neg (pow_pos hd N) hneg

/-- Complete integer, real symmetric, positive-definite Bapat counterexample
for the original inversion-weighted q-permanent, including rational positive
interior parameters and a strictly negative derivative at q=1. -/
theorem exists_integer_real_symmetric_counterexample :
    ∃ (N : ℕ) (B : Matrix (Fin N) (Fin N) ℤ), 4<N ∧ B.IsSymm ∧
      (realOfIntMatrix B).PosDef ∧ ¬B.IsDiag ∧
      (qPolynomial (realOfIntMatrix B)).derivative.eval 1<0 ∧
      ∃ q₀ q₁ : ℚ, 0<q₀ ∧ q₀<q₁ ∧ q₁<1 ∧
        BapatRankTwo.qPermanent (realOfIntMatrix B) (q₁:ℝ) <
          BapatRankTwo.qPermanent (realOfIntMatrix B) (q₀:ℝ) := by
  obtain ⟨N,B,hN,hpd,hneg⟩ := exists_integer_posDef_negative_endpoint
  have hsym : B.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    have h := hpd.isHermitian.isSymm.apply i j
    change (B j i:ℝ)=(B i j:ℝ) at h
    exact_mod_cast h
  have hnd : ¬B.IsDiag := by
    intro hd
    apply not_isDiag_of_negative_endpoint (realOfIntMatrix B) hneg
    intro i j hij
    change (B i j:ℝ)=0
    rw [hd hij,Int.cast_zero]
  obtain ⟨q₀,q₁,hq₀,hqq,hq₁,hdec⟩ := exists_rational_interior_decrease
    (qPolynomial (realOfIntMatrix B)) hneg
  refine ⟨N,B,hN,hsym,hpd,hnd,hneg,q₀,q₁,hq₀,hqq,hq₁,?_⟩
  simpa only [qPolynomial_eval] using hdec

end
end BapatRealExistence
