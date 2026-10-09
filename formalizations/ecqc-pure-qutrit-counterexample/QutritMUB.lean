import QutritState

open scoped BigOperators ComplexConjugate
open Matrix

namespace ECQC.Qutrit

noncomputable def omega : ℂ := ⟨-1/2, Real.sqrt 3 / 2⟩

/-- Exact normalized entries. Writing real and imaginary parts explicitly avoids
repeated expansion of nested complex inverses in the algebraic certificates. -/
noncomputable def alpha : ℂ := ⟨Real.sqrt 3 / 3, 0⟩
noncomputable def beta : ℂ := ⟨-Real.sqrt 3 / 6, 1/2⟩

/-- The computational basis and the three normalized quadratic Fourier bases.
Columns, not rows, are the measurement outcome vectors. -/
noncomputable def basis : Fin 4 → Matrix Q Q ℂ :=
  ![1,
    !![alpha,alpha,alpha; alpha,beta,conj beta; alpha,conj beta,beta],
    !![alpha,alpha,alpha; beta,conj beta,alpha; beta,alpha,conj beta],
    !![alpha,alpha,alpha; conj beta,alpha,beta; conj beta,beta,alpha]]

theorem sqrt3_sq : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
theorem sqrt3_pow3 : (Real.sqrt 3)^3 = 3 * Real.sqrt 3 := by
  calc _ = (Real.sqrt 3)^2 * Real.sqrt 3 := by ring
       _ = _ := by rw [sqrt3_sq]
theorem sqrt3_pow4 : (Real.sqrt 3)^4 = 9 := by
  calc _ = ((Real.sqrt 3)^2)^2 := by ring
       _ = _ := by rw [sqrt3_sq]; norm_num

macro "qutrit_arith" : tactic => `(tactic|
  (norm_num [map_ofNat, basis, alpha, beta, omega, Matrix.one_apply,
     Fin.sum_univ_succ, Complex.normSq_apply,
     Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
     Complex.conj_re, Complex.conj_im]
   <;> ring_nf
   <;> norm_num [sqrt3_sq, sqrt3_pow3, sqrt3_pow4]))

/-- Link to the canonical root-of-unity description in the manuscript. -/
theorem alpha_mul_omega : alpha * omega = beta := by
  apply Complex.ext <;> qutrit_arith

set_option maxHeartbeats 1000000 in
/-- Each displayed matrix has orthonormal columns. -/
theorem basis_orthonormal (a : Fin 4) : (basis a)ᴴ * basis a = 1 := by
  ext i j
  change (∑ x : Q, conj (basis a x i) * basis a x j) = if i = j then (1 : ℂ) else 0
  fin_cases a <;> fin_cases i <;> fin_cases j <;> apply Complex.ext <;> qutrit_arith

set_option maxHeartbeats 2000000 in
/-- Every cross-basis squared overlap is exactly 1/3. -/
theorem basis_mutually_unbiased (a b : Fin 4) (hab : a ≠ b) (i j : Q) :
    Complex.normSq (((basis a)ᴴ * basis b) i j) = 1/3 := by
  change Complex.normSq (∑ x : Q, conj (basis a x i) * basis b x j) = 1/3
  fin_cases a <;> fin_cases b <;> try contradiction
  all_goals fin_cases i <;> fin_cases j <;> qutrit_arith

end ECQC.Qutrit
