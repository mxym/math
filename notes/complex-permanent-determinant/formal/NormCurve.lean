import Main
import Mathlib.Data.Real.Sqrt
open scoped ComplexConjugate

namespace ComplexPencilFull
open ComplexPencilMain
open ComplexPencilLink

noncomputable section

def rt3 : ℝ := Real.sqrt 3
theorem rt3_pos : 0 < rt3 := Real.sqrt_pos.2 (by norm_num)
theorem rt3_sq : rt3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

def normBoundSq (lam : ℂ) : ℝ :=
  max (4/3 : ℝ)
      (max (1 + qval lam + 2*lam.re)
      (max (1 + qval lam - 2*lam.re)
      (max (qval lam + 1/3 + (2*rt3/3)*lam.im)
           (qval lam + 1/3 - (2*rt3/3)*lam.im))))

theorem bound_base (lam : ℂ) : (4/3 : ℝ) ≤ normBoundSq lam := by
  simp [normBoundSq]

theorem bound_plus (lam : ℂ) :
    1 + qval lam + 2*lam.re ≤ normBoundSq lam := by
  simp [normBoundSq]

theorem bound_minus (lam : ℂ) :
    1 + qval lam - 2*lam.re ≤ normBoundSq lam := by
  simp [normBoundSq]

theorem bound_fourier_plus (lam : ℂ) :
    qval lam + 1/3 + (2*rt3/3)*lam.im ≤ normBoundSq lam := by
  simp [normBoundSq]

theorem bound_fourier_minus (lam : ℂ) :
    qval lam + 1/3 - (2*rt3/3)*lam.im ≤ normBoundSq lam := by
  simp [normBoundSq]

theorem bound_preconditions (lam : ℂ) :
    0 ≤ normBoundSq lam ∧
    0 ≤ 3*normBoundSq lam - 4 ∧
    0 ≤ ComplexPencilCert.h (normBoundSq lam) (qval lam) +
         ComplexPencilCert.v lam.re ∧
    0 ≤ ComplexPencilCert.h (normBoundSq lam) (qval lam) -
         ComplexPencilCert.v lam.re ∧
    0 ≤ (3*(normBoundSq lam-qval lam)-1)^2 -
       12*(qval lam - lam.re*lam.re) := by
  have hb0 := bound_base lam
  have hbp := bound_plus lam
  have hbm := bound_minus lam
  have hfp := bound_fourier_plus lam
  have hfm := bound_fourier_minus lam
  have rr := rt3_sq
  have hG1 : 0 ≤ 3*(normBoundSq lam-qval lam)-1-2*rt3*lam.im := by
    linarith
  have hG2 : 0 ≤ 3*(normBoundSq lam-qval lam)-1+2*rt3*lam.im := by
    linarith
  have hprod := mul_nonneg hG1 hG2
  have hfactor :
     (3*(normBoundSq lam-qval lam)-1-2*rt3*lam.im)*
     (3*(normBoundSq lam-qval lam)-1+2*rt3*lam.im) =
     (3*(normBoundSq lam-qval lam)-1)^2-12*lam.im^2 := by
       calc
         _ = (3*(normBoundSq lam-qval lam)-1)^2-
             4*rt3^2*lam.im^2 := by ring
         _ = _ := by rw [rt3_sq]; ring
  have hq : qval lam-lam.re*lam.re=lam.im*lam.im := by
    simp [qval, ComplexPencilLink.sq] <;> ring
  refine ⟨by linarith, by linarith, ?_, ?_, ?_⟩
  · unfold ComplexPencilCert.h ComplexPencilCert.v
    linarith
  · unfold ComplexPencilCert.h ComplexPencilCert.v
    linarith
  · rw [hq]
    nlinarith [hfactor, hprod]

theorem exact_norm_upper (lam a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℂ) :
    ComplexPencilLink.sq
      (permanent3 a0 a1 a2 b0 b1 b2 c0 c1 c2 +
       lam*determinant3 a0 a1 a2 b0 b1 b2 c0 c1 c2) ≤
       normBoundSq lam * rowSq a0 a1 a2 *
        rowSq b0 b1 b2 * rowSq c0 c1 c2 := by
  obtain ⟨hB,h3B,hp,hm,hF⟩ := bound_preconditions lam
  exact pencil_squared_upper lam a0 a1 a2 b0 b1 b2 c0 c1 c2
       (normBoundSq lam) hB h3B hp hm hF

end
end ComplexPencilFull
