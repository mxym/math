import EqualityFlatKernel

namespace ComplexPencilEquality
open ComplexPencilCert
open ComplexPencilMain
open ComplexPencilLink
open ComplexPencilAbsolute
noncomputable section

theorem flat_minor_polynomial (X q x : ℝ) :
    minorDirect X X X (4/3) q x =
      X*X*((1-3*q)*(3-q)+4*x*x) := by
  unfold minorDirect diag1 diag2 z2 h v
  ring

theorem flat_minor_positive (X q x : ℝ)
    (hX : 0 < X) (hq : q < 1/3) :
    0 < minorDirect X X X (4/3) q x := by
  rw [flat_minor_polynomial]
  have h1 : 0 < 1-3*q := by linarith
  have h2 : 0 < 3-q := by linarith
  have hx : 0 ≤ 4*x*x := by nlinarith [_root_.sq_nonneg x]
  exact mul_pos (mul_pos hX hX)
    (add_pos_of_pos_of_nonneg (mul_pos h1 h2) hx)

theorem flat_first_row_minor_positive
    (lam a0 a1 a2 : ℂ)
    (he01 : ComplexPencilLink.sq a0 = ComplexPencilLink.sq a1)
    (he12 : ComplexPencilLink.sq a1 = ComplexPencilLink.sq a2)
    (haPos : 0 < rowSq a0 a1 a2)
    (hradius : qval lam = detWeight^2) :
    0 < m12
      (diag1 (ComplexPencilLink.sq a0)
        (ComplexPencilLink.sq a1) (ComplexPencilLink.sq a2)
        (4/3) (qval lam) lam.re)
      (diag2 (ComplexPencilLink.sq a0)
        (ComplexPencilLink.sq a1) (ComplexPencilLink.sq a2)
        (4/3) (qval lam) lam.re)
      (uentry lam a0 a1) := by
  have hW := detWeight_identity
  have hW0 := detWeight_nonneg
  have hWp : 0 < detWeight := by nlinarith
  have hq : qval lam < 1/3 := by rw [hradius]; nlinarith
  have hflat : rowSq a0 a1 a2 =
      3 * ComplexPencilLink.sq a0 := by
    unfold rowSq
    rw [←he12, ←he01]
    ring
  have hX : 0 < ComplexPencilLink.sq a0 := by
    rw [hflat] at haPos
    linarith
  rw [ComplexPencilMain.minor01_actual]
  rw [←he12, ←he01]
  exact flat_minor_positive _ _ _ hX hq

#print axioms ComplexPencilEquality.flat_first_row_minor_positive

end
end ComplexPencilEquality
