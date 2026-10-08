import EqualityFlatSaturation

namespace ComplexPencilEquality

open ComplexPencilMain
open ComplexPencilCert
open ComplexPencilLink

noncomputable section

/-- If both steps in the sharp permanent–determinant pencil norm
bound saturate, the terminal complex Cauchy–Schwarz inequality also
saturates *exactly*, without any positivity assumptions on phases. -/
theorem saturated_pencil_cauchy_equality
    (lam a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℂ)
    (B : ℝ)
    (hsat : ComplexPencilLink.sq
       (permanent3 a0 a1 a2 b0 b1 b2 c0 c1 c2+
         lam*determinant3 a0 a1 a2 b0 b1 b2 c0 c1 c2) =
       B*rowSq a0 a1 a2*rowSq b0 b1 b2*rowSq c0 c1 c2)
    (hQ : Q3
      (diag1 (ComplexPencilLink.sq a0)
        (ComplexPencilLink.sq a1) (ComplexPencilLink.sq a2)
        B (qval lam) lam.re)
      (diag2 (ComplexPencilLink.sq a0)
        (ComplexPencilLink.sq a1) (ComplexPencilLink.sq a2)
        B (qval lam) lam.re)
      (diag3 (ComplexPencilLink.sq a0)
        (ComplexPencilLink.sq a1) (ComplexPencilLink.sq a2)
        B (qval lam) lam.re)
      (uentry lam a0 a1) (ventry lam a0 a2)
      (wentry lam a1 a2) b0 b1 b2 = 0) :
    ComplexPencilLink.sq
      (c0*t0 lam a1 a2 b1 b2+
       c1*t1 lam a0 a2 b0 b2+
       c2*t2 lam a0 a1 b0 b1) =
    (ComplexPencilLink.sq c0+
     ComplexPencilLink.sq c1+
     ComplexPencilLink.sq c2) *
    (ComplexPencilLink.sq (t0 lam a1 a2 b1 b2)+
     ComplexPencilLink.sq (t1 lam a0 a2 b0 b2)+
     ComplexPencilLink.sq (t2 lam a0 a1 b0 b1)) := by
  have hb := actual_complement lam a0 a1 a2 b0 b1 b2 B
  rw [hQ] at hb
  have ht : B*rowSq a0 a1 a2*rowSq b0 b1 b2 =
      ComplexPencilLink.sq (t0 lam a1 a2 b1 b2)+
      ComplexPencilLink.sq (t1 lam a0 a2 b0 b2)+
      ComplexPencilLink.sq (t2 lam a0 a1 b0 b1) := by
    linarith
  have heq :
    ComplexPencilLink.sq
      (c0*t0 lam a1 a2 b1 b2+
       c1*t1 lam a0 a2 b0 b2+
       c2*t2 lam a0 a1 b0 b1) =
       B*rowSq a0 a1 a2*rowSq b0 b1 b2*
         rowSq c0 c1 c2 := by
    rw [trilinear_pencil_identity]
    exact hsat
  calc
    _ = B*rowSq a0 a1 a2*rowSq b0 b1 b2*
         rowSq c0 c1 c2 := heq
    _ = rowSq c0 c1 c2 *
      (ComplexPencilLink.sq (t0 lam a1 a2 b1 b2)+
       ComplexPencilLink.sq (t1 lam a0 a2 b0 b2)+
       ComplexPencilLink.sq (t2 lam a0 a1 b0 b1)) := by rw [←ht]; ring
    _ = _ := rfl

#print axioms ComplexPencilEquality.saturated_pencil_cauchy_equality

end
end ComplexPencilEquality
