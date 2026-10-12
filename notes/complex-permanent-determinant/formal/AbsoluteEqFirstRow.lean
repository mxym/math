import EqualityFirstRow

open scoped ComplexConjugate
namespace ComplexPencilEquality
open ComplexPencilMain
open ComplexPencilAbsolute

noncomputable section

theorem link_sq_zero (z : ℂ)
    (h : ComplexPencilLink.sq z=0) : z=0 := by
  apply ComplexPencilCert.sq_zero z
  rw [ComplexPencilMain.sq_agree]
  exact h

theorem absolute_equality_forces_V_zero
    (a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℂ)
    (hb : 0 < rowSq b0 b1 b2)
    (hc : 0 < rowSq c0 c1 c2)
    (heq :
      (‖permanent3 a0 a1 a2 b0 b1 b2 c0 c1 c2‖+
       detWeight*‖determinant3 a0 a1 a2 b0 b1 b2 c0 c1 c2‖)^2 =
      (4/3:ℝ)*rowSq a0 a1 a2*
        rowSq b0 b1 b2*rowSq c0 c1 c2) :
    ComplexPencilCert.V
      (ComplexPencilLink.sq a0)
      (ComplexPencilLink.sq a1)
      (ComplexPencilLink.sq a2) = 0 := by
  let P := permanent3 a0 a1 a2 b0 b1 b2 c0 c1 c2
  let D := determinant3 a0 a1 a2 b0 b1 b2 c0 c1 c2
  obtain ⟨lam, hlam, halign⟩ :=
    aligned_phase P D detWeight detWeight_nonneg
  have heqP :
      ComplexPencilLink.sq
       (c0*(t0 lam a1 a2 b1 b2)+
        c1*(t1 lam a0 a2 b0 b2)+
        c2*(t2 lam a0 a1 b0 b1)) =
      (4/3:ℝ)*rowSq a0 a1 a2*
        rowSq b0 b1 b2*rowSq c0 c1 c2 := by
    rw [trilinear_pencil_identity]
    change ComplexPencilLink.sq (P+lam*D)=_
    rw [← ComplexPencilFull.normSq_eq_sq, halign]
    exact heq
  exact pencil_equality_forces_V_zero
    lam a0 a1 a2 b0 b1 b2 c0 c1 c2
    hlam hb hc heqP

theorem absolute_equality_firstrow_support
    (a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℂ)
    (hb : 0 < rowSq b0 b1 b2)
    (hc : 0 < rowSq c0 c1 c2)
    (heq :
      (‖permanent3 a0 a1 a2 b0 b1 b2 c0 c1 c2‖+
       detWeight*‖determinant3 a0 a1 a2 b0 b1 b2 c0 c1 c2‖)^2 =
      (4/3:ℝ)*rowSq a0 a1 a2*
        rowSq b0 b1 b2*rowSq c0 c1 c2) :
    ((ComplexPencilLink.sq a0 = ComplexPencilLink.sq a1 ∧
        ComplexPencilLink.sq a1 = ComplexPencilLink.sq a2) ∨
      (a0=0 ∧ a1=0) ∨ (a0=0 ∧ a2=0) ∨
      (a1=0 ∧ a2=0)) := by
  have hV := absolute_equality_forces_V_zero
      a0 a1 a2 b0 b1 b2 c0 c1 c2 hb hc heq
  rcases ComplexPencilEquality.V_zero_support
      (ComplexPencilLink.sq a0)
      (ComplexPencilLink.sq a1)
      (ComplexPencilLink.sq a2)
      (ComplexPencilLink.sq_nonneg a0)
      (ComplexPencilLink.sq_nonneg a1)
      (ComplexPencilLink.sq_nonneg a2) hV with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl
      ⟨link_sq_zero a0 h.1,
       link_sq_zero a1 h.2⟩)
  · exact Or.inr (Or.inr (Or.inl
      ⟨link_sq_zero a0 h.1,
       link_sq_zero a2 h.2⟩))
  · exact Or.inr (Or.inr (Or.inr
      ⟨link_sq_zero a1 h.1,
       link_sq_zero a2 h.2⟩))

#print axioms ComplexPencilEquality.absolute_equality_firstrow_support

end
end ComplexPencilEquality
