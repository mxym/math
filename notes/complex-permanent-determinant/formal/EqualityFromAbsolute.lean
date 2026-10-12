import EqualityRowShape

namespace ComplexPencilEquality
open ComplexPencilMain
open ComplexPencilAbsolute
open ComplexPencilLink

noncomputable section

/-- The exact sharp absolute permanent–determinant equality, together
with nonzero second/third rows, forces the first row to have equal
squared coordinate moduli or one-sparse support. -/
theorem absolute_equality_first_row_shape
    (a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℂ)
    (hbpos : 0 < rowSq b0 b1 b2)
    (hcpos : 0 < rowSq c0 c1 c2)
    (heq :
      ‖permanent3 a0 a1 a2 b0 b1 b2 c0 c1 c2‖+
      detWeight*‖determinant3 a0 a1 a2 b0 b1 b2 c0 c1 c2‖ =
      ComplexPencilFull.rho*rowNorm a0 a1 a2*
         rowNorm b0 b1 b2*rowNorm c0 c1 c2) :
    ((ComplexPencilLink.sq a0=ComplexPencilLink.sq a1 ∧
      ComplexPencilLink.sq a1=ComplexPencilLink.sq a2) ∨
     (a1=0 ∧ a2=0) ∨
     (a0=0 ∧ a2=0) ∨
     (a0=0 ∧ a1=0)) := by
  let P := permanent3 a0 a1 a2 b0 b1 b2 c0 c1 c2
  let D := determinant3 a0 a1 a2 b0 b1 b2 c0 c1 c2
  obtain ⟨lam, hrad, halign⟩ :=
    aligned_phase P D detWeight detWeight_nonneg
  have hlens := lens_of_normSq lam hrad
  have hqrad : qval lam=detWeight^2 := by
    exact (ComplexPencilFull.normSq_eq_sq lam).symm.trans hrad
  have hs : ComplexPencilLink.sq (P+lam*D) =
      (4/3:ℝ)*rowSq a0 a1 a2*rowSq b0 b1 b2*
        rowSq c0 c1 c2 := by
    rw [←ComplexPencilFull.normSq_eq_sq]
    rw [halign,heq]
    rw [mul_pow,mul_pow,mul_pow,ComplexPencilFull.rho_sq,
      rowNorm_sq, rowNorm_sq, rowNorm_sq]
  exact first_row_shape_of_saturated_pencil
    lam a0 a1 a2 b0 b1 b2 c0 c1 c2
    hlens hqrad hbpos hcpos hs

#print axioms ComplexPencilEquality.absolute_equality_first_row_shape

end
end ComplexPencilEquality
