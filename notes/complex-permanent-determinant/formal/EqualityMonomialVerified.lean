import EqualityCases

namespace ComplexPencilEquality
open ComplexPencilMain
open ComplexPencilAbsolute

noncomputable section

theorem sparse_rows_permanent_energy
    (a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℂ)
    (ha : oneSparse a0 a1 a2)
    (hb : oneSparse b0 b1 b2)
    (hc : oneSparse c0 c1 c2)
    (hper : permanent3 a0 a1 a2 b0 b1 b2 c0 c1 c2≠0) :
    ComplexPencilLink.sq
      (permanent3 a0 a1 a2 b0 b1 b2 c0 c1 c2) =
      rowSq a0 a1 a2*rowSq b0 b1 b2*rowSq c0 c1 c2 := by
  rcases ha with ⟨ha0,ha1⟩ | ⟨ha0,ha2⟩ | ⟨ha1,ha2⟩ <;>
    rcases hb with ⟨hb0,hb1⟩ | ⟨hb0,hb2⟩ | ⟨hb1,hb2⟩ <;>
    rcases hc with ⟨hc0,hc1⟩ | ⟨hc0,hc2⟩ | ⟨hc1,hc2⟩ <;>
    simp_all [permanent3,rowSq,
      ComplexPencilLink.sq_mul, ComplexPencilLink.sq] <;>
    ring

theorem monomialRows_saturates_verified
    (a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℂ)
    (hm : monomialRows a0 a1 a2 b0 b1 b2 c0 c1 c2) :
      (‖permanent3 a0 a1 a2 b0 b1 b2 c0 c1 c2‖+
       detWeight*‖determinant3 a0 a1 a2 b0 b1 b2 c0 c1 c2‖)^2 =
       (4/3:ℝ)*rowSq a0 a1 a2*
        rowSq b0 b1 b2*rowSq c0 c1 c2 := by
  rcases hm with ⟨ha,hb,hc,hper⟩
  have hsgn := sparse_rows_det_sign a0 a1 a2 b0 b1 b2 c0 c1 c2 ha hb hc
  have hnorm :
      ‖determinant3 a0 a1 a2 b0 b1 b2 c0 c1 c2‖ =
      ‖permanent3 a0 a1 a2 b0 b1 b2 c0 c1 c2‖ := by
    rcases hsgn with he | he
    · rw [he]
    · rw [he,norm_neg]
  have hP := sparse_rows_permanent_energy
    a0 a1 a2 b0 b1 b2 c0 c1 c2 ha hb hc hper
  rw [hnorm]
  have hcoef : 1+detWeight=ComplexPencilFull.rho := by
    unfold detWeight
    ring
  have hρ := ComplexPencilFull.rho_sq
  have hnormsq :
     ‖permanent3 a0 a1 a2 b0 b1 b2 c0 c1 c2‖^2 =
       rowSq a0 a1 a2*rowSq b0 b1 b2*rowSq c0 c1 c2 := by
    rw [ComplexPencilFull.norm_sq_equals_sq]
    exact hP
  calc
    (‖permanent3 a0 a1 a2 b0 b1 b2 c0 c1 c2‖+
     detWeight*‖permanent3 a0 a1 a2 b0 b1 b2 c0 c1 c2‖)^2 =
    ((1+detWeight)*‖permanent3 a0 a1 a2 b0 b1 b2 c0 c1 c2‖)^2 := by
      ring
    _ = ComplexPencilFull.rho^2 *
        ‖permanent3 a0 a1 a2 b0 b1 b2 c0 c1 c2‖^2 := by
      rw [hcoef]; ring
    _ = (4/3:ℝ)*rowSq a0 a1 a2*
         rowSq b0 b1 b2*rowSq c0 c1 c2 := by
      rw [hρ,hnormsq]
      ring

#print axioms ComplexPencilEquality.monomialRows_saturates_verified

end
end ComplexPencilEquality
