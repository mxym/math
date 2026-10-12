import EqualityPhase

namespace ComplexPencilEquality
open ComplexPencilMain
open ComplexPencilAbsolute

noncomputable section

theorem permanent_swap_last (a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℂ) :
    permanent3 a0 a1 a2 c0 c1 c2 b0 b1 b2 =
      permanent3 a0 a1 a2 b0 b1 b2 c0 c1 c2 := by
  unfold permanent3
  ring

theorem determinant_swap_last (a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℂ) :
    determinant3 a0 a1 a2 c0 c1 c2 b0 b1 b2 =
      -determinant3 a0 a1 a2 b0 b1 b2 c0 c1 c2 := by
  unfold determinant3
  ring

theorem permanent_swap_first (a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℂ) :
    permanent3 b0 b1 b2 a0 a1 a2 c0 c1 c2 =
      permanent3 a0 a1 a2 b0 b1 b2 c0 c1 c2 := by
  unfold permanent3
  ring

theorem determinant_swap_first (a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℂ) :
    determinant3 b0 b1 b2 a0 a1 a2 c0 c1 c2 =
      -determinant3 a0 a1 a2 b0 b1 b2 c0 c1 c2 := by
  unfold determinant3
  ring

theorem equality_swap_last (a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℂ)
    (heq :
      (‖permanent3 a0 a1 a2 b0 b1 b2 c0 c1 c2‖+
       detWeight*‖determinant3 a0 a1 a2 b0 b1 b2 c0 c1 c2‖)^2 =
      (4/3:ℝ)*rowSq a0 a1 a2*
        rowSq b0 b1 b2*rowSq c0 c1 c2) :
      (‖permanent3 a0 a1 a2 c0 c1 c2 b0 b1 b2‖+
       detWeight*‖determinant3 a0 a1 a2 c0 c1 c2 b0 b1 b2‖)^2 =
      (4/3:ℝ)*rowSq a0 a1 a2*
        rowSq c0 c1 c2*rowSq b0 b1 b2 := by
  rw [permanent_swap_last,determinant_swap_last,norm_neg]
  convert heq using 1 <;> ring

theorem equality_swap_first (a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℂ)
    (heq :
      (‖permanent3 a0 a1 a2 b0 b1 b2 c0 c1 c2‖+
       detWeight*‖determinant3 a0 a1 a2 b0 b1 b2 c0 c1 c2‖)^2 =
      (4/3:ℝ)*rowSq a0 a1 a2*
        rowSq b0 b1 b2*rowSq c0 c1 c2) :
      (‖permanent3 b0 b1 b2 a0 a1 a2 c0 c1 c2‖+
       detWeight*‖determinant3 b0 b1 b2 a0 a1 a2 c0 c1 c2‖)^2 =
      (4/3:ℝ)*rowSq b0 b1 b2*
        rowSq a0 a1 a2*rowSq c0 c1 c2 := by
  rw [permanent_swap_first,determinant_swap_first,norm_neg]
  convert heq using 1 <;> ring

theorem absolute_equality_flat_rankone
    (a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℂ)
    (ha0 : a0 ≠ 0)
    (hflat0 : ComplexPencilLink.sq a0=ComplexPencilLink.sq a1)
    (hflat1 : ComplexPencilLink.sq a1=ComplexPencilLink.sq a2)
    (hb : 0 < rowSq b0 b1 b2)
    (hc : 0 < rowSq c0 c1 c2)
    (heq :
      (‖permanent3 a0 a1 a2 b0 b1 b2 c0 c1 c2‖+
       detWeight*‖determinant3 a0 a1 a2 b0 b1 b2 c0 c1 c2‖)^2 =
      (4/3:ℝ)*rowSq a0 a1 a2*
        rowSq b0 b1 b2*rowSq c0 c1 c2) :
    ∃ t u : ℂ, b0=t*a0 ∧ b1=t*a1 ∧ b2=t*a2 ∧
                c0=u*a0 ∧ c1=u*a1 ∧ c2=u*a2 := by
  obtain ⟨t,ht0,ht1,ht2⟩ :=
    absolute_equality_flat_second_row
     a0 a1 a2 b0 b1 b2 c0 c1 c2 hc hflat0 hflat1 ha0 heq
  have heqswap := equality_swap_last a0 a1 a2 b0 b1 b2 c0 c1 c2 heq
  obtain ⟨u,hu0,hu1,hu2⟩ :=
    absolute_equality_flat_second_row
     a0 a1 a2 c0 c1 c2 b0 b1 b2 hb hflat0 hflat1 ha0 heqswap
  exact ⟨t,u,ht0,ht1,ht2,hu0,hu1,hu2⟩

#print axioms ComplexPencilEquality.absolute_equality_flat_rankone

end
end ComplexPencilEquality
