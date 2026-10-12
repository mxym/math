import EqualityCases

namespace ComplexPencilEquality
open ComplexPencilMain
open ComplexPencilAbsolute

noncomputable section

theorem rankone_permanent (a0 a1 a2 t u : ℂ) :
    permanent3 a0 a1 a2
      (t*a0) (t*a1) (t*a2)
      (u*a0) (u*a1) (u*a2) =
      6*t*u*a0*a1*a2 := by
  unfold permanent3
  ring

theorem rankone_determinant (a0 a1 a2 t u : ℂ) :
    determinant3 a0 a1 a2
      (t*a0) (t*a1) (t*a2)
      (u*a0) (u*a1) (u*a2) = 0 := by
  unfold determinant3
  ring

theorem rowSq_mul (t a0 a1 a2 : ℂ) :
    rowSq (t*a0) (t*a1) (t*a2) =
      ComplexPencilLink.sq t *rowSq a0 a1 a2 := by
  unfold rowSq
  rw [ComplexPencilLink.sq_mul,ComplexPencilLink.sq_mul,
      ComplexPencilLink.sq_mul]
  ring

theorem rowSq_flat (a0 a1 a2 : ℂ)
    (h01 : ComplexPencilLink.sq a0=ComplexPencilLink.sq a1)
    (h12 : ComplexPencilLink.sq a1=ComplexPencilLink.sq a2) :
    rowSq a0 a1 a2 = 3*ComplexPencilLink.sq a0 := by
  have hY : ComplexPencilLink.sq a1=ComplexPencilLink.sq a0 := h01.symm
  have hZ : ComplexPencilLink.sq a2=ComplexPencilLink.sq a0 :=
    (h01.trans h12).symm
  simp only [rowSq,hY,hZ]
  ring

theorem rankone_flat_absolute_equality (a0 a1 a2 t u : ℂ)
    (h01 : ComplexPencilLink.sq a0=ComplexPencilLink.sq a1)
    (h12 : ComplexPencilLink.sq a1=ComplexPencilLink.sq a2) :
      (‖permanent3 a0 a1 a2
        (t*a0) (t*a1) (t*a2)
        (u*a0) (u*a1) (u*a2)‖+
       detWeight*‖determinant3 a0 a1 a2
        (t*a0) (t*a1) (t*a2)
        (u*a0) (u*a1) (u*a2)‖)^2 =
       (4/3:ℝ)*rowSq a0 a1 a2*
        rowSq (t*a0) (t*a1) (t*a2)*
        rowSq (u*a0) (u*a1) (u*a2) := by
  rw [rankone_permanent,rankone_determinant]
  simp only [norm_zero,mul_zero,add_zero]
  rw [ComplexPencilFull.norm_sq_equals_sq]
  have h6 :
    ComplexPencilLink.sq ((6:ℂ)*t*u*a0*a1*a2) =
     36*ComplexPencilLink.sq t*ComplexPencilLink.sq u*
       ComplexPencilLink.sq a0*
       ComplexPencilLink.sq a1*ComplexPencilLink.sq a2 := by
    have hconst : ComplexPencilLink.sq (6:ℂ)=36 := by
      norm_num [ComplexPencilLink.sq]
    simp only [ComplexPencilLink.sq_mul,hconst]
  change ComplexPencilLink.sq (6*t*u*a0*a1*a2) = _
  rw [show (6:ℂ)*t*u*a0*a1*a2=6*t*u*a0*a1*a2 from rfl] at h6
  rw [h6, rowSq_mul,rowSq_mul,
       rowSq_flat a0 a1 a2 h01 h12]
  have hY : ComplexPencilLink.sq a1=ComplexPencilLink.sq a0 := h01.symm
  have hZ : ComplexPencilLink.sq a2=ComplexPencilLink.sq a0 :=
    (h01.trans h12).symm
  simp only [hY,hZ]
  ring

theorem flatRankOne_saturates_verified
    (a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℂ)
    (h : flatRankOne a0 a1 a2 b0 b1 b2 c0 c1 c2) :
      (‖permanent3 a0 a1 a2 b0 b1 b2 c0 c1 c2‖+
       detWeight*‖determinant3 a0 a1 a2 b0 b1 b2 c0 c1 c2‖)^2 =
       (4/3:ℝ)*rowSq a0 a1 a2*
        rowSq b0 b1 b2*rowSq c0 c1 c2 := by
  rcases h with ⟨h01,h12,han0,t,u,ht0,ht1,ht2,hu0,hu1,hu2⟩
  subst b0; subst b1; subst b2; subst c0; subst c1; subst c2
  exact rankone_flat_absolute_equality a0 a1 a2 t u h01 h12

#print axioms ComplexPencilEquality.flatRankOne_saturates_verified

end
end ComplexPencilEquality
