import EqualityFlatKernel

open scoped ComplexConjugate
namespace ComplexPencilEquality
open ComplexPencilMain
open ComplexPencilCert
open ComplexPencilAbsolute

noncomputable section

theorem pencil_equality_forces_Q3_zero
    (lam a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℂ)
    (hlens : qval lam + 2*|lam.re| ≤ (1/3:ℝ))
    (hc : 0 < rowSq c0 c1 c2)
    (heq : ComplexPencilLink.sq
      (c0*(t0 lam a1 a2 b1 b2)+
       c1*(t1 lam a0 a2 b0 b2)+
       c2*(t2 lam a0 a1 b0 b1)) =
       (4/3:ℝ)*rowSq a0 a1 a2*
         rowSq b0 b1 b2*rowSq c0 c1 c2) :
    Q3
      (diag1 (ComplexPencilLink.sq a0)
        (ComplexPencilLink.sq a1) (ComplexPencilLink.sq a2)
        (4/3:ℝ) (qval lam) lam.re)
      (diag2 (ComplexPencilLink.sq a0)
        (ComplexPencilLink.sq a1) (ComplexPencilLink.sq a2)
        (4/3:ℝ) (qval lam) lam.re)
      (diag3 (ComplexPencilLink.sq a0)
        (ComplexPencilLink.sq a1) (ComplexPencilLink.sq a2)
        (4/3:ℝ) (qval lam) lam.re)
      (uentry lam a0 a1)
      (ventry lam a0 a2)
      (wentry lam a1 a2) b0 b1 b2 = 0 := by
  let B : ℝ := 4/3
  let d1 := diag1 (ComplexPencilLink.sq a0)
      (ComplexPencilLink.sq a1) (ComplexPencilLink.sq a2)
       B (qval lam) lam.re
  let d2 := diag2 (ComplexPencilLink.sq a0)
      (ComplexPencilLink.sq a1) (ComplexPencilLink.sq a2)
       B (qval lam) lam.re
  let d3 := diag3 (ComplexPencilLink.sq a0)
      (ComplexPencilLink.sq a1) (ComplexPencilLink.sq a2)
       B (qval lam) lam.re
  let u := uentry lam a0 a1
  let v0 := ventry lam a0 a2
  let w := wentry lam a1 a2
  obtain ⟨hB,h3B,hp,hm,hF⟩ := lens_preconditions lam hlens
  have hqnonneg : 0 ≤ Q3 d1 d2 d3 u v0 w b0 b1 b2 :=
    q3_actual_nonneg lam a0 a1 a2 b0 b1 b2 B hB h3B hp hm hF
  have hcs :
    ComplexPencilLink.sq
      (c0*(t0 lam a1 a2 b1 b2)+
       c1*(t1 lam a0 a2 b0 b2)+
       c2*(t2 lam a0 a1 b0 b1)) ≤
    rowSq c0 c1 c2 *
      (ComplexPencilLink.sq (t0 lam a1 a2 b1 b2)+
       ComplexPencilLink.sq (t1 lam a0 a2 b0 b2)+
       ComplexPencilLink.sq (t2 lam a0 a1 b0 b1)) :=
      ComplexPencilLink.complex_three_cauchy c0 c1 c2 _ _ _
  have hbridge := actual_complement lam a0 a1 a2 b0 b1 b2 B
  have hprod :
     rowSq c0 c1 c2 * Q3 d1 d2 d3 u v0 w b0 b1 b2=0 := by
    apply le_antisymm
    · rw [← hbridge]
      dsimp [B]
      nlinarith [hcs, heq]
    · exact mul_nonneg (le_of_lt hc) hqnonneg
  exact (mul_eq_zero.mp hprod).resolve_left (ne_of_gt hc)

theorem absolute_equality_flat_second_row
    (a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℂ)
    (hc : 0 < rowSq c0 c1 c2)
    (hflat0 : ComplexPencilLink.sq a0=ComplexPencilLink.sq a1)
    (hflat1 : ComplexPencilLink.sq a1=ComplexPencilLink.sq a2)
    (ha0 : a0 ≠ 0)
    (heq :
      (‖permanent3 a0 a1 a2 b0 b1 b2 c0 c1 c2‖+
       detWeight*‖determinant3 a0 a1 a2 b0 b1 b2 c0 c1 c2‖)^2 =
      (4/3:ℝ)*rowSq a0 a1 a2*
        rowSq b0 b1 b2*rowSq c0 c1 c2) :
    ∃ t : ℂ, b0=t*a0 ∧ b1=t*a1 ∧ b2=t*a2 := by
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
  have hlens := lens_of_normSq lam hlam
  have hQ := pencil_equality_forces_Q3_zero
    lam a0 a1 a2 b0 b1 b2 c0 c1 c2 hlens hc heqP
  exact flat_kernel_collinear lam a0 a1 a2 b0 b1 b2
    hlam hflat0 hflat1 ha0 hQ

#print axioms ComplexPencilEquality.absolute_equality_flat_second_row

end
end ComplexPencilEquality
