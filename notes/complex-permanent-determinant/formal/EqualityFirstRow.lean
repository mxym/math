import EqualityDet

open scoped ComplexConjugate
namespace ComplexPencilEquality
open ComplexPencilMain
open ComplexPencilCert
open ComplexPencilAbsolute

noncomputable section

theorem pencil_equality_forces_V_zero
    (lam a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℂ)
    (hlam : Complex.normSq lam = detWeight^2)
    (hb : 0 < rowSq b0 b1 b2)
    (hc : 0 < rowSq c0 c1 c2)
    (heq : ComplexPencilLink.sq
      (c0*(t0 lam a1 a2 b1 b2)+
       c1*(t1 lam a0 a2 b0 b2)+
       c2*(t2 lam a0 a1 b0 b1)) =
       (4/3:ℝ)*rowSq a0 a1 a2*
         rowSq b0 b1 b2*rowSq c0 c1 c2) :
    V (ComplexPencilLink.sq a0)
      (ComplexPencilLink.sq a1)
      (ComplexPencilLink.sq a2)=0 := by
  let B : ℝ := 4/3
  let q : ℝ := qval lam
  let x : ℝ := lam.re
  let X : ℝ := ComplexPencilLink.sq a0
  let Y : ℝ := ComplexPencilLink.sq a1
  let Z : ℝ := ComplexPencilLink.sq a2
  let d1 := diag1 X Y Z B q x
  let d2 := diag2 X Y Z B q x
  let d3 := diag3 X Y Z B q x
  let u := uentry lam a0 a1
  let v0 := ventry lam a0 a2
  let w := wentry lam a1 a2
  have hlens := lens_of_normSq lam hlam
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
       ComplexPencilLink.sq (t2 lam a0 a1 b0 b1)) := by
    exact ComplexPencilLink.complex_three_cauchy
      c0 c1 c2 _ _ _
  have hbridge := actual_complement lam a0 a1 a2 b0 b1 b2 B
  have hprod :
     rowSq c0 c1 c2 * Q3 d1 d2 d3 u v0 w b0 b1 b2=0 := by
    apply le_antisymm
    · rw [← hbridge]
      dsimp [B]
      nlinarith [hcs, heq]
    · exact mul_nonneg (le_of_lt hc) hqnonneg
  have hQ : Q3 d1 d2 d3 u v0 w b0 b1 b2=0 :=
    (mul_eq_zero.mp hprod).resolve_left (ne_of_gt hc)
  have hbnz : b0 ≠ 0 ∨ b1 ≠ 0 ∨ b2 ≠ 0 := by
    by_contra hh
    push_neg at hh
    rcases hh with ⟨hb0,hb1,hb2⟩
    have hzero : rowSq b0 b1 b2=0 := by
      simp [rowSq,hb0,hb1,hb2,ComplexPencilLink.sq]
    exact (ne_of_gt hb) hzero
  have hdet0 : detDirect X Y Z B q x=0 :=
    actual_Q3_zero_det_zero lam a0 a1 a2 b0 b1 b2
      B hB h3B hp hm hF hQ hbnz
  have hqs : q=detWeight^2 := by
    dsimp [q]
    calc
      _ = Complex.normSq lam := by
        simp [qval, ComplexPencilLink.sq,
          Complex.normSq_apply,pow_two]
      _ = _ := hlam
  have hspos : 0<detWeight := by
    have hn := detWeight_nonneg
    have hi := detWeight_identity
    nlinarith
  have hhpos : 0 < h B q := by
    dsimp [B]
    rw [hqs]
    unfold ComplexPencilCert.h
    nlinarith [detWeight_identity]
  have h3eq : 3*B-4=0 := by dsimp [B]; norm_num
  exact zero_det_forces_V_zero X Y Z B q x
    (ComplexPencilLink.sq_nonneg a0)
    (ComplexPencilLink.sq_nonneg a1)
    (ComplexPencilLink.sq_nonneg a2)
    (by dsimp [B]; norm_num)
    hp hm h3eq hhpos hdet0

#print axioms ComplexPencilEquality.pencil_equality_forces_V_zero

end
end ComplexPencilEquality
