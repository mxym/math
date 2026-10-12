import EqualityFlatStrictMinor

namespace ComplexPencilEquality

open ComplexPencilCert
open ComplexPencilMain
open ComplexPencilLink
open ComplexPencilAbsolute

noncomputable section

/-- Equality in the universal sharp complex pencil with a flat,
nonzero first row forces the second row to be a scalar multiple.
This is the strict-nullspace part of the rank-one classification. -/
theorem saturated_flat_second_row_parallel
    (lam a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℂ)
    (hlens : qval lam + 2*|lam.re| ≤ (1/3:ℝ))
    (hradius : qval lam = detWeight^2)
    (he01 : ComplexPencilLink.sq a0 = ComplexPencilLink.sq a1)
    (he12 : ComplexPencilLink.sq a1 = ComplexPencilLink.sq a2)
    (hapos : 0 < rowSq a0 a1 a2)
    (hcpos : 0 < rowSq c0 c1 c2)
    (hsat :
      ComplexPencilLink.sq
      (permanent3 a0 a1 a2 b0 b1 b2 c0 c1 c2 +
       lam*determinant3 a0 a1 a2 b0 b1 b2 c0 c1 c2) =
      (4/3:ℝ)*rowSq a0 a1 a2 * rowSq b0 b1 b2 *
         rowSq c0 c1 c2) :
    ∃ z : ℂ, b0=z*a0 ∧ b1=z*a1 ∧ b2=z*a2 := by
  let X : ℝ := ComplexPencilLink.sq a0
  let Y : ℝ := ComplexPencilLink.sq a1
  let Z : ℝ := ComplexPencilLink.sq a2
  let B : ℝ := 4/3
  let q : ℝ := qval lam
  let x : ℝ := lam.re
  let d1 : ℝ := diag1 X Y Z B q x
  let d2 : ℝ := diag2 X Y Z B q x
  let d3 : ℝ := diag3 X Y Z B q x
  let u : ℂ := uentry lam a0 a1
  let v' : ℂ := ventry lam a0 a2
  let w : ℂ := wentry lam a1 a2
  have hX : 0 < X := by
    have hflat : rowSq a0 a1 a2 = 3*X := by
      dsimp [rowSq, X]
      rw [←he12, ←he01]
      ring
    rw [hflat] at hapos
    linarith
  have hY : 0 ≤ Y := ComplexPencilLink.sq_nonneg a1
  have hZ : 0 ≤ Z := ComplexPencilLink.sq_nonneg a2
  obtain ⟨hB,h3B,hp,hm,hF⟩ := lens_preconditions lam hlens
  have hd1 : 0 < d1 := by
    have hp0 : 0 < B*X := mul_pos (by norm_num : (0:ℝ)<B) hX
    have hp1 : 0 ≤ (ComplexPencilCert.h B q +
        ComplexPencilCert.v x)*Y := mul_nonneg hp hY
    have hp2 : 0 ≤ (ComplexPencilCert.h B q -
        ComplexPencilCert.v x)*Z := mul_nonneg hm hZ
    unfold d1 diag1
    linarith
  have hminor : 0 < m12 d1 d2 u :=
    flat_first_row_minor_positive lam a0 a1 a2
      he01 he12 hapos hradius
  have hdetpoly : detDirect X X X B q x=0 := by
    dsimp [B]
    rw [determinant_global_identity]
    unfold detCertificate U V
    ring
  have hdet : det3 d1 d2 d3 u v' w=0 := by
    dsimp [d1,d2,d3,u,v',w,X,Y,Z,B,q,x]
    rw [determinant_actual]
    rw [←he12,←he01]
    exact hdetpoly
  have hQb : Q3 d1 d2 d3 u v' w b0 b1 b2=0 := by
    apply Q3_zero_of_pencil_saturation
      lam a0 a1 a2 b0 b1 b2 c0 c1 c2 B hcpos hsat
    exact q3_actual_nonneg lam a0 a1 a2 b0 b1 b2
      B hB h3B hp hm hF
  have hQa : Q3 d1 d2 d3 u v' w a0 a1 a2=0 :=
    flat_first_row_null_vector lam a0 a1 a2 he01 he12
  have ha2nonzero : a2 ≠ 0 := by
    intro heq
    have hsq : ComplexPencilLink.sq a2=0 := by
      simp [heq,ComplexPencilLink.sq]
    have hrel : X = ComplexPencilLink.sq a2 := by
      exact he01.trans he12
    rw [hrel,hsq] at hX
    exact (not_lt_of_ge (le_refl (0:ℝ))) hX
  exact Hermitian_nullspace_is_line
      d1 d2 d3 u v' w a0 a1 a2 b0 b1 b2
      hd1 hminor hdet hQa hQb ha2nonzero

#print axioms ComplexPencilEquality.saturated_flat_second_row_parallel

end
end ComplexPencilEquality
