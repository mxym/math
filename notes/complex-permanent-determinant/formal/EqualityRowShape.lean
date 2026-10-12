import EqualitySaturation

namespace ComplexPencilEquality
open ComplexPencilCert
open ComplexPencilMain
open ComplexPencilLink
open ComplexPencilAbsolute

noncomputable section

private theorem link_sq_zero (z : ℂ)
    (hz : ComplexPencilLink.sq z = 0) : z = 0 := by
  exact ComplexPencilCert.sq_zero z
    ((ComplexPencilMain.sq_agree z).trans hz)

/-- Equality in the complex squared sharp-lens bound forces the
first row's three squared moduli to be equal or one-sparse,
provided all three rows are nonzero and the selected coefficient
has the sharp disk boundary modulus. -/
theorem first_row_shape_of_saturated_pencil
    (lam a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℂ)
    (hlens : qval lam+2*|lam.re|≤(1/3:ℝ))
    (hradius : qval lam=detWeight^2)
    (hbpos : 0<rowSq b0 b1 b2)
    (hcpos : 0<rowSq c0 c1 c2)
    (hsat :
      ComplexPencilLink.sq
      (permanent3 a0 a1 a2 b0 b1 b2 c0 c1 c2+
       lam*determinant3 a0 a1 a2 b0 b1 b2 c0 c1 c2) =
      (4/3:ℝ)*rowSq a0 a1 a2*rowSq b0 b1 b2*
       rowSq c0 c1 c2) :
    ((ComplexPencilLink.sq a0=ComplexPencilLink.sq a1 ∧
      ComplexPencilLink.sq a1=ComplexPencilLink.sq a2) ∨
     (a1=0 ∧ a2=0) ∨
     (a0=0 ∧ a2=0) ∨
     (a0=0 ∧ a1=0)) := by
  let X : ℝ := ComplexPencilLink.sq a0
  let Y : ℝ := ComplexPencilLink.sq a1
  let Z : ℝ := ComplexPencilLink.sq a2
  let q : ℝ := qval lam
  let x : ℝ := lam.re
  let B : ℝ := 4/3
  let d1 : ℝ := diag1 X Y Z B q x
  let d2 : ℝ := diag2 X Y Z B q x
  let d3 : ℝ := diag3 X Y Z B q x
  let u : ℂ := uentry lam a0 a1
  let v' : ℂ := ventry lam a0 a2
  let w : ℂ := wentry lam a1 a2
  have hX : 0≤X := ComplexPencilLink.sq_nonneg a0
  have hY : 0≤Y := ComplexPencilLink.sq_nonneg a1
  have hZ : 0≤Z := ComplexPencilLink.sq_nonneg a2
  obtain ⟨hB,h3B,hp,hm,hF⟩ := lens_preconditions lam hlens
  have hd1 : 0≤d1 := by
    unfold d1 diag1
    exact add_nonneg
      (add_nonneg (mul_nonneg hB hX) (mul_nonneg hp hY))
      (mul_nonneg hm hZ)
  have hm12 : 0≤m12 d1 d2 u := by
    rw [show m12 d1 d2 u = minorDirect X Y Z B q x from
      minor01_actual lam a0 a1 a2 B]
    exact minor_certificate_nonneg X Y Z B q x hX hY hZ hB hp hm
  have hm13 : 0≤m13 d1 d3 v' := by
    rw [show m13 d1 d3 v' = minorDirect Z X Y B q x from
      minor13_actual lam a0 a1 a2 B]
    exact minor_certificate_nonneg Z X Y B q x hZ hX hY hB hp hm
  have hdet : 0≤det3 d1 d2 d3 u v' w := by
    rw [show det3 d1 d2 d3 u v' w =
        detDirect X Y Z B q x from
          determinant_actual lam a0 a1 a2 B]
    exact determinant_certificate_nonneg
      X Y Z B q x hX hY hZ hB h3B hp hm hF
  have hQnonneg : 0≤Q3 d1 d2 d3 u v' w b0 b1 b2 :=
    q3_actual_nonneg lam a0 a1 a2 b0 b1 b2
      B hB h3B hp hm hF
  have hQzero : Q3 d1 d2 d3 u v' w b0 b1 b2=0 :=
    Q3_zero_of_pencil_saturation
      lam a0 a1 a2 b0 b1 b2 c0 c1 c2 B
      hcpos hsat hQnonneg
  have hbnz : b0≠0 ∨ b1≠0 ∨ b2≠0 := by
    by_contra h
    push_neg at h
    obtain ⟨h0,h1,h2⟩ := h
    simp [rowSq,h0,h1,h2,ComplexPencilLink.sq] at hbpos
  have hdetzero : det3 d1 d2 d3 u v' w=0 :=
    Q3_zero_det_zero d1 d2 d3 u v' w b0 b1 b2
      hd1 hm12 hm13 hdet hbnz hQzero
  have hdetpoly : detDirect X Y Z B q x=0 := by
    rw [←show det3 d1 d2 d3 u v' w =
      detDirect X Y Z B q x from
      determinant_actual lam a0 a1 a2 B]
    exact hdetzero
  have hsp : 0<detWeight := by
    have hp' := detWeight_nonneg
    have hi := detWeight_identity
    nlinarith
  have hpositive : 0 < ComplexPencilCert.h B q := by
    dsimp [ComplexPencilCert.h, B, q]
    rw [hradius]
    nlinarith [detWeight_identity]
  have hvzero : V X Y Z=0 :=
    V_zero_of_det_zero X Y Z B q x hX hY hZ
      (by norm_num : 0<B) h3B hp hm hF
      hpositive hdetpoly
  rcases V_zero_classify X Y Z hX hY hZ hvzero with heq | hsp
  · exact Or.inl heq
  · rcases hsp with hsp | hsp
    · exact Or.inr (Or.inl
        ⟨link_sq_zero a1 hsp.1,
         link_sq_zero a2 hsp.2⟩)
    · rcases hsp with hsp | hsp
      · exact Or.inr (Or.inr (Or.inl
        ⟨link_sq_zero a0 hsp.1,
         link_sq_zero a2 hsp.2⟩))
      · exact Or.inr (Or.inr (Or.inr
        ⟨link_sq_zero a0 hsp.1,
         link_sq_zero a1 hsp.2⟩))

#print axioms ComplexPencilEquality.first_row_shape_of_saturated_pencil

end
end ComplexPencilEquality
