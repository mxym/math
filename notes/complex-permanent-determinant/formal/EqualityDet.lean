import EqualityKernel

open scoped ComplexConjugate
namespace ComplexPencilEquality
open ComplexPencilCert
open ComplexPencilMain

noncomputable section

theorem zero_det_forces_V_zero
    (X Y Z B q x : ℝ)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hZ : 0 ≤ Z)
    (hB : 0 < B)
    (hp : 0 ≤ h B q + v x) (hm : 0 ≤ h B q - v x)
    (h3B : 3*B-4=0)
    (hh : 0 < h B q)
    (hdet : detDirect X Y Z B q x=0) :
    V X Y Z=0 := by
  have hcoefU : 0 ≤ B*((h B q)^2-(v x)^2) :=
    mul_nonneg (le_of_lt hB)
      (hsq_sub_vsq_nonneg B q x hp hm)
  have hcoefV : 0 < B*(3*(h B q)^2+(v x)^2) := by
    apply mul_pos hB
    nlinarith [sq_pos_of_pos hh, _root_.sq_nonneg (v x)]
  have hprodU : 0 ≤
    B*((h B q)^2-(v x)^2)*U X Y Z :=
    mul_nonneg hcoefU (U_nonneg X Y Z hX hY hZ)
  have hsum := hdet
  rw [determinant_global_identity] at hsum
  unfold detCertificate at hsum
  rw [h3B] at hsum
  simp only [zero_mul, add_zero] at hsum
  have hterm : B*(3*(h B q)^2+(v x)^2)*V X Y Z=0 := by
    have hv := V_nonneg X Y Z hX hY hZ
    have hprodV := mul_nonneg (le_of_lt hcoefV) hv
    linarith
  exact (mul_eq_zero.mp hterm).resolve_left (ne_of_gt hcoefV)

theorem actual_Q3_zero_det_zero
    (lam a0 a1 a2 b0 b1 b2 : ℂ) (B : ℝ)
    (hB : 0 ≤ B)
    (h3B : 0 ≤ 3*B-4)
    (hp : 0 ≤ ComplexPencilCert.h B (qval lam) +
              ComplexPencilCert.v lam.re)
    (hm : 0 ≤ ComplexPencilCert.h B (qval lam) -
              ComplexPencilCert.v lam.re)
    (hF : 0 ≤ (3*(B-qval lam)-1)^2 -
              12*(qval lam - lam.re*lam.re))
    (hQ : ComplexPencilCert.Q3
       (ComplexPencilCert.diag1 (ComplexPencilLink.sq a0)
         (ComplexPencilLink.sq a1) (ComplexPencilLink.sq a2)
         B (qval lam) lam.re)
       (ComplexPencilCert.diag2 (ComplexPencilLink.sq a0)
         (ComplexPencilLink.sq a1) (ComplexPencilLink.sq a2)
         B (qval lam) lam.re)
       (ComplexPencilCert.diag3 (ComplexPencilLink.sq a0)
         (ComplexPencilLink.sq a1) (ComplexPencilLink.sq a2)
         B (qval lam) lam.re)
       (uentry lam a0 a1) (ventry lam a0 a2)
       (wentry lam a1 a2) b0 b1 b2 = 0)
    (hnonzero : b0 ≠ 0 ∨ b1 ≠ 0 ∨ b2 ≠ 0) :
    detDirect (ComplexPencilLink.sq a0)
       (ComplexPencilLink.sq a1) (ComplexPencilLink.sq a2)
       B (qval lam) lam.re=0 := by
  let X := ComplexPencilLink.sq a0
  let Y := ComplexPencilLink.sq a1
  let Z := ComplexPencilLink.sq a2
  let q := qval lam
  let x := lam.re
  let d1 := ComplexPencilCert.diag1 X Y Z B q x
  let d2 := ComplexPencilCert.diag2 X Y Z B q x
  let d3 := ComplexPencilCert.diag3 X Y Z B q x
  let u := uentry lam a0 a1
  let v := ventry lam a0 a2
  let w := wentry lam a1 a2
  have hX : 0 ≤ X := ComplexPencilLink.sq_nonneg a0
  have hY : 0 ≤ Y := ComplexPencilLink.sq_nonneg a1
  have hZ : 0 ≤ Z := ComplexPencilLink.sq_nonneg a2
  have hd1 : 0 ≤ d1 := by
    unfold d1 ComplexPencilCert.diag1
    exact add_nonneg
      (add_nonneg (mul_nonneg hB hX) (mul_nonneg hp hY))
      (mul_nonneg hm hZ)
  have hd2 : 0 ≤ d2 := by
    unfold d2 ComplexPencilCert.diag2
    exact add_nonneg
      (add_nonneg (mul_nonneg hm hX) (mul_nonneg hB hY))
      (mul_nonneg hp hZ)
  have hd3 : 0 ≤ d3 := by
    unfold d3 ComplexPencilCert.diag3
    exact add_nonneg
      (add_nonneg (mul_nonneg hp hX) (mul_nonneg hm hY))
      (mul_nonneg hB hZ)
  have h12 : 0 ≤ ComplexPencilCert.m12 d1 d2 u := by
    rw [show ComplexPencilCert.m12 d1 d2 u =
       ComplexPencilCert.minorDirect X Y Z B q x from
         minor01_actual lam a0 a1 a2 B]
    exact ComplexPencilCert.minor_certificate_nonneg
       X Y Z B q x hX hY hZ hB hp hm
  have h13 : 0 ≤ ComplexPencilCert.m13 d1 d3 v := by
    rw [show ComplexPencilCert.m13 d1 d3 v =
       ComplexPencilCert.minorDirect Z X Y B q x from
         minor13_actual lam a0 a1 a2 B]
    exact ComplexPencilCert.minor_certificate_nonneg
       Z X Y B q x hZ hX hY hB hp hm
  have h23 : 0 ≤ ComplexPencilCert.m23 d2 d3 w := by
    rw [show ComplexPencilCert.m23 d2 d3 w =
       ComplexPencilCert.minorDirect Y Z X B q x from
         minor23_actual lam a0 a1 a2 B]
    exact ComplexPencilCert.minor_certificate_nonneg
       Y Z X B q x hY hZ hX hB hp hm
  have hdet : 0 ≤ ComplexPencilCert.det3 d1 d2 d3 u v w := by
    rw [show ComplexPencilCert.det3 d1 d2 d3 u v w =
        ComplexPencilCert.detDirect X Y Z B q x from
          determinant_actual lam a0 a1 a2 B]
    exact ComplexPencilCert.determinant_certificate_nonneg
       X Y Z B q x hX hY hZ hB h3B hp hm hF
  have hh : ComplexPencilCert.Q3 d1 d2 d3 u v w b0 b1 b2=0 := hQ
  have hz := hermitian3_zero_quadratic_det_zero
      d1 d2 d3 u v w b0 b1 b2
      hd1 hd2 hd3 h12 h13 h23 hdet hh hnonzero
  rw [determinant_actual] at hz
  exact hz

#print axioms ComplexPencilEquality.actual_Q3_zero_det_zero

end
end ComplexPencilEquality
