import AbsolutePencil
import TensorNormSharp

namespace ComplexPencilEquality
open ComplexPencilCert
open ComplexPencilMain
open ComplexPencilAbsolute
open ComplexPencilLink

noncomputable section

/-- The exact nonnegative cubic form in the determinant certificate
vanishes only for three equal nonnegative coordinates, or a vector
with at most one nonzero coordinate. -/
theorem V_zero_classify (X Y Z : ℝ)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hZ : 0 ≤ Z)
    (hv : V X Y Z = 0) :
    (X = Y ∧ Y = Z) ∨
    (Y = 0 ∧ Z = 0) ∨
    (X = 0 ∧ Z = 0) ∨
    (X = 0 ∧ Y = 0) := by
  have h1 : 0 ≤ X*(Y-Z)^2 := mul_nonneg hX (_root_.sq_nonneg _)
  have h2 : 0 ≤ Y*(Z-X)^2 := mul_nonneg hY (_root_.sq_nonneg _)
  have h3 : 0 ≤ Z*(X-Y)^2 := mul_nonneg hZ (_root_.sq_nonneg _)
  have hz : X*(Y-Z)^2 + Y*(Z-X)^2 + Z*(X-Y)^2 = 0 := by
    simpa only [V_sos] using hv
  have hz1 : X*(Y-Z)^2=0 := by linarith
  have hz2 : Y*(Z-X)^2=0 := by linarith
  by_cases hxp : 0 < X
  · have hyz : Y=Z := by
      have hs : (Y-Z)^2=0 := (mul_eq_zero.mp hz1).resolve_left (ne_of_gt hxp)
      nlinarith [_root_.sq_nonneg (Y-Z)]
    by_cases hyp : 0 < Y
    · have hzx : Z=X := by
        have hs : (Z-X)^2=0 := (mul_eq_zero.mp hz2).resolve_left (ne_of_gt hyp)
        nlinarith [_root_.sq_nonneg (Z-X)]
      exact Or.inl ⟨by linarith,hyz⟩
    · have hy0 : Y=0 := le_antisymm (le_of_not_gt hyp) hY
      exact Or.inr (Or.inl ⟨hy0,by linarith⟩)
  · have hx0 : X=0 := le_antisymm (le_of_not_gt hxp) hX
    by_cases hyp : 0 < Y
    · have hzx : Z=X := by
        have hs : (Z-X)^2=0 := (mul_eq_zero.mp hz2).resolve_left (ne_of_gt hyp)
        nlinarith [_root_.sq_nonneg (Z-X)]
      exact Or.inr (Or.inr (Or.inl ⟨hx0,by linarith⟩))
    · have hy0 : Y=0 := le_antisymm (le_of_not_gt hyp) hY
      exact Or.inr (Or.inr (Or.inr ⟨hx0,hy0⟩))

/-- If the positive determinant certificate vanishes, the
difference-discriminant cubic must vanish. -/
theorem V_zero_of_det_zero
    (X Y Z B q x : ℝ)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hZ : 0 ≤ Z)
    (hB : 0 < B) (h3B : 0 ≤ 3*B-4)
    (hp : 0 ≤ h B q+v x)
    (hm : 0 ≤ h B q-v x)
    (hF : 0 ≤ (3*(B-q)-1)^2-12*(q-x*x))
    (hpositive : 0 < h B q)
    (hdet : detDirect X Y Z B q x = 0) :
    V X Y Z = 0 := by
  have hsq : 0 ≤ (h B q)^2-(v x)^2 :=
    hsq_sub_vsq_nonneg B q x hp hm
  have hU := U_nonneg X Y Z hX hY hZ
  have hV := V_nonneg X Y Z hX hY hZ
  have hc : 0 < B*(3*(h B q)^2+(v x)^2) := by
    apply mul_pos hB
    nlinarith [_root_.sq_nonneg (v x)]
  have h1 : 0 ≤ B*((h B q)^2-(v x)^2)*U X Y Z := by
    exact mul_nonneg (mul_nonneg (le_of_lt hB) hsq) hU
  have h2 : 0 ≤ B*(3*(h B q)^2+(v x)^2)*V X Y Z := by
    exact mul_nonneg (le_of_lt hc) hV
  have h3 : 0 ≤ (3*B-4)*((3*(B-q)-1)^2-12*(q-x*x))*X*Y*Z := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg h3B hF) hX) hY) hZ
  rw [determinant_global_identity] at hdet
  unfold detCertificate at hdet
  have hzero : B*(3*(h B q)^2+(v x)^2)*V X Y Z=0 := by
    linarith
  exact (mul_eq_zero.mp hzero).resolve_left (ne_of_gt hc)

#print axioms ComplexPencilEquality.V_zero_classify
#print axioms ComplexPencilEquality.V_zero_of_det_zero

end
end ComplexPencilEquality
