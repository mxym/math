import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Exact Hermitian certificates for the full complex three-row pencil

The six-variable polynomial identities below reproduce the *global*
complex-coefficient proof from notes/complex-permanent-determinant/PAPER.md,
including the determinant and a principal 2x2 minor.

These theorems are universal polynomial statements over the reals;
they do not assume a numerical grid or an unproved determinant identity.
-/

namespace ComplexPencilCert

noncomputable section

def h (B q : ℝ) : ℝ := B - 1 - q
def v (x : ℝ) : ℝ := 2 * x

def U (X Y Z : ℝ) : ℝ :=
  X^3 + Y^3 + Z^3 - 3 * X * Y * Z

def V (X Y Z : ℝ) : ℝ :=
  (X+Y+Z)*(X*Y+Y*Z+Z*X)-9*X*Y*Z

theorem U_sos (X Y Z : ℝ) :
    U X Y Z =
       (X+Y+Z) * ((X-Y)^2 + (Y-Z)^2 + (Z-X)^2) / 2 := by
  unfold U
  ring

theorem V_sos (X Y Z : ℝ) :
    V X Y Z =
     X*(Y-Z)^2 + Y*(Z-X)^2 + Z*(X-Y)^2 := by
  unfold V
  ring

theorem U_nonneg (X Y Z : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hZ : 0 ≤ Z) : 0 ≤ U X Y Z := by
  rw [U_sos]
  positivity

theorem V_nonneg (X Y Z : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hZ : 0 ≤ Z) : 0 ≤ V X Y Z := by
  rw [V_sos]
  positivity

def diag1 (X Y Z B q x : ℝ) : ℝ :=
  B*X + (h B q + v x)*Y + (h B q - v x)*Z

def diag2 (X Y Z B q x : ℝ) : ℝ :=
  (h B q - v x)*X + B*Y + (h B q + v x)*Z

def diag3 (X Y Z B q x : ℝ) : ℝ :=
  (h B q + v x)*X + (h B q - v x)*Y + B*Z

def z2 (q x : ℝ) : ℝ :=
   (1+q)^2-(v x)^2

def reZ3 (q x : ℝ) : ℝ :=
   (1-q)^3 - 12*(1-q)*(q-x*x)

def detDirect (X Y Z B q x : ℝ) : ℝ :=
  (diag1 X Y Z B q x)*(diag2 X Y Z B q x)*
    (diag3 X Y Z B q x) -
    (z2 q x)*
    ((diag1 X Y Z B q x)*Y*Z +
     (diag2 X Y Z B q x)*X*Z +
     (diag3 X Y Z B q x)*X*Y) -
    2*(reZ3 q x)*X*Y*Z

def detCertificate (X Y Z B q x : ℝ) : ℝ :=
    B*((h B q)^2-(v x)^2)*U X Y Z +
    B*(3*(h B q)^2 + (v x)^2)*V X Y Z +
    (3*B-4)*((3*(B-q)-1)^2 - 12*(q-x*x))*X*Y*Z

theorem determinant_global_identity (X Y Z B q x : ℝ) :
    detDirect X Y Z B q x = detCertificate X Y Z B q x := by
  unfold detDirect detCertificate diag1 diag2 diag3 z2 reZ3 h v U V
  ring

def minorDirect (X Y Z B q x : ℝ) : ℝ :=
  (diag1 X Y Z B q x)*(diag2 X Y Z B q x) -
    (z2 q x)*X*Y

def minorCertificate (X Y Z B q x : ℝ) : ℝ :=
    B*(h B q - v x)*X*X +
    B*(h B q + v x)*Y*Y +
    ((h B q)^2-(v x)^2)*Z*Z +
    2*B*(h B q)*X*Y +
    (B*(h B q + v x)+(h B q - v x)^2)*X*Z +
    ((h B q + v x)^2 + B*(h B q - v x))*Y*Z

theorem minor_global_identity (X Y Z B q x : ℝ) :
    minorDirect X Y Z B q x = minorCertificate X Y Z B q x := by
  unfold minorDirect minorCertificate diag1 diag2 z2 h v
  ring

theorem hsq_sub_vsq_nonneg (B q x : ℝ)
    (hp : 0 ≤ h B q + v x) (hm : 0 ≤ h B q - v x) :
    0 ≤ (h B q)^2-(v x)^2 := by
  nlinarith [mul_nonneg hp hm]

theorem determinant_certificate_nonneg
    (X Y Z B q x : ℝ)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hZ : 0 ≤ Z)
    (hB : 0 ≤ B)
    (h3B : 0 ≤ 3*B-4)
    (hp : 0 ≤ h B q+v x)
    (hm : 0 ≤ h B q-v x)
    (hF : 0 ≤ (3*(B-q)-1)^2-12*(q-x*x)) :
    0 ≤ detDirect X Y Z B q x := by
  rw [determinant_global_identity]
  unfold detCertificate
  have hh : 0 ≤ (h B q)^2-(v x)^2 :=
    hsq_sub_vsq_nonneg B q x hp hm
  have hu := U_nonneg X Y Z hX hY hZ
  have hv := V_nonneg X Y Z hX hY hZ
  have hsmall : 0 ≤ 3*(h B q)^2+(v x)^2 := by positivity
  positivity

theorem minor_certificate_nonneg
    (X Y Z B q x : ℝ)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hZ : 0 ≤ Z)
    (hB : 0 ≤ B)
    (hp : 0 ≤ h B q+v x)
    (hm : 0 ≤ h B q-v x) :
    0 ≤ minorDirect X Y Z B q x := by
  rw [minor_global_identity]
  unfold minorCertificate
  have hh : 0 ≤ h B q := by linarith
  have hs : 0 ≤ (h B q)^2-(v x)^2 :=
    hsq_sub_vsq_nonneg B q x hp hm
  positivity

end
end ComplexPencilCert
