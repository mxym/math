import Link

open scoped ComplexConjugate

namespace ComplexPencilMain
open ComplexPencilLink

noncomputable section

def alpha (lam : ℂ) : ℂ := 1-lam
def beta (lam : ℂ) : ℂ := 1+lam
def qval (lam : ℂ) : ℝ := ComplexPencilLink.sq lam
def rowSq (a0 a1 a2 : ℂ) : ℝ := ComplexPencilLink.sq a0+ComplexPencilLink.sq a1+ComplexPencilLink.sq a2

def zout (lam : ℂ) : ℂ := (conj (alpha lam)) * beta lam

def p0 (lam a2 : ℂ) := alpha lam *a2
def q0 (lam a1 : ℂ) := beta lam*a1
def p1 (lam a2 : ℂ) := beta lam*a2
def q1 (lam a0 : ℂ) := alpha lam*a0
def p2 (lam a1 : ℂ) := alpha lam*a1
def q2 (lam a0 : ℂ) := beta lam*a0

def t0 (lam a1 a2 b1 b2 : ℂ) : ℂ :=
  p0 lam a2*b1+q0 lam a1*b2
def t1 (lam a0 a2 b0 b2 : ℂ) : ℂ :=
  p1 lam a2*b0+q1 lam a0*b2
def t2 (lam a0 a1 b0 b1 : ℂ) : ℂ :=
  p2 lam a1*b0+q2 lam a0*b1

def uentry (lam a0 a1 : ℂ) : ℂ :=
  -conj (p2 lam a1)*q2 lam a0
def ventry (lam a0 a2 : ℂ) : ℂ :=
  -conj (p1 lam a2)*q1 lam a0
def wentry (lam a1 a2 : ℂ) : ℂ :=
  -conj (p0 lam a2)*q0 lam a1

theorem sq_alpha (lam : ℂ) :
    ComplexPencilLink.sq (alpha lam) = 1+ComplexPencilLink.sq lam-2*lam.re := by
  simp [alpha, ComplexPencilLink.sq, Complex.sub_re, Complex.sub_im]
  ring

theorem sq_beta (lam : ℂ) :
    ComplexPencilLink.sq (beta lam) = 1+ComplexPencilLink.sq lam+2*lam.re := by
  simp [beta, ComplexPencilLink.sq, Complex.add_re, Complex.add_im]
  ring

theorem sq_conjugate (z : ℂ) : ComplexPencilLink.sq (conj z) = ComplexPencilLink.sq z := by
  simp [ComplexPencilLink.sq, Complex.conj_re, Complex.conj_im]

theorem sq_neg (z : ℂ) : ComplexPencilLink.sq (-z) = ComplexPencilLink.sq z := by
  simp [ComplexPencilLink.sq]

theorem diagonal0
    (lam a0 a1 a2 : ℂ) (B : ℝ) :
    B*rowSq a0 a1 a2-
       (ComplexPencilLink.sq (p1 lam a2)+ComplexPencilLink.sq (p2 lam a1)) =
      ComplexPencilCert.diag1 (ComplexPencilLink.sq a0) (ComplexPencilLink.sq a1) (ComplexPencilLink.sq a2) B (qval lam) lam.re := by
  simp [p1, p2, rowSq, ComplexPencilCert.diag1, ComplexPencilCert.h, ComplexPencilCert.v, qval,
    sq_mul, sq_alpha, sq_beta]
  ring

theorem diagonal1
    (lam a0 a1 a2 : ℂ) (B : ℝ) :
    B*rowSq a0 a1 a2-
       (ComplexPencilLink.sq (p0 lam a2)+ComplexPencilLink.sq (q2 lam a0)) =
      ComplexPencilCert.diag2 (ComplexPencilLink.sq a0) (ComplexPencilLink.sq a1) (ComplexPencilLink.sq a2) B (qval lam) lam.re := by
  simp [p0, q2, rowSq, ComplexPencilCert.diag2, ComplexPencilCert.h, ComplexPencilCert.v, qval,
    sq_mul, sq_alpha, sq_beta]
  ring

theorem diagonal2
    (lam a0 a1 a2 : ℂ) (B : ℝ) :
    B*rowSq a0 a1 a2-
       (ComplexPencilLink.sq (q0 lam a1)+ComplexPencilLink.sq (q1 lam a0)) =
      ComplexPencilCert.diag3 (ComplexPencilLink.sq a0) (ComplexPencilLink.sq a1) (ComplexPencilLink.sq a2) B (qval lam) lam.re := by
  simp [q0, q1, rowSq, ComplexPencilCert.diag3, ComplexPencilCert.h, ComplexPencilCert.v, qval,
    sq_mul, sq_alpha, sq_beta]
  ring

theorem zout_re (lam : ℂ) :
    (zout lam).re = 1-qval lam := by
  simp [zout, alpha, beta, qval, ComplexPencilLink.sq,
    Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.sub_re, Complex.conj_re, Complex.conj_im,
    Complex.add_im, Complex.sub_im]
  ring

theorem zout_im (lam : ℂ) :
    (zout lam).im = 2*lam.im := by
  simp [zout, alpha, beta, qval, ComplexPencilLink.sq,
    Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.sub_re, Complex.conj_re, Complex.conj_im,
    Complex.add_im, Complex.sub_im]
  ring

theorem sq_zout (lam : ℂ) :
    ComplexPencilLink.sq (zout lam) = ComplexPencilCert.z2 (qval lam) lam.re := by
  rw [show ComplexPencilLink.sq (zout lam)=(zout lam).re^2+(zout lam).im^2 by
    simp [ComplexPencilLink.sq, pow_two]]
  rw [zout_re, zout_im]
  simp [ComplexPencilCert.z2, ComplexPencilCert.v, qval, ComplexPencilLink.sq]
  ring

theorem rez3_zout (lam : ℂ) :
    ((zout lam)^3).re = ComplexPencilCert.reZ3 (qval lam) lam.re := by
  have hcube (z : ℂ) :
     (z^3).re = z.re^3-3*z.re*z.im^2 := by
    simp [pow_succ, Complex.mul_re, Complex.mul_im]
    ring
  rw [hcube, zout_re, zout_im]
  simp [ComplexPencilCert.reZ3, qval, ComplexPencilLink.sq]
  ring

theorem uentry_factor (lam a0 a1 : ℂ) :
    uentry lam a0 a1 = -(zout lam)*(conj a1)*a0 := by
  unfold uentry p2 q2 zout
  simp only [map_mul]
  ring

theorem ventry_factor (lam a0 a2 : ℂ) :
    ventry lam a0 a2 = -(conj (zout lam))*(conj a2)*a0 := by
  unfold ventry p1 q1 zout
  simp only [map_mul]
  simp
  ring

theorem wentry_factor (lam a1 a2 : ℂ) :
    wentry lam a1 a2 = -(zout lam)*(conj a2)*a1 := by
  unfold wentry p0 q0 zout
  simp only [map_mul]
  ring

theorem sq_agree (z : ℂ) :
    ComplexPencilCert.sq z = ComplexPencilLink.sq z := by
  simp [ComplexPencilCert.sq, ComplexPencilLink.sq, pow_two]

theorem sq_uentry (lam a0 a1 : ℂ) :
    ComplexPencilCert.sq (uentry lam a0 a1) =
       ComplexPencilCert.z2 (qval lam) lam.re *
       ComplexPencilLink.sq a0 * ComplexPencilLink.sq a1 := by
  rw [sq_agree, uentry_factor]
  simp only [ComplexPencilLink.sq_mul, sq_neg, sq_conjugate]
  rw [sq_zout]
  ring

theorem sq_ventry (lam a0 a2 : ℂ) :
    ComplexPencilCert.sq (ventry lam a0 a2) =
       ComplexPencilCert.z2 (qval lam) lam.re *
       ComplexPencilLink.sq a0 * ComplexPencilLink.sq a2 := by
  rw [sq_agree, ventry_factor]
  simp only [ComplexPencilLink.sq_mul, sq_neg, sq_conjugate]
  rw [sq_zout]
  ring

theorem sq_wentry (lam a1 a2 : ℂ) :
    ComplexPencilCert.sq (wentry lam a1 a2) =
       ComplexPencilCert.z2 (qval lam) lam.re *
       ComplexPencilLink.sq a1 * ComplexPencilLink.sq a2 := by
  rw [sq_agree, wentry_factor]
  simp only [ComplexPencilLink.sq_mul, sq_neg, sq_conjugate]
  rw [sq_zout]
  ring

theorem actual_complement
    (lam a0 a1 a2 b0 b1 b2 : ℂ) (B : ℝ) :
    B*(rowSq a0 a1 a2)*(rowSq b0 b1 b2) -
      (ComplexPencilLink.sq (t0 lam a1 a2 b1 b2) +
       ComplexPencilLink.sq (t1 lam a0 a2 b0 b2) +
       ComplexPencilLink.sq (t2 lam a0 a1 b0 b1)) =
      ComplexPencilCert.Q3
       (ComplexPencilCert.diag1 (ComplexPencilLink.sq a0)
         (ComplexPencilLink.sq a1) (ComplexPencilLink.sq a2)
         B (qval lam) lam.re)
       (ComplexPencilCert.diag2 (ComplexPencilLink.sq a0)
         (ComplexPencilLink.sq a1) (ComplexPencilLink.sq a2)
         B (qval lam) lam.re)
       (ComplexPencilCert.diag3 (ComplexPencilLink.sq a0)
         (ComplexPencilLink.sq a1) (ComplexPencilLink.sq a2)
         B (qval lam) lam.re)
       (uentry lam a0 a1)
       (ventry lam a0 a2)
       (wentry lam a1 a2) b0 b1 b2 := by
  have he :=
    ComplexPencilLink.zero_diagonal_norm_complement B
      (rowSq a0 a1 a2)
      (p0 lam a2) (q0 lam a1)
      (p1 lam a2) (q1 lam a0)
      (p2 lam a1) (q2 lam a0)
      b0 b1 b2
  rw [ComplexPencilLink.quad_as_PSD3,
      diagonal0, diagonal1, diagonal2] at he
  simpa only [ComplexPencilLink.threeOutputNorm, rowSq,
    t0, t1, t2, uentry, ventry, wentry, neg_mul] using he

theorem conjugate_times_self (z : ℂ) :
    (conj z) * z = (ComplexPencilLink.sq z : ℂ) := by
  calc
    _ = (Complex.normSq z : ℂ) :=
          (Complex.normSq_eq_conj_mul_self).symm
    _ = (ComplexPencilLink.sq z : ℂ) := by
      congr 1

theorem ventry_conj_factor (lam a0 a2 : ℂ) :
    conj (ventry lam a0 a2) =
      -(zout lam)*a2*(conj a0) := by
  rw [ventry_factor]
  simp only [map_mul, map_neg]
  simp

theorem offdiag_triple_factor (lam a0 a1 a2 : ℂ) :
   (uentry lam a0 a1)*(wentry lam a1 a2)*
      (conj (ventry lam a0 a2)) =
     -(zout lam)^3 *
      ((ComplexPencilLink.sq a0 *
        ComplexPencilLink.sq a1 *
        ComplexPencilLink.sq a2 : ℝ) : ℂ) := by
  rw [uentry_factor, wentry_factor, ventry_conj_factor]
  have h0 := conjugate_times_self a0
  have h1 := conjugate_times_self a1
  have h2 := conjugate_times_self a2
  calc
    _ = -((zout lam)^3) *
      (((conj a0)*a0)*((conj a1)*a1)*((conj a2)*a2)) := by ring
    _ = -(zout lam)^3 *
      ((ComplexPencilLink.sq a0 *
        ComplexPencilLink.sq a1 *
        ComplexPencilLink.sq a2 : ℝ) : ℂ) := by
      rw [h0, h1, h2]
      simp only [Complex.ofReal_mul]

theorem offdiag_triple_re (lam a0 a1 a2 : ℂ) :
   ((uentry lam a0 a1)*(wentry lam a1 a2)*
      (conj (ventry lam a0 a2))).re =
      -(ComplexPencilCert.reZ3 (qval lam) lam.re) *
      ComplexPencilLink.sq a0 *
      ComplexPencilLink.sq a1 *
      ComplexPencilLink.sq a2 := by
  rw [offdiag_triple_factor]
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
     Complex.ofReal_im, mul_zero, sub_zero]
  rw [rez3_zout]
  ring

theorem determinant_actual
    (lam a0 a1 a2 : ℂ) (B : ℝ) :
    ComplexPencilCert.det3
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
       (wentry lam a1 a2) =
     ComplexPencilCert.detDirect (ComplexPencilLink.sq a0)
        (ComplexPencilLink.sq a1) (ComplexPencilLink.sq a2)
        B (qval lam) lam.re := by
  unfold ComplexPencilCert.det3 ComplexPencilCert.detDirect
  rw [sq_wentry, sq_ventry, sq_uentry,
      offdiag_triple_re]
  ring

theorem minor01_actual
    (lam a0 a1 a2 : ℂ) (B : ℝ) :
    ComplexPencilCert.m12
       (ComplexPencilCert.diag1 (ComplexPencilLink.sq a0)
        (ComplexPencilLink.sq a1) (ComplexPencilLink.sq a2)
        B (qval lam) lam.re)
       (ComplexPencilCert.diag2 (ComplexPencilLink.sq a0)
        (ComplexPencilLink.sq a1) (ComplexPencilLink.sq a2)
        B (qval lam) lam.re)
       (uentry lam a0 a1) =
     ComplexPencilCert.minorDirect (ComplexPencilLink.sq a0)
        (ComplexPencilLink.sq a1) (ComplexPencilLink.sq a2)
        B (qval lam) lam.re := by
  unfold ComplexPencilCert.m12 ComplexPencilCert.minorDirect
  rw [sq_uentry]

theorem minor13_actual
    (lam a0 a1 a2 : ℂ) (B : ℝ) :
    ComplexPencilCert.m13
       (ComplexPencilCert.diag1 (ComplexPencilLink.sq a0)
        (ComplexPencilLink.sq a1) (ComplexPencilLink.sq a2)
        B (qval lam) lam.re)
       (ComplexPencilCert.diag3 (ComplexPencilLink.sq a0)
        (ComplexPencilLink.sq a1) (ComplexPencilLink.sq a2)
        B (qval lam) lam.re)
       (ventry lam a0 a2) =
     ComplexPencilCert.minorDirect (ComplexPencilLink.sq a2)
        (ComplexPencilLink.sq a0) (ComplexPencilLink.sq a1)
        B (qval lam) lam.re := by
  unfold ComplexPencilCert.m13 ComplexPencilCert.minorDirect
  rw [sq_ventry]
  unfold ComplexPencilCert.diag1 ComplexPencilCert.diag2
     ComplexPencilCert.diag3
  ring

theorem minor23_actual
    (lam a0 a1 a2 : ℂ) (B : ℝ) :
    ComplexPencilCert.m23
       (ComplexPencilCert.diag2 (ComplexPencilLink.sq a0)
        (ComplexPencilLink.sq a1) (ComplexPencilLink.sq a2)
        B (qval lam) lam.re)
       (ComplexPencilCert.diag3 (ComplexPencilLink.sq a0)
        (ComplexPencilLink.sq a1) (ComplexPencilLink.sq a2)
        B (qval lam) lam.re)
       (wentry lam a1 a2) =
     ComplexPencilCert.minorDirect (ComplexPencilLink.sq a1)
        (ComplexPencilLink.sq a2) (ComplexPencilLink.sq a0)
        B (qval lam) lam.re := by
  unfold ComplexPencilCert.m23 ComplexPencilCert.minorDirect
  rw [sq_wentry]
  unfold ComplexPencilCert.diag1 ComplexPencilCert.diag2
     ComplexPencilCert.diag3
  ring

theorem q3_actual_nonneg
    (lam a0 a1 a2 b0 b1 b2 : ℂ) (B : ℝ)
    (hB : 0 ≤ B)
    (h3B : 0 ≤ 3*B-4)
    (hp : 0 ≤ ComplexPencilCert.h B (qval lam) +
              ComplexPencilCert.v lam.re)
    (hm : 0 ≤ ComplexPencilCert.h B (qval lam) -
              ComplexPencilCert.v lam.re)
    (hF : 0 ≤ (3*(B-qval lam)-1)^2 -
              12*(qval lam - lam.re*lam.re)) :
    0 ≤ ComplexPencilCert.Q3
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
       (wentry lam a1 a2) b0 b1 b2 := by
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
  exact ComplexPencilCert.hermitian3_nonneg
     d1 d2 d3 u v w b0 b1 b2
     hd1 hd2 hd3 h12 h13 h23 hdet

theorem trilinear_squared_upper
    (lam a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℂ) (B : ℝ)
    (hB : 0 ≤ B)
    (h3B : 0 ≤ 3*B-4)
    (hp : 0 ≤ ComplexPencilCert.h B (qval lam) +
              ComplexPencilCert.v lam.re)
    (hm : 0 ≤ ComplexPencilCert.h B (qval lam) -
              ComplexPencilCert.v lam.re)
    (hF : 0 ≤ (3*(B-qval lam)-1)^2 -
              12*(qval lam - lam.re*lam.re)) :
    ComplexPencilLink.sq
       (c0*(t0 lam a1 a2 b1 b2)+
        c1*(t1 lam a0 a2 b0 b2)+
        c2*(t2 lam a0 a1 b0 b1)) ≤
      B*(rowSq a0 a1 a2)*
       (rowSq b0 b1 b2)*(rowSq c0 c1 c2) := by
  have hq := q3_actual_nonneg lam a0 a1 a2 b0 b1 b2
    B hB h3B hp hm hF
  have hbridge := actual_complement
     lam a0 a1 a2 b0 b1 b2 B
  have hnorm :
    ComplexPencilLink.sq (t0 lam a1 a2 b1 b2)+
    ComplexPencilLink.sq (t1 lam a0 a2 b0 b2)+
    ComplexPencilLink.sq (t2 lam a0 a1 b0 b1) ≤
      B*(rowSq a0 a1 a2)*(rowSq b0 b1 b2) := by
    rw [← hbridge] at hq
    linarith
  have hc : 0 ≤ rowSq c0 c1 c2 := by
    unfold rowSq
    have h0 := ComplexPencilLink.sq_nonneg c0
    have h1 := ComplexPencilLink.sq_nonneg c1
    have h2 := ComplexPencilLink.sq_nonneg c2
    linarith
  calc
    ComplexPencilLink.sq
       (c0*(t0 lam a1 a2 b1 b2)+
        c1*(t1 lam a0 a2 b0 b2)+
        c2*(t2 lam a0 a1 b0 b1)) ≤
      (rowSq c0 c1 c2)*
        (ComplexPencilLink.sq (t0 lam a1 a2 b1 b2)+
         ComplexPencilLink.sq (t1 lam a0 a2 b0 b2)+
         ComplexPencilLink.sq (t2 lam a0 a1 b0 b1)) := by
           exact ComplexPencilLink.complex_three_cauchy
             c0 c1 c2 _ _ _
    _ ≤ (rowSq c0 c1 c2)*
          (B*(rowSq a0 a1 a2)*(rowSq b0 b1 b2)) :=
        mul_le_mul_of_nonneg_left hnorm hc
    _ = B*(rowSq a0 a1 a2)*
       (rowSq b0 b1 b2)*(rowSq c0 c1 c2) := by ring

def permanent3
    (a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℂ) : ℂ :=
  a0*b1*c2+a0*b2*c1+a1*b0*c2+
  a1*b2*c0+a2*b0*c1+a2*b1*c0

def determinant3
    (a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℂ) : ℂ :=
  a0*b1*c2+a1*b2*c0+a2*b0*c1-
  a0*b2*c1-a1*b0*c2-a2*b1*c0

theorem trilinear_pencil_identity
    (lam a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℂ) :
    c0*(t0 lam a1 a2 b1 b2)+
    c1*(t1 lam a0 a2 b0 b2)+
    c2*(t2 lam a0 a1 b0 b1) =
    permanent3 a0 a1 a2 b0 b1 b2 c0 c1 c2 +
      lam*determinant3 a0 a1 a2 b0 b1 b2 c0 c1 c2 := by
  unfold t0 t1 t2 p0 q0 p1 q1 p2 q2
    alpha beta permanent3 determinant3
  ring

theorem pencil_squared_upper
    (lam a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℂ) (B : ℝ)
    (hB : 0 ≤ B)
    (h3B : 0 ≤ 3*B-4)
    (hp : 0 ≤ ComplexPencilCert.h B (qval lam) +
              ComplexPencilCert.v lam.re)
    (hm : 0 ≤ ComplexPencilCert.h B (qval lam) -
              ComplexPencilCert.v lam.re)
    (hF : 0 ≤ (3*(B-qval lam)-1)^2 -
              12*(qval lam - lam.re*lam.re)) :
    ComplexPencilLink.sq
      (permanent3 a0 a1 a2 b0 b1 b2 c0 c1 c2 +
       lam*determinant3 a0 a1 a2 b0 b1 b2 c0 c1 c2) ≤
        B*(rowSq a0 a1 a2)*(rowSq b0 b1 b2)*
          (rowSq c0 c1 c2) := by
  rw [← trilinear_pencil_identity]
  exact trilinear_squared_upper
    lam a0 a1 a2 b0 b1 b2 c0 c1 c2 B hB h3B hp hm hF

theorem lens_preconditions (lam : ℂ)
    (hlens : qval lam + 2*|lam.re| ≤ (1/3 : ℝ)) :
    0 ≤ (4/3:ℝ) ∧
    0 ≤ 3*(4/3:ℝ)-4 ∧
    0 ≤ ComplexPencilCert.h (4/3:ℝ) (qval lam) +
            ComplexPencilCert.v lam.re ∧
    0 ≤ ComplexPencilCert.h (4/3:ℝ) (qval lam) -
            ComplexPencilCert.v lam.re ∧
    0 ≤ (3*((4/3:ℝ)-qval lam)-1)^2 -
            12*(qval lam-lam.re*lam.re) := by
  have hx1 := le_abs_self lam.re
  have hx2 := neg_le_abs lam.re
  have hq : qval lam ≤ (1/3:ℝ) := by
    linarith [abs_nonneg lam.re]
  have hRe : lam.re*lam.re ≤ qval lam := by
    unfold qval ComplexPencilLink.sq
    nlinarith [mul_self_nonneg lam.im]
  have hbig : 2 ≤ 3*((4/3:ℝ)-qval lam)-1 := by
    linarith
  have hProd :
    0 ≤ (3*((4/3:ℝ)-qval lam)-1-2) *
        (3*((4/3:ℝ)-qval lam)-1+2) :=
    mul_nonneg (by linarith) (by linarith)
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · unfold ComplexPencilCert.h ComplexPencilCert.v
    linarith
  constructor
  · unfold ComplexPencilCert.h ComplexPencilCert.v
    linarith
  · nlinarith [hProd, hq, hRe]

theorem sharp_complex_lens_upper
    (lam a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℂ)
    (hlens : qval lam + 2*|lam.re| ≤ (1/3:ℝ)) :
    ComplexPencilLink.sq
      (permanent3 a0 a1 a2 b0 b1 b2 c0 c1 c2 +
       lam*determinant3 a0 a1 a2 b0 b1 b2 c0 c1 c2) ≤
      (4/3:ℝ)*(rowSq a0 a1 a2)*(rowSq b0 b1 b2)*
        (rowSq c0 c1 c2) := by
  obtain ⟨hB, h3B, hp, hm, hF⟩ :=
     lens_preconditions lam hlens
  exact pencil_squared_upper
    lam a0 a1 a2 b0 b1 b2 c0 c1 c2 (4/3:ℝ)
    hB h3B hp hm hF

def universalLensBound (lam : ℂ) : Prop :=
  ∀ a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℂ,
    ComplexPencilLink.sq
      (permanent3 a0 a1 a2 b0 b1 b2 c0 c1 c2 +
       lam*determinant3 a0 a1 a2 b0 b1 b2 c0 c1 c2) ≤
       (4/3:ℝ)*(rowSq a0 a1 a2)*(rowSq b0 b1 b2)*
        (rowSq c0 c1 c2)

theorem sharp_complex_lens_iff (lam : ℂ) :
    universalLensBound lam ↔
      qval lam + 2*|lam.re| ≤ (1/3:ℝ) := by
  constructor
  · intro hall
    have heven := hall 1 0 0 0 1 0 0 0 1
    have hodd := hall 1 0 0 0 0 1 0 1 0
    have hplus : ComplexPencilLink.sq (1+lam) ≤ (4/3:ℝ) := by
      simpa [permanent3, determinant3, rowSq, ComplexPencilLink.sq] using heven
    have hminus : ComplexPencilLink.sq (1-lam) ≤ (4/3:ℝ) := by
      simpa [permanent3, determinant3, rowSq,
        ComplexPencilLink.sq, sub_eq_add_neg] using hodd
    change ComplexPencilLink.sq (beta lam) ≤ (4/3:ℝ) at hplus
    change ComplexPencilLink.sq (alpha lam) ≤ (4/3:ℝ) at hminus
    rw [sq_beta] at hplus
    rw [sq_alpha] at hminus
    have hl : 2*lam.re ≤ (1/3:ℝ)-qval lam := by
      unfold qval
      linarith
    have hr : -2*lam.re ≤ (1/3:ℝ)-qval lam := by
      unfold qval
      linarith
    have habs : 2*|lam.re| ≤ (1/3:ℝ)-qval lam := by
      rcases le_total (0:ℝ) lam.re with hx | hx
      · rw [abs_of_nonneg hx]
        linarith
      · rw [abs_of_nonpos hx]
        linarith
    linarith
  · intro hlens
    intro a0 a1 a2 b0 b1 b2 c0 c1 c2
    exact sharp_complex_lens_upper
      lam a0 a1 a2 b0 b1 b2 c0 c1 c2 hlens

theorem coefficient_four_thirds_is_sharp (lam : ℂ) (B : ℝ)
    (hAll : ∀ a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℂ,
      ComplexPencilLink.sq
        (permanent3 a0 a1 a2 b0 b1 b2 c0 c1 c2 +
         lam*determinant3 a0 a1 a2 b0 b1 b2 c0 c1 c2) ≤
      B*(rowSq a0 a1 a2)*(rowSq b0 b1 b2)*
        (rowSq c0 c1 c2)) :
    (4/3:ℝ) ≤ B := by
  have h := hAll 1 1 1 1 1 1 1 1 1
  norm_num [permanent3, determinant3, rowSq,
    ComplexPencilLink.sq] at h
  nlinarith

end
end ComplexPencilMain

#print axioms ComplexPencilMain.sharp_complex_lens_iff
#print axioms ComplexPencilMain.coefficient_four_thirds_is_sharp
#print axioms ComplexPencilMain.pencil_squared_upper
#print axioms ComplexPencilCert.determinant_global_identity
#print axioms ComplexPencilCert.hermitian3_nonneg
