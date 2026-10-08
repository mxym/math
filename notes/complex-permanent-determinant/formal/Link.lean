import HermitianCertificate
import PSD3

open scoped ComplexConjugate
namespace ComplexPencilLink

def sq (z : ℂ) : ℝ := z.re * z.re + z.im * z.im

theorem sq_nonneg (z : ℂ) : 0 ≤ sq z := by
  unfold sq
  exact add_nonneg (mul_self_nonneg z.re) (mul_self_nonneg z.im)

theorem sq_mul (a b : ℂ) :
    sq (a*b) = sq a * sq b := by
  simp [sq, Complex.mul_re, Complex.mul_im]
  ring

theorem sq_two_terms (p q x y : ℂ) :
    sq (p*x+q*y) =
      sq p * sq x + sq q * sq y +
        2*((conj x)*(conj p)*q*y).re := by
  simp [sq, Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.conj_re, Complex.conj_im]
  ring

def threeOutputNorm
   (p q r s t u : ℂ) (b0 b1 b2 : ℂ) : ℝ :=
  sq (p*b1+q*b2) + sq (r*b0+s*b2) + sq (t*b0+u*b1)

def hermitianQuadratic
  (d1 d2 d3 : ℝ) (u v w b0 b1 b2 : ℂ) : ℝ :=
  d1*sq b0+d2*sq b1+d3*sq b2 +
  2*((conj b0*u*b1).re+(conj b0*v*b2).re+
     (conj b1*w*b2).re)

theorem zero_diagonal_norm_complement
    (B T : ℝ) (p q r s t u b0 b1 b2 : ℂ) :
    B*T*(sq b0+sq b1+sq b2) -
        threeOutputNorm p q r s t u b0 b1 b2 =
    hermitianQuadratic
       (B*T-(sq r+sq t))
       (B*T-(sq p+sq u))
       (B*T-(sq q+sq s))
       (-(conj t*u))
       (-(conj r*s))
       (-(conj p*q))
       b0 b1 b2 := by
  unfold threeOutputNorm hermitianQuadratic
  rw [sq_two_terms p q b1 b2,
      sq_two_terms r s b0 b2,
      sq_two_terms t u b0 b1]
  simp only [neg_mul, mul_neg, Complex.neg_re, mul_assoc]
  ring

theorem quad_as_PSD3
    (d1 d2 d3 : ℝ) (u v w b0 b1 b2 : ℂ) :
    hermitianQuadratic d1 d2 d3 u v w b0 b1 b2 =
    ComplexPencilCert.Q3 d1 d2 d3 u v w b0 b1 b2 := by
  unfold hermitianQuadratic ComplexPencilCert.Q3 sq
    ComplexPencilCert.sq
  ring

theorem complex_three_lagrange
    (c0 c1 c2 t0 t1 t2 : ℂ) :
   (sq c0+sq c1+sq c2)*(sq t0+sq t1+sq t2) -
      sq (c0*t0+c1*t1+c2*t2) =
   sq (c0*conj t1-c1*conj t0) +
   sq (c0*conj t2-c2*conj t0) +
   sq (c1*conj t2-c2*conj t1) := by
  simp [sq, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.conj_re, Complex.conj_im]
  ring

theorem complex_three_cauchy
    (c0 c1 c2 t0 t1 t2 : ℂ) :
    sq (c0*t0+c1*t1+c2*t2) ≤
      (sq c0+sq c1+sq c2)*(sq t0+sq t1+sq t2) := by
  have h := complex_three_lagrange c0 c1 c2 t0 t1 t2
  have h0 := sq_nonneg (c0*conj t1-c1*conj t0)
  have h1 := sq_nonneg (c0*conj t2-c2*conj t0)
  have h2 := sq_nonneg (c1*conj t2-c2*conj t1)
  linarith

end ComplexPencilLink
