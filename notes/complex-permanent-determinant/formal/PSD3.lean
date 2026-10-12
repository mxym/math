import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Basic.Complex.Basic

/-!
# A concrete Hermitian 3x3 principal-minor criterion

A fully quantified proof over the actual complex field,
using a division-free polynomial Cholesky identity and
separate singular-pivot cases. This lemma connects
Hermitian minor certificates to a vector quadratic-form
inequality; it is NOT an assumption of matrix PSD.
-/

open scoped ComplexConjugate
namespace ComplexPencilCert
noncomputable section

def sq (z : ℂ) : ℝ := z.re ^ 2 + z.im ^ 2

private theorem sq_nonneg (z : ℂ) : 0 ≤ sq z := by
  unfold sq
  positivity

private theorem sq_zero (z : ℂ) (h : sq z = 0) : z = 0 := by
  have h1 : z.re = 0 := by
    have h0 := sq_nonneg z
    unfold sq at h
    nlinarith [sq_nonneg z]
  have h2 : z.im = 0 := by
    unfold sq at h
    nlinarith [sq_nonneg z]
  exact Complex.ext h1 h2

def Q2 (d2 d3 : ℝ) (w b2 b3 : ℂ) : ℝ :=
  d2 * sq b2 + d3 * sq b3 +
  2 * (((conj b2) * w * b3).re)

def Q3 (d1 d2 d3 : ℝ) (u v w b1 b2 b3 : ℂ) : ℝ :=
  d1 * sq b1 + d2 * sq b2 + d3 * sq b3 +
  2 * (((conj b1) * u * b2).re +
       ((conj b1) * v * b3).re +
       ((conj b2) * w * b3).re)

def m12 (d1 d2 : ℝ) (u : ℂ) : ℝ := d1 * d2 - sq u
def m13 (d1 d3 : ℝ) (v : ℂ) : ℝ := d1 * d3 - sq v
def m23 (d2 d3 : ℝ) (w : ℂ) : ℝ := d2 * d3 - sq w

def det3 (d1 d2 d3 : ℝ) (u v w : ℂ) : ℝ :=
  d1 * d2 * d3 - d1 * sq w - d2 * sq v - d3 * sq u +
  2 * ((u * w * (conj v)).re)

private theorem schur2 (d2 d3 : ℝ) (w b2 b3 : ℂ) :
  d2 * Q2 d2 d3 w b2 b3 =
    sq ((d2 : ℂ) * b2 + w * b3) +
    m23 d2 d3 w * sq b3 := by
  simp [Q2, sq, m23, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.conj_re,
    Complex.conj_im]
  ring

private theorem schur1 (d1 d2 d3 : ℝ) (u v w b1 b2 b3 : ℂ) :
  d1 * Q3 d1 d2 d3 u v w b1 b2 b3 =
    sq ((d1 : ℂ) * b1 + u * b2 + v * b3) +
    m12 d1 d2 u * sq b2 + m13 d1 d3 v * sq b3 +
    2 * (((conj b2) * ((d1 : ℂ) * w - (conj u) * v) * b3).re) := by
  simp [Q3, sq, m12, m13, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

private theorem minor_det3 (d1 d2 d3 : ℝ) (u v w : ℂ) :
  m12 d1 d2 u * m13 d1 d3 v -
    sq ((d1 : ℂ) * w - (conj u) * v) =
  d1 * det3 d1 d2 d3 u v w := by
  simp [det3, m12, m13, sq,
    Complex.mul_re, Complex.mul_im, Complex.sub_re,
    Complex.sub_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

private theorem sq_cross (m : ℝ) (b2 b3 alpha : ℂ) :
  sq ((m : ℂ)*b2 + alpha*b3) =
    m*m*sq b2 + sq alpha*sq b3 +
        2*m*((conj b2)*alpha*b3).re := by
  simp [sq, Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

private theorem cholesky_polynomial
    (d1 d2 d3 : ℝ) (u v w b1 b2 b3 : ℂ) :
  d1 * m12 d1 d2 u * Q3 d1 d2 d3 u v w b1 b2 b3 =
    m12 d1 d2 u * sq ((d1 : ℂ)*b1 + u*b2 + v*b3) +
    sq (((m12 d1 d2 u : ℝ) : ℂ)*b2 +
         ((d1 : ℂ)*w-(conj u)*v)*b3) +
    d1*det3 d1 d2 d3 u v w*sq b3 := by
  let m : ℝ := m12 d1 d2 u
  let a : ℂ := (d1 : ℂ)*w-(conj u)*v
  have hs := schur1 d1 d2 d3 u v w b1 b2 b3
  have hd := minor_det3 d1 d2 d3 u v w
  have hc := sq_cross m b2 b3 a
  change m * m13 d1 d3 v - sq a =
      d1*det3 d1 d2 d3 u v w at hd
  change d1 * Q3 d1 d2 d3 u v w b1 b2 b3 =
    sq ((d1 : ℂ)*b1 + u*b2 + v*b3) +
    m*sq b2 + m13 d1 d3 v*sq b3 +
    2*((conj b2)*a*b3).re at hs
  change
    d1 * m * Q3 d1 d2 d3 u v w b1 b2 b3 =
    m * sq ((d1 : ℂ)*b1 + u*b2 + v*b3) +
    sq ((m : ℂ)*b2+a*b3) +
    d1 * det3 d1 d2 d3 u v w*sq b3
  calc
    _ = m * (d1 * Q3 d1 d2 d3 u v w b1 b2 b3) := by ring
    _ = m*(sq ((d1 : ℂ)*b1 + u*b2 + v*b3) +
      m*sq b2 + m13 d1 d3 v*sq b3 +
      2*((conj b2)*a*b3).re) := by rw [hs]
    _ = m * sq ((d1 : ℂ)*b1 + u*b2 + v*b3) +
        sq ((m : ℂ)*b2+a*b3) +
        (m*m13 d1 d3 v - sq a)*sq b3 := by rw [hc]; ring
    _ = m * sq ((d1 : ℂ)*b1 + u*b2 + v*b3) +
        sq ((m : ℂ)*b2+a*b3) +
        d1*det3 d1 d2 d3 u v w*sq b3 := by rw [hd]

/- The entire 3x3 Hermitian quadratic form is nonnegative if
   its three diagonal entries, three 2x2 principal minors,
   and its full determinant are nonnegative. -/
theorem hermitian3_nonneg
    (d1 d2 d3 : ℝ) (u v w b1 b2 b3 : ℂ)
    (h1 : 0 ≤ d1) (h2 : 0 ≤ d2) (h3 : 0 ≤ d3)
    (h12 : 0 ≤ m12 d1 d2 u)
    (h13 : 0 ≤ m13 d1 d3 v)
    (h23 : 0 ≤ m23 d2 d3 w)
    (hd : 0 ≤ det3 d1 d2 d3 u v w) :
    0 ≤ Q3 d1 d2 d3 u v w b1 b2 b3 := by
  by_cases h1pos : 0 < d1
  · by_cases hmpos : 0 < m12 d1 d2 u
    · have hmult := cholesky_polynomial d1 d2 d3 u v w b1 b2 b3
      have hnonneg : 0 ≤ d1 * m12 d1 d2 u *
                           Q3 d1 d2 d3 u v w b1 b2 b3 := by
        rw [hmult]
        have hp1 : 0 ≤ m12 d1 d2 u *
          sq ((d1 : ℂ)*b1 + u*b2 + v*b3) :=
            mul_nonneg h12 (sq_nonneg _)
        have hp3 : 0 ≤ d1 * det3 d1 d2 d3 u v w * sq b3 :=
            mul_nonneg (mul_nonneg h1 hd) (sq_nonneg _)
        nlinarith [sq_nonneg
          (((m12 d1 d2 u : ℝ) : ℂ)*b2 +
          ((d1 : ℂ)*w-(conj u)*v)*b3)]
      have hh : 0 < d1 * m12 d1 d2 u := mul_pos h1pos hmpos
      exact nonneg_of_mul_nonneg_left (by simpa [mul_comm] using hnonneg) hh
    · have hmzero : m12 d1 d2 u = 0 := le_antisymm (le_of_not_gt hmpos) h12
      have hh := minor_det3 d1 d2 d3 u v w
      rw [hmzero] at hh
      have hz : sq ((d1 : ℂ)*w-(conj u)*v) = 0 := by
        have hp := mul_nonneg (le_of_lt h1pos) hd
        nlinarith [sq_nonneg ((d1 : ℂ)*w-(conj u)*v)]
      have hcross : (d1 : ℂ)*w-(conj u)*v = 0 := sq_zero _ hz
      have hs := schur1 d1 d2 d3 u v w b1 b2 b3
      rw [hmzero, hcross] at hs
      simp only [zero_mul, mul_zero, add_zero,
        Complex.zero_re] at hs
      have hnn : 0 ≤ d1 * Q3 d1 d2 d3 u v w b1 b2 b3 := by
        rw [hs]
        have hp : 0 ≤ (m13 d1 d3 v) * sq b3 :=
          mul_nonneg h13 (sq_nonneg _)
        nlinarith [sq_nonneg
          ((d1 : ℂ)*b1+u*b2+v*b3)]
      exact nonneg_of_mul_nonneg_left (by simpa [mul_comm] using hnn) h1pos
  · have h1zero : d1 = 0 := le_antisymm (le_of_not_gt h1pos) h1
    have hu : u = 0 := by
      have hh := h12
      rw [h1zero] at hh
      simp [m12] at hh
      exact sq_zero u (le_antisymm (by linarith [hh]) (sq_nonneg u))
    have hv : v = 0 := by
      have hh := h13
      rw [h1zero] at hh
      simp [m13] at hh
      exact sq_zero v (le_antisymm (by linarith [hh]) (sq_nonneg v))
    simp only [h1zero, hu, hv] at *
    have hQ2 : 0 ≤ Q2 d2 d3 w b2 b3 := by
      by_cases h2pos : 0 < d2
      · have hs := schur2 d2 d3 w b2 b3
        have hnn : 0 ≤ d2 * Q2 d2 d3 w b2 b3 := by
          rw [hs]
          have hp : 0 ≤ m23 d2 d3 w * sq b3 :=
            mul_nonneg h23 (sq_nonneg _)
          nlinarith [sq_nonneg ((d2 : ℂ)*b2+w*b3)]
        exact nonneg_of_mul_nonneg_left (by simpa [mul_comm] using hnn) h2pos
      · have h2zero : d2 = 0 := le_antisymm (le_of_not_gt h2pos) h2
        have hw : w = 0 := by
          have hh := h23
          rw [h2zero] at hh
          simp [m23] at hh
          exact sq_zero w (le_antisymm (by linarith [hh]) (sq_nonneg w))
        simpa [Q2, h2zero, hw] using mul_nonneg h3 (sq_nonneg b3)

    simpa [Q3, Q2] using hQ2

end
end ComplexPencilCert
