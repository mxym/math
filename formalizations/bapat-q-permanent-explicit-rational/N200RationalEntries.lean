import N200EntryBounds
import ConstantParameters

set_option autoImplicit false
open scoped ComplexOrder

namespace BapatExplicit
open BapatRankTwo BapatRankTwo.Exact BapatRankTwo.N200

noncomputable def explicitMatrix : Matrix (Fin 200) (Fin 200) ℂ :=
  perturb matrix (epsilon : ℝ)

theorem toComplex_re (z : GI) : (toComplex z).re = (z.re : ℝ) := by
  simp [toComplex, Zsqrtd.lift_apply_apply]

theorem toComplex_im (z : GI) : (toComplex z).im = (z.im : ℝ) := by
  simp [toComplex, Zsqrtd.lift_apply_apply]

noncomputable def rationalReal (i j : Fin 200) : ℚ :=
  let x := vectorAt vectors i.val
  let y := vectorAt vectors j.val
  (x.1.re : ℚ) * (y.1.re : ℚ) + (x.1.im : ℚ) * (y.1.im : ℚ) +
    (x.2.re : ℚ) * (y.2.re : ℚ) + (x.2.im : ℚ) * (y.2.im : ℚ)

noncomputable def rationalImag (i j : Fin 200) : ℚ :=
  let x := vectorAt vectors i.val
  let y := vectorAt vectors j.val
  (x.1.im : ℚ) * (y.1.re : ℚ) - (x.1.re : ℚ) * (y.1.im : ℚ) +
    ((x.2.im : ℚ) * (y.2.re : ℚ) - (x.2.re : ℚ) * (y.2.im : ℚ))

theorem matrix_rational_entries (i j : Fin 200) :
    matrix i j = (rationalReal i j : ℂ) + (rationalImag i j : ℂ) * Complex.I := by
  apply Complex.ext <;>
    simp [matrix, gram, a, b, rationalReal, rationalImag, toComplex_re, toComplex_im,
      Complex.mul_re, Complex.mul_im] <;> ring

/-- Every entry of the specified positive-definite matrix has rational real
and imaginary parts, using the very same CSV and rational epsilon. -/
theorem explicitMatrix_rational_entries (i j : Fin 200) :
    explicitMatrix i j =
      ((rationalReal i j + if i = j then epsilon else 0 : ℚ) : ℂ) +
        (rationalImag i j : ℂ) * Complex.I := by
  change matrix i j + (Matrix.diagonal (fun _ => ((epsilon : ℝ) : ℂ))) i j = _
  rw [matrix_rational_entries]
  by_cases hij : i = j
  · subst j
    simp [Matrix.diagonal_apply]
    ring
  · simp [Matrix.diagonal_apply, hij]

end BapatExplicit
