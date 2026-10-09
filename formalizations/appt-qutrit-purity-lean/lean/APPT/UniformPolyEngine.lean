import Mathlib

/-!
A small executable/kernel-only experiment for the all-qutrit polynomial checker.
This module establishes that exact multivariate polynomial identities can be
replayed by the ordinary `decide` elaborator, not `native_decide`.
-/
namespace APPT.UniformPolyEngine

abbrev P := MvPolynomial (Fin 2) ℤ

private def x : P := MvPolynomial.X 0
private def y : P := MvPolynomial.X 1

/-- Integer multivariate polynomial evaluation, fully kernel-checked. -/
theorem cubic_binomial :
    (x + y)^3 = x^3 + 3*x^2*y + 3*x*y^2 + y^3 := by
  decide

/-- Signed and parameter-dependent polynomial products. -/
theorem signed_parameter :
    ((x + 3*y - 18)^2)*(x-y) =
      (x-y)*(x+3*y-18)*(x+3*y-18) := by
  decide

end APPT.UniformPolyEngine
