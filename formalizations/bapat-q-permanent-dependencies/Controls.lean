import PositiveDefiniteViolation

namespace BapatBounds

theorem constant_polynomial_control (q : ℝ) :
    realPolynomial (fun _ : Unit => 0) (fun _ => 7) q = 7 ∧
      realDerivative (fun _ : Unit => 0) (fun _ => 7) q = 0 := by
  simp [realPolynomial, realDerivative]

theorem linear_reverse_control :
    realPolynomial (fun _ : Unit => 1) (fun _ => -1) (7 / 8 : ℝ) >
      realPolynomial (fun _ : Unit => 1) (fun _ => -1) 1 := by
  norm_num [realPolynomial]

theorem omitted_negative_endpoint_control :
    (∀ q : ℝ, HasDerivAt (fun x : ℝ => x) 1 q) ∧
    (∀ q : ℝ, |(1 : ℝ) - 1| ≤ 1 * (1 - q) ↔ q ≤ 1) ∧
    ¬((1 : ℝ) < 1 - 1 / (8 * 1)) := by
  refine ⟨fun q => hasDerivAt_id q, ?_, ?_⟩
  · intro q
    simp
  · norm_num

end BapatBounds
