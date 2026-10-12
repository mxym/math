import ErdosSimilarityGrowingGaps.AsymptoticProducts

namespace ErdosSimilarityGrowingGaps

open Filter Topology Asymptotics

/-- A nonnegative quantity bounded below by one inherits little-o from its
square.  This is useful for routing coefficients, whose natural powers are
at least one. -/
theorem littleO_of_sq_of_one_le
    {ι : Type*} {l : Filter ι} (A U : ι → ℝ)
    (hA2 : (fun i => (A i)^2) =o[l] U)
    (hA1 : ∀ᶠ i in l, 1 ≤ A i)
    (hU : ∀ᶠ i in l, 0 ≤ U i) :
    A =o[l] U := by
  apply IsLittleO.of_bound
  intro c hc
  have hsmall := hA2.bound hc
  filter_upwards [hsmall, hA1, hU] with i hi hAi hUi
  have hsq : A i ≤ (A i)^2 := by nlinarith
  have hi' : (A i)^2 ≤ c * U i := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (A i)),
      Real.norm_eq_abs, abs_of_nonneg hUi, mul_one] using hi
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ A i),
    Real.norm_eq_abs, abs_of_nonneg hUi]
  exact hsq.trans hi'

/-- The square of a sum is little-o when both summands have little-o squares.
The estimate is the elementary inequality `(a+b)^2 ≤ 2a^2+2b^2`. -/
theorem sq_add_littleO_of_sq
    {ι : Type*} {l : Filter ι} (A B U : ι → ℝ)
    (hA2 : (fun i => (A i)^2) =o[l] U)
    (hB2 : (fun i => (B i)^2) =o[l] U)
    (hA : ∀ᶠ i in l, 0 ≤ A i)
    (hB : ∀ᶠ i in l, 0 ≤ B i)
    (hU : ∀ᶠ i in l, 0 ≤ U i) :
    (fun i => (A i + B i)^2) =o[l] U := by
  apply IsLittleO.of_bound
  intro c hc
  have hAc := hA2.bound (by linarith : 0 < c / 4)
  have hBc := hB2.bound (by linarith : 0 < c / 4)
  filter_upwards [hAc, hBc, hA, hB, hU] with i hAi hBi hAi0 hBi0 hUi
  have hAineq : (A i)^2 ≤ (c / 4) * U i := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (A i)),
      Real.norm_eq_abs, abs_of_nonneg hUi, mul_one] using hAi
  have hBineq : (B i)^2 ≤ (c / 4) * U i := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (B i)),
      Real.norm_eq_abs, abs_of_nonneg hUi, mul_one] using hBi
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (A i + B i)),
    Real.norm_eq_abs, abs_of_nonneg hUi]
  nlinarith [sq_nonneg (A i - B i), hAineq, hBineq]

/-- Adding a fixed nonnegative constant preserves a square little-o bound. -/
theorem sq_add_const_littleO
    {ι : Type*} {l : Filter ι} (A U : ι → ℝ) (C : ℝ)
    (hA2 : (fun i => (A i)^2) =o[l] U)
    (hA : ∀ᶠ i in l, 0 ≤ A i) (hUlim : Tendsto U l atTop)
    (hC : 0 ≤ C) :
    (fun i => (A i + C)^2) =o[l] U := by
  have hC2 : (fun _ : ι => C^2) =o[l] U := by
    exact (isLittleO_const_id_atTop (C^2)).comp_tendsto hUlim
  exact sq_add_littleO_of_sq A (fun _ => C) U hA2 hC2 hA
    (Filter.Eventually.of_forall (fun _ => hC))
    (hUlim.eventually (eventually_ge_atTop 0))

end ErdosSimilarityGrowingGaps
