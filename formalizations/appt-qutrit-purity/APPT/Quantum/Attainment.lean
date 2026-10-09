import APPT.Quantum.ShortAttainment
import APPT.Quantum.LongAttainment
open scoped BigOperators ComplexOrder
open Matrix
namespace APPT.Quantum

noncomputable def targetPurity (n : ℕ) : ℝ :=
  if n ≤ 8 then (3*(n : ℝ)+8)/(3*(n : ℝ)+2)^2 else 3/(8*(n : ℝ))

/-- Both branches of the desired maximum are attained by actual APPT density matrices.
This is the complete lower-bound/attainment direction, not the upper bound. -/
theorem targetPurity_attained (n : ℕ) (hn : 3 ≤ n) :
    ∃ A : Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ,
      IsDensity A ∧ AbsolutelyPPT A ∧ purity A = targetPurity n := by
  have hn0 : 0 < n := by omega
  by_cases h : n ≤ 8
  · simpa [targetPurity,h] using exists_shortState n hn0
  · refine ⟨longState n,longState_isDensity n hn0,longState_absolutelyPPT n,?_⟩
    simpa [targetPurity,h] using longState_purity n hn0

end APPT.Quantum
