import APPTReview.RectangularMaximum
import APPTReview.Counterexample1038

open scoped BigOperators ComplexOrder
namespace APPTReview

/-- This is an exact unrestricted maximum, not only the previous attainment test. -/
theorem rectangular_4_58_maximum : IsGreatest (apptPurityValues 4 58) (2/435:ℝ) := by
  convert appt_rectangular_maximum_formula (m:=4) (n:=58) (by decide) (by decide) using 1 <;> norm_num

/-- An odd-parity instance checks the exact ceiling-rank formula. -/
theorem rectangular_4_59_maximum : IsGreatest (apptPurityValues 4 59) (887/196249:ℝ) := by
  convert appt_rectangular_maximum_formula (m:=4) (n:=59) (by decide) (by decide) using 1 <;> norm_num

/-- The rectangular cutoff cannot simply be omitted: an already kernel-verified
actual APPT density exceeds the plateau branch in smaller aspect dimensions. -/
theorem rectangular_cutoff_cannot_be_dropped :
    APPT.Quantum.IsDensity counterexample1038 ∧
    APPT.Quantum.AbsolutelyPPT counterexample1038 ∧
    roundedPlateauPurity 10 38 < APPT.Quantum.purity counterexample1038 := by
  refine ⟨counterexample1038_isDensity,counterexample1038_absolutelyPPT,?_⟩
  rw [counterexample1038_purity,roundedPlateauPurity_formula (by decide) (by decide)]
  norm_num

end APPTReview
