import HydrologyTree.LinearForcedODE
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Explicit classical scalar solution, using the actual interval integral.
The formula is defined for both time orientations and all real decay rates. -/
open MeasureTheory
noncomputable section
namespace HydrologyTree

def scalarForcedSolution (r : ℝ) (u : ℝ → ℝ) (a y0 s : ℝ) : ℝ :=
  Real.exp (-r*(s-a)) * (y0 + ∫ v in a..s, Real.exp (r*(v-a))*u v)

@[simp] theorem scalarForcedSolution_initial (r : ℝ) (u : ℝ → ℝ) (a y0 : ℝ) :
    scalarForcedSolution r u a y0 a=y0 := by simp [scalarForcedSolution]

lemma scalarIntegratingFactor_cancel (r a s : ℝ) :
    Real.exp (-r*(s-a))*Real.exp (r*(s-a))=1 := by
  rw [← Real.exp_add]
  convert Real.exp_zero using 1 <;> ring

/-- The derivative is the actual inhomogeneous scalar differential equation. -/
theorem scalarForcedSolution_hasDerivAt (r : ℝ) (u : ℝ → ℝ) (hu : Continuous u)
    (a y0 s : ℝ) :
    HasDerivAt (scalarForcedSolution r u a y0)
      (-r*scalarForcedSolution r u a y0 s + u s) s := by
  have hc : Continuous (fun v : ℝ => Real.exp (r*(v-a))*u v) := by fun_prop
  have hI := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable a s)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have he : HasDerivAt (fun v : ℝ => Real.exp (-r*(v-a)))
      (Real.exp (-r*(s-a))*(-r)) s := by
    convert (((hasDerivAt_id s).sub_const a).const_mul (-r)).exp using 1 <;> simp
  have h := he.mul (hI.const_add y0)
  apply h.congr_deriv
  dsimp only [scalarForcedSolution]
  have hcanc := scalarIntegratingFactor_cancel r a s
  calc
    _ = -r*(Real.exp (-r*(s-a))*(y0+∫ v in a..s, Real.exp (r*(v-a))*u v)) +
        (Real.exp (-r*(s-a))*Real.exp (r*(s-a)))*u s := by ring
    _ = _ := by rw [hcanc,one_mul]

/-- Scaling the forcing and initial state scales the actual integral solution. -/
theorem scalarForcedSolution_scale (r c : ℝ) (u : ℝ → ℝ) (a y0 s : ℝ) :
    scalarForcedSolution r (fun v => c*u v) a (c*y0) s =
      c*scalarForcedSolution r u a y0 s := by
  simp only [scalarForcedSolution]
  have he : (fun v : ℝ => Real.exp (r*(v-a))*(c*u v)) =
      (fun v : ℝ => c*(Real.exp (r*(v-a))*u v)) := by funext v; ring
  rw [he,intervalIntegral.integral_const_mul]
  ring

end HydrologyTree
