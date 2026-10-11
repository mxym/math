import ErdosSimilarityGrowingGaps.VariableRateSchedule
import ErdosSimilarityGrowingGaps.AnnulusSequence

namespace ErdosSimilarityGrowingGaps

open Filter Topology Asymptotics

/-! Elementary asymptotic interfaces used when the late annulus is selected
from `WindowFilling`.  These lemmas keep the logarithmic width estimate in a
form that can be fed directly to the variable branching/depth schedule. -/

theorem tendsto_log_log_atTop_of_tendsto
    {ι : Type*} {l : Filter ι} (U : ι → ℝ)
    (hU : Tendsto U l atTop) :
    Tendsto (fun i => Real.log (Real.log (U i))) l atTop := by
  simpa [Function.comp_def] using
    (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp hU))

theorem eventually_additive_width_le_loglog
    {ι : Type*} {l : Filter ι} (D U : ι → ℝ)
    (hU : Tendsto U l atTop)
    (hD : D =o[l] (fun i => Real.log (Real.log (U i))))
    (hD₀ : ∀ᶠ i in l, 0 ≤ D i)
    (δ ε : ℝ) (hδ : 0 ≤ δ) (hε : 0 < ε) :
    ∀ᶠ i in l, D i + δ ≤ ε * Real.log (Real.log (U i)) := by
  have hLL : Tendsto (fun i => Real.log (Real.log (U i))) l atTop :=
    tendsto_log_log_atTop_of_tendsto U hU
  have hLLpos : ∀ᶠ i in l, 0 < Real.log (Real.log (U i)) :=
    hLL.eventually_gt_atTop 0
  have hDsmall := hD.def (by positivity : 0 < ε / 2)
  have hδsmall : ∀ᶠ i in l,
      δ ≤ (ε / 2) * Real.log (Real.log (U i)) := by
    filter_upwards [hLL.eventually_ge_atTop (2 * δ / ε)] with i hi
    have hmul := (div_le_iff₀ hε).1 hi
    nlinarith
  filter_upwards [hDsmall, hD₀, hLLpos, hδsmall] with i hi hDi hLLi hδi
  rw [Real.norm_eq_abs, abs_of_nonneg hDi,
    Real.norm_eq_abs, abs_of_pos hLLi] at hi
  nlinarith

theorem variableBranching_littleO_loglog
    {ι : Type*} {l : Filter ι} (p : ℝ) (hp : 0 < p)
    (D U : ι → ℝ) (hD₁ : ∀ᶠ i in l, 1 ≤ D i)
    (hU : Tendsto U l atTop)
    (hD : D =o[l] (fun i => Real.log (Real.log (U i)))) :
    (fun i => (variableBranching p (D i) : ℝ)) =o[l]
      (fun i => Real.log (Real.log (U i))) := by
  exact (variableBranching_bigO_width p hp D hD₁).trans_isLittleO hD

theorem variableDepth_log_littleO_of_window_width
    {ι : Type*} {l : Filter ι} (p : ℝ) (hp : 0 < p) (hp₁ : p ≤ 1)
    (D U : ι → ℝ) (hU : Tendsto U l atTop)
    (hD₁ : ∀ᶠ i in l, 1 ≤ D i)
    (hD : D =o[l] (fun i => Real.log (Real.log (U i)))) :
    (fun i => (variableDepth p (variableBranching p (D i)) : ℝ) *
      Real.log (2 * (variableBranching p (D i) : ℝ))) =o[l]
      (fun i => Real.log (U i)) := by
  exact variableDepth_log_littleO p hp hp₁ D U hU hD₁ hD

end ErdosSimilarityGrowingGaps
