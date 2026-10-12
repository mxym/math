import GaussianPartition
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod

/-! Exact product splitting of the actual standard Gaussian, with an explicit
coordinate embedding. No independence or product-law hypothesis is assumed. -/
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d : ℕ}

noncomputable def joinCoordinate (t : ℝ) (y : Space d) : Space (d+1) :=
  WithLp.toLp 2 (Fin.cons t (fun j => y j))

@[simp] lemma joinCoordinate_zero (t : ℝ) (y : Space d) : joinCoordinate t y 0 = t := rfl
@[simp] lemma joinCoordinate_succ (t : ℝ) (y : Space d) (j : Fin d) :
    joinCoordinate t y j.succ = y j := rfl

lemma inner_joinCoordinate (s t : ℝ) (x y : Space d) :
    ⟪joinCoordinate s x, joinCoordinate t y⟫ = s*t + ⟪x,y⟫ := by
  simp [PiLp.inner_apply, Fin.sum_univ_succ, mul_comm]

lemma gaussian_toLp_preserving (d : ℕ) :
    MeasurePreserving (WithLp.toLp 2 : (Fin d → ℝ) → Space d)
      (Measure.pi fun _ => gaussianReal 0 1) (gaussian d) :=
  ⟨by fun_prop, map_pi_eq_stdGaussian⟩

lemma gaussian_ofLp_preserving (d : ℕ) :
    MeasurePreserving (WithLp.ofLp : Space d → (Fin d → ℝ))
      (gaussian d) (Measure.pi fun _ => gaussianReal 0 1) := by
  refine ⟨by fun_prop, ?_⟩
  rw [← (gaussian_toLp_preserving d).map_eq,
    Measure.map_map (by fun_prop) (by fun_prop)]
  change Measure.map id _ = _
  rw [Measure.map_id]

/-- The first coordinate and the remaining d coordinates have the genuine
product law gamma_1 times gamma_d. -/
theorem gaussian_joinCoordinate_preserving :
    MeasurePreserving (fun z : ℝ × Space d => joinCoordinate z.1 z.2)
      ((gaussianReal 0 1).prod (gaussian d)) (gaussian (d+1)) := by
  have hp := (MeasurePreserving.id (gaussianReal 0 1)).prod (gaussian_ofLp_preserving d)
  have he := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (d+1) => gaussianReal 0 1) 0).symm
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => ℝ) 0)
  have hh := (gaussian_toLp_preserving (d+1)).comp (he.comp hp)
  convert hh using 1
  funext z
  ext i
  simp [joinCoordinate, Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv, Fin.insertNth_zero']

theorem gaussian_joinCoordinate_swapped_preserving :
    MeasurePreserving (fun z : Space d × ℝ => joinCoordinate z.2 z.1)
      ((gaussian d).prod (gaussianReal 0 1)) (gaussian (d+1)) := by
  exact gaussian_joinCoordinate_preserving.comp Measure.measurePreserving_swap

end GaussianMeasureBridge
