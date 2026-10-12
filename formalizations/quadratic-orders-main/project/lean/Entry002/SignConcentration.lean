/-
Generic fair-sign Hoeffding proofs reused verbatim from openai/math family028,
commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, SignConcentration.lean lines 2-53.
Apache-2.0; see ../../upstream-028/LICENSE. Gaussian-specific sequel omitted.
-/
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace OAI

universe uIota

namespace GaussianMoat

open MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable def fairCoin : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure
instance fairCoin_probability : IsProbabilityMeasure fairCoin := by
  unfold fairCoin
  infer_instance
noncomputable def signMeasure (ι : Type uIota) [Fintype ι] : Measure (ι → Bool) :=
  Measure.pi (fun _ => fairCoin)
instance signMeasure_probability (ι : Type uIota) [Fintype ι] : IsProbabilityMeasure (signMeasure ι) := by
  unfold signMeasure
  infer_instance

theorem fairCoin_mean (f : Bool → ℝ) : ∫ b, f b ∂fairCoin = (f false + f true) / 2 := by
  have hf : Integrable f fairCoin := Integrable.of_mem_Icc
    (min (f false) (f true)) (max (f false) (f true)) (by fun_prop) (by
      apply ae_of_all
      intro b
      cases b <;> simp)
  rw [integral_fintype hf]
  simp [fairCoin, measureReal_def,
    PMF.uniformOfFintype_apply]
  ring

theorem sign_hoeffding {ι : Type uIota} [Fintype ι] (f : ι → Bool → ℝ) (w : ι → ℝ)
    (hf : ∀ i b, f i b ∈ Set.Icc 0 (w i)) {ε : ℝ} (hε : 0 ≤ ε) :
    (signMeasure ι).real {σ | ε + ∑ i, (f i false + f i true) / 2 ≤ ∑ i, f i (σ i)}
      ≤ Real.exp (-ε ^ 2 / (2 * ∑ i, (((‖w i‖₊ / 2) ^ 2 : ℝ≥0) : ℝ))) := by
  classical
  let X : ι → (ι → Bool) → ℝ := fun i σ => f i (σ i) - (f i false + f i true) / 2
  have hsub (i : ι) : HasSubgaussianMGF (X i) ((‖w i‖₊ / 2) ^ 2) (signMeasure ι) := by
    have h := hasSubgaussianMGF_of_mem_Icc (μ := fairCoin) (X := f i)
      (by fun_prop) (ae_of_all _ (hf i))
    rw [fairCoin_mean] at h
    simp only [sub_zero] at h
    have he := (measurePreserving_eval (fun _ : ι => fairCoin) i).map_eq
    rw [← he] at h
    have heval : AEMeasurable (Function.eval i : (ι → Bool) → Bool) (signMeasure ι) :=
      (measurable_pi_apply i).aemeasurable
    exact HasSubgaussianMGF.of_map heval h
  have hind : iIndepFun X (signMeasure ι) :=
    iIndepFun_pi (X := fun i b => f i b - (f i false + f i true) / 2) (fun _ => by fun_prop)
  have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind
    (s := Finset.univ) (fun i _ => hsub i) hε
  simpa only [X, Finset.sum_sub_distrib, le_sub_iff_add_le, NNReal.coe_sum] using h

end GaussianMoat
end OAI
