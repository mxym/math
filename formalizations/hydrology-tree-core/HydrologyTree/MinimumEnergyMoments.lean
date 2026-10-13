import HydrologyTree.ControlEnergy

/-! The exact unique minimum-energy continuous solution of finite exponential
moment constraints. Both feasibility and the sharp energy/equality statements
are proved from the actual positive integral Gramian. -/
open Matrix MeasureTheory
noncomputable section
namespace HydrologyTree

variable {n : ℕ}

def HasExponentialMoments (r d : Fin (n+1) → ℝ) (T : ℝ) (u : ℝ → ℝ) : Prop :=
  ∀ i, (∫ s in 0..T, Real.exp (r i*s)*u s)=d i

def minimumEnergyCoefficients (r d : Fin (n+1) → ℝ) (T : ℝ) : Fin (n+1) → ℝ :=
  (exponentialGramian r T)⁻¹*ᵥd

def minimumEnergyInput (r d : Fin (n+1) → ℝ) (T : ℝ) : ℝ → ℝ :=
  exponentialSignal r (minimumEnergyCoefficients r d T)

lemma minimumEnergyInput_continuous (r d : Fin (n+1) → ℝ) (T : ℝ) :
    Continuous (minimumEnergyInput r d T) := continuous_exponentialSignal _ _

/-- The proposed minimum-energy input satisfies every actual integral constraint. -/
theorem minimumEnergyInput_moments (r d : Fin (n+1) → ℝ) (hr : Function.Injective r)
    (T : ℝ) (hT : 0 < T) : HasExponentialMoments r d T (minimumEnergyInput r d T) := by
  intro i
  rw [minimumEnergyInput,← exponentialGramian_mulVec,minimumEnergyCoefficients,
    Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _
      (isUnit_iff_ne_zero.mpr (ne_of_gt (exponentialGramian_posDef r hr T hT).det_pos)),
    Matrix.one_mulVec]

/-- The energy is the explicit inverse-Gramian quadratic form in the target moments. -/
theorem minimumEnergyInput_energy (r d : Fin (n+1) → ℝ) (hr : Function.Injective r)
    (T : ℝ) (hT : 0 < T) :
    controlEnergy T (minimumEnergyInput r d T) = d ⬝ᵥ ((exponentialGramian r T)⁻¹*ᵥd) := by
  change (∫ s in 0..T, (exponentialSignal r (minimumEnergyCoefficients r d T) s)^2) = _
  rw [← exponentialGramian_quadratic]
  have hm : exponentialGramian r T*ᵥminimumEnergyCoefficients r d T=d := by
    ext i
    rw [exponentialGramian_mulVec]
    exact minimumEnergyInput_moments r d hr T hT i
  rw [hm,dotProduct_comm]
  rfl

/-- All feasible residuals are orthogonal to the constructed input in the
actual time-integral inner product. -/
theorem minimumEnergyInput_residual_orthogonal (r d : Fin (n+1) → ℝ)
    (hr : Function.Injective r) (T : ℝ) (hT : 0 < T)
    (u : ℝ → ℝ) (hu : Continuous u) (hm : HasExponentialMoments r d T u) :
    (∫ s in 0..T, minimumEnergyInput r d T s*(u s-minimumEnergyInput r d T s))=0 := by
  have hv := minimumEnergyInput_continuous r d T
  have hz (i : Fin (n+1)) :
      (∫ s in 0..T, Real.exp (r i*s)*(u s-minimumEnergyInput r d T s))=0 := by
    have he : Continuous (fun s : ℝ => Real.exp (r i*s)) := by fun_prop
    simp only [mul_sub]
    have hui : IntervalIntegrable (fun s : ℝ => Real.exp (r i*s)*u s) volume 0 T :=
      (he.mul hu).intervalIntegrable 0 T
    have hvi : IntervalIntegrable (fun s : ℝ => Real.exp (r i*s)*minimumEnergyInput r d T s) volume 0 T :=
      (he.mul hv).intervalIntegrable 0 T
    rw [intervalIntegral.integral_sub hui hvi,hm i,minimumEnergyInput_moments r d hr T hT i,sub_self]
  change (∫ s in 0..T, exponentialSignal r (minimumEnergyCoefficients r d T) s*
    (u s-minimumEnergyInput r d T s))=0
  rw [exponentialSignal_integral_pairing r _ T (fun s => u s-minimumEnergyInput r d T s) (hu.sub hv)]
  simp only [hz,mul_zero,Finset.sum_const_zero]

/-- Sharp global energy identity on the entire affine constraint set. -/
theorem minimumEnergyInput_exact_gap (r d : Fin (n+1) → ℝ) (hr : Function.Injective r)
    (T : ℝ) (hT : 0 < T) (u : ℝ → ℝ) (hu : Continuous u)
    (hm : HasExponentialMoments r d T u) :
    controlEnergy T u = d ⬝ᵥ ((exponentialGramian r T)⁻¹*ᵥd) +
      controlEnergy T (fun s => u s-minimumEnergyInput r d T s) := by
  rw [controlEnergy_expansion T u (minimumEnergyInput r d T) hu (minimumEnergyInput_continuous r d T),
    minimumEnergyInput_residual_orthogonal r d hr T hT u hu hm,
    minimumEnergyInput_energy r d hr T hT]
  ring

/-- The bound holds for ALL continuous feasible controls, not only a sampled
or parameterized family of inputs. -/
theorem minimumEnergyInput_optimal (r d : Fin (n+1) → ℝ) (hr : Function.Injective r)
    (T : ℝ) (hT : 0 < T) (u : ℝ → ℝ) (hu : Continuous u)
    (hm : HasExponentialMoments r d T u) :
    d ⬝ᵥ ((exponentialGramian r T)⁻¹*ᵥd) ≤ controlEnergy T u := by
  rw [minimumEnergyInput_exact_gap r d hr T hT u hu hm]
  exact le_add_of_nonneg_right (controlEnergy_nonneg T hT.le _)

/-- Complete equality classification: agreement on the whole closed control
interval, with no false uniqueness claim concerning input values outside it. -/
theorem minimumEnergyInput_equality_iff (r d : Fin (n+1) → ℝ) (hr : Function.Injective r)
    (T : ℝ) (hT : 0 < T) (u : ℝ → ℝ) (hu : Continuous u)
    (hm : HasExponentialMoments r d T u) :
    controlEnergy T u = d ⬝ᵥ ((exponentialGramian r T)⁻¹*ᵥd) ↔
      ∀ s ∈ Set.Icc 0 T, u s=minimumEnergyInput r d T s := by
  rw [minimumEnergyInput_exact_gap r d hr T hT u hu hm,add_eq_left,
    controlEnergy_zero_iff T hT (fun s => u s-minimumEnergyInput r d T s) (hu.sub (minimumEnergyInput_continuous r d T))]
  simp only [sub_eq_zero]

end HydrologyTree
