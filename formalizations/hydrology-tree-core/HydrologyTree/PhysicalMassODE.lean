import HydrologyTree.PhysicalForcedODE

/-! Exact differential and integrated water balance for actual ODE trajectories.
All integrals are real interval integrals, not formal transfer-function symbols. -/
open Matrix MeasureTheory
noncomputable section
namespace HydrologyTree

def coordinateSumLM (I : Type*) [Fintype I] : (I → ℝ) →ₗ[ℝ] ℝ where
  toFun z := ∑ i, z i
  map_add' z y := by simp [Finset.sum_add_distrib]
  map_smul' c z := by simp [Finset.mul_sum]

def coordinateSumCLM (I : Type*) [Fintype I] : (I → ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (coordinateSumLM I)

/-- Exact mass balance for any actual classical trajectory, even for real rates
that are not assumed positive. -/
theorem physical_total_storage_hasDerivAt {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (u : ℝ → ℝ) (z : ℝ → Fin (n+1) → ℝ) (hz : IsPhysicalForcedSolution t x u z) (s : ℝ) :
    HasDerivAt (fun v => ∑ i, z v i) (u s-x.1 0*z s 0) s := by
  have h := (coordinateSumCLM (Fin (n+1))).hasFDerivAt.comp_hasDerivAt s (hz s)
  apply h.congr_deriv
  change (∑ i, ((compartmentMatrix t x)*ᵥz s + u s • (Pi.single 0 1 : Fin (n+1) → ℝ)) i) = _
  simp only [Pi.add_apply,Finset.sum_add_distrib,Pi.smul_apply,smul_eq_mul]
  rw [compartment_total_flux]
  simp [← Finset.mul_sum]
  ring

/-- Integrated physical water balance in either time orientation. -/
theorem physical_total_storage_integral_balance {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (u : ℝ → ℝ) (hu : Continuous u) (z : ℝ → Fin (n+1) → ℝ)
    (hz : IsPhysicalForcedSolution t x u z) (a s : ℝ) :
    (∑ i, z s i) = (∑ i, z a i) + ∫ v in a..s, (u v-x.1 0*z v 0) := by
  have hzc : Continuous z := continuous_iff_continuousAt.mpr (fun v => (hz v).continuousAt)
  have hc : Continuous (fun v => u v-x.1 0*z v 0) := by fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun v _ => physical_total_storage_hasDerivAt t x u z hz v) (hc.intervalIntegrable a s)
  linarith

/-- Equal input and discharge with equal initial total storage give equal actual
storage, not just equality of a symbolic mass-balance equation. -/
theorem equal_discharge_equal_total_storage {n : ℕ} (t v : OrderedTree n) (x y : TreeRates n)
    (u : ℝ → ℝ) (hu : Continuous u) (z q : ℝ → Fin (n+1) → ℝ)
    (hz : IsPhysicalForcedSolution t x u z) (hq : IsPhysicalForcedSolution v y u q)
    (a : ℝ) (h0 : (∑ i, z a i)=(∑ i, q a i))
    (hQ : ∀ s, x.1 0*z s 0=y.1 0*q s 0) (s : ℝ) :
    (∑ i, z s i)=(∑ i, q s i) := by
  rw [physical_total_storage_integral_balance t x u hu z hz a s,
    physical_total_storage_integral_balance v y u hu q hq a s,h0]
  simp only [hQ]

end HydrologyTree
