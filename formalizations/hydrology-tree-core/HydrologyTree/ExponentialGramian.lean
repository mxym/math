import HydrologyTree.ExponentialIndependence
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! Strict positivity of the actual finite-horizon exponential Gramian. -/
open Matrix MeasureTheory
noncomputable section
namespace HydrologyTree
variable {n : ℕ}

def exponentialSignal (r c : Fin (n+1) → ℝ) (s : ℝ) : ℝ := ∑ i, c i*Real.exp (r i*s)

def exponentialGramian (r : Fin (n+1) → ℝ) (T : ℝ) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  Matrix.of fun i j => ∫ s in 0..T, Real.exp (r i*s)*Real.exp (r j*s)

lemma continuous_exponentialSignal (r c : Fin (n+1) → ℝ) : Continuous (exponentialSignal r c) := by
  unfold exponentialSignal
  fun_prop

theorem exponentialGramian_mulVec (r c : Fin (n+1) → ℝ) (T : ℝ) (i : Fin (n+1)) :
    (exponentialGramian r T*ᵥc) i=∫ s in 0..T, Real.exp (r i*s)*exponentialSignal r c s := by
  have hi (j : Fin (n+1)) : IntervalIntegrable
      (fun s : ℝ => (Real.exp (r i*s)*Real.exp (r j*s))*c j) volume 0 T := by
    apply Continuous.intervalIntegrable
    fun_prop
  simp only [Matrix.mulVec,dotProduct,exponentialGramian,Matrix.of_apply]
  rw [show (∑ j, (∫ s in 0..T, Real.exp (r i*s)*Real.exp (r j*s))*c j) =
      ∑ j, ∫ s in 0..T, (Real.exp (r i*s)*Real.exp (r j*s))*c j by
        simp only [intervalIntegral.integral_mul_const]]
  rw [← intervalIntegral.integral_finsetSum (fun j _ => hi j)]
  apply intervalIntegral.integral_congr
  intro s _
  simp only [exponentialSignal,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => by ring)

theorem exponentialGramian_quadratic (r c : Fin (n+1) → ℝ) (T : ℝ) :
    c ⬝ᵥ (exponentialGramian r T*ᵥc) = ∫ s in 0..T, (exponentialSignal r c s)^2 := by
  simp only [dotProduct,exponentialGramian_mulVec]
  simp_rw [← intervalIntegral.integral_const_mul]
  have hi (i : Fin (n+1)) : IntervalIntegrable
      (fun s : ℝ => c i*(Real.exp (r i*s)*exponentialSignal r c s)) volume 0 T := by
    apply Continuous.intervalIntegrable
    exact continuous_const.mul ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (continuous_exponentialSignal r c))
  rw [← intervalIntegral.integral_finsetSum (fun i _ => hi i)]
  apply intervalIntegral.integral_congr
  intro s _
  simp only [← mul_assoc]
  rw [← Finset.sum_mul]
  change exponentialSignal r c s * exponentialSignal r c s = _
  ring

theorem exponentialGramian_posDef (r : Fin (n+1) → ℝ) (hr : Function.Injective r)
    (T : ℝ) (hT : 0 < T) : (exponentialGramian r T).PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  constructor
  · ext i j
    simp [exponentialGramian,Matrix.conjTranspose_apply,mul_comm]
  · intro c hc
    simp only [star_trivial,exponentialGramian_quadratic]
    have hcont : Continuous (fun s : ℝ => (exponentialSignal r c s)^2) :=
      (continuous_exponentialSignal r c).pow 2
    have hnon : 0 ≤ ∫ s in 0..T, (exponentialSignal r c s)^2 :=
      intervalIntegral.integral_nonneg_of_forall hT.le (fun s => sq_nonneg _)
    apply lt_of_le_of_ne hnon
    intro hz
    have hae : (fun s : ℝ => (exponentialSignal r c s)^2) =ᵐ[volume.restrict (Set.Ioc 0 T)] 0 :=
      (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae hT.le
        (Filter.Eventually.of_forall (fun s => sq_nonneg (exponentialSignal r c s)))
        (hcont.intervalIntegrable 0 T)).mp hz.symm
    have heq := MeasureTheory.Measure.eqOn_Ioc_of_ae_eq (μ := volume) hae
      hcont.continuousOn continuous_const.continuousOn
    apply hc
    apply exponential_sum_independent r c hr 0 T hT
    intro s hs
    have he := heq ⟨hs.1,hs.2.le⟩
    have hz0 : exponentialSignal r c s=0 := sq_eq_zero_iff.mp he
    simpa [exponentialMoment,exponentialSignal] using hz0

end HydrologyTree
