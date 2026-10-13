import HydrologyTree.ExponentialGramian

/-! Exact control energy identities on a finite interval. Equality means equality
on that interval only; arbitrary values outside it are not spuriously identified. -/
open Matrix MeasureTheory
noncomputable section
namespace HydrologyTree

def controlEnergy (T : ℝ) (u : ℝ → ℝ) : ℝ := ∫ s in 0..T, (u s)^2

lemma controlEnergy_nonneg (T : ℝ) (hT : 0 ≤ T) (u : ℝ → ℝ) :
    0 ≤ controlEnergy T u :=
  intervalIntegral.integral_nonneg_of_forall hT (fun _ => sq_nonneg _)

/-- Zero actual square integral detects a continuous input at every point of
its complete closed time interval, including both endpoints. -/
theorem controlEnergy_zero_iff (T : ℝ) (hT : 0 < T) (u : ℝ → ℝ) (hu : Continuous u) :
    controlEnergy T u=0 ↔ ∀ s ∈ Set.Icc 0 T, u s=0 := by
  constructor
  · intro hz s hs
    by_contra hne
    have hp := intervalIntegral.integral_pos hT (hu.pow 2).continuousOn
      (fun v _ => sq_nonneg (u v)) ⟨s,hs,sq_pos_of_ne_zero hne⟩
    change 0 < controlEnergy T u at hp
    rw [hz] at hp
    exact (lt_irrefl 0) hp
  · intro hz
    change (∫ s in 0..T, (u s)^2)=0
    calc
      _ = ∫ s in 0..T, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro s hs
        have hv := hz s (by simpa only [Set.uIcc_of_le hT.le] using hs)
        simp [hv]
      _ = 0 := by simp

/-- Exact Pythagorean expansion of control energy, without a minimization premise. -/
theorem controlEnergy_expansion (T : ℝ) (u v : ℝ → ℝ)
    (hu : Continuous u) (hv : Continuous v) :
    controlEnergy T u = controlEnergy T v +
      2*(∫ s in 0..T, v s*(u s-v s)) + controlEnergy T (fun s => u s-v s) := by
  have h0 : IntervalIntegrable (fun s => (v s)^2) volume 0 T :=
    (hv.pow 2).intervalIntegrable 0 T
  have h1 : IntervalIntegrable (fun s => 2*(v s*(u s-v s))) volume 0 T :=
    (continuous_const.mul (hv.mul (hu.sub hv))).intervalIntegrable 0 T
  have h2 : IntervalIntegrable (fun s => (u s-v s)^2) volume 0 T :=
    ((hu.sub hv).pow 2).intervalIntegrable 0 T
  unfold controlEnergy
  calc
    _ = ∫ s in 0..T, ((v s)^2+2*(v s*(u s-v s)))+(u s-v s)^2 := by
      apply intervalIntegral.integral_congr
      intro s _
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add (h0.add h1) h2,
        intervalIntegral.integral_add h0 h1,intervalIntegral.integral_const_mul]

/-- Actual integral against a finite exponential signal equals its moment pairing. -/
theorem exponentialSignal_integral_pairing {n : ℕ} (r c : Fin (n+1) → ℝ)
    (T : ℝ) (u : ℝ → ℝ) (hu : Continuous u) :
    (∫ s in 0..T, exponentialSignal r c s*u s) =
      ∑ i, c i*(∫ s in 0..T, Real.exp (r i*s)*u s) := by
  have hi (i : Fin (n+1)) : IntervalIntegrable
      (fun s : ℝ => c i*(Real.exp (r i*s)*u s)) volume 0 T := by
    apply Continuous.intervalIntegrable
    exact continuous_const.mul ((Real.continuous_exp.comp
      (continuous_const.mul continuous_id)).mul hu)
  calc
    _ = ∫ s in 0..T, ∑ i, c i*(Real.exp (r i*s)*u s) := by
      apply intervalIntegral.integral_congr
      intro s _
      simp only [exponentialSignal,Finset.sum_mul]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    _ = _ := by
      rw [intervalIntegral.integral_finsetSum (fun i _ => hi i)]
      simp only [intervalIntegral.integral_const_mul]

end HydrologyTree
