import HydrologyTree.PhysicalKalman
import HydrologyTree.PhysicalForcedODE

/-! Actual finite-window trajectory observability. The conclusion compares
whole physical state trajectories from a scalar output on any open time interval. -/
open Matrix Filter
open scoped Topology
noncomputable section
namespace HydrologyTree

lemma homogeneous_power_output_derivative {n : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (z : ℝ → Fin (n+1) → ℝ)
    (hz : IsForcedMatrixSolution A (Pi.single 0 1) 0 z) (k : ℕ) (s : ℝ) :
    HasDerivAt (fun v => (A^k*ᵥz v) 0) ((A^(k+1)*ᵥz s) 0) s := by
  have h := (matrixOperator (A^k)).hasFDerivAt.comp_hasDerivAt s (hz s)
  have he := hasDerivAt_pi.mp h (0 : Fin (n+1))
  simpa only [Function.comp_apply,matrixOperator_apply,Pi.zero_apply,zero_smul,add_zero,Matrix.mulVec_mulVec,pow_succ] using he

/-- A zero root signal on an open time interval forces every Kalman output
coordinate to vanish there, using actual derivatives rather than formal jets. -/
theorem homogeneous_zero_output_powers {n : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (z : ℝ → Fin (n+1) → ℝ)
    (hz : IsForcedMatrixSolution A (Pi.single 0 1) 0 z) (a b : ℝ)
    (hout : ∀ s ∈ Set.Ioo a b, z s 0=0) :
    ∀ k : ℕ, ∀ s ∈ Set.Ioo a b, (A^k*ᵥz s) 0=0 := by
  intro k
  induction k with
  | zero => simpa using hout
  | succ k ih =>
    intro s hs
    have he : (fun v : ℝ => (A^k*ᵥz v) 0) =ᶠ[𝓝 s] (fun _ => (0 : ℝ)) := by
      filter_upwards [isOpen_Ioo.mem_nhds hs] with v hv
      exact ih v hv
    have hd0 := (hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq he
    exact (homogeneous_power_output_derivative A z hz k s).unique hd0

/-- Nonzero actual observability determinant identifies any homogeneous state
trajectory from its root coordinate on ANY nonempty open time window. -/
theorem root_observation_detects_trajectory {n : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hO : (rootObservationMatrix A).det ≠ 0) (z : ℝ → Fin (n+1) → ℝ)
    (hz : IsForcedMatrixSolution A (Pi.single 0 1) 0 z)
    (a b : ℝ) (hab : a < b) (hout : ∀ s ∈ Set.Ioo a b, z s 0=0) : z=0 := by
  let s := (a+b)/2
  have hs : s ∈ Set.Ioo a b := by dsimp [s]; constructor <;> linarith
  have hzero : rootObservationMatrix A*ᵥz s=0 := by
    ext i
    exact homogeneous_zero_output_powers A z hz a b hout i.val s hs
  have hzs : z s=0 := by
    have h := congrArg (fun v => (rootObservationMatrix A)⁻¹*ᵥv) hzero
    simpa only [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hO),
      Matrix.one_mulVec,Matrix.mulVec_zero] using h
  apply forcedMatrixSolution_unique A (Pi.single 0 1) 0 z 0 s hz
  · intro v
    simpa using (hasDerivAt_const v (0 : Fin (n+1) → ℝ))
  · exact hzs

/-- Equal scalar output and a common forcing on any nonempty open interval
identify the entire actual state trajectories, without assuming initial states. -/
theorem actual_trajectory_observability {n : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hO : (rootObservationMatrix A).det ≠ 0) (u : ℝ → ℝ)
    (z q : ℝ → Fin (n+1) → ℝ)
    (hz : IsForcedMatrixSolution A (Pi.single 0 1) u z)
    (hq : IsForcedMatrixSolution A (Pi.single 0 1) u q)
    (a b : ℝ) (hab : a < b) (hout : ∀ s ∈ Set.Ioo a b, z s 0=q s 0) : z=q := by
  have hd : IsForcedMatrixSolution A (Pi.single 0 1) 0 (z-q) := by
    intro s
    have h := (hz s).sub (hq s)
    apply h.congr_deriv
    simp [Matrix.mulVec_sub]
  have he := root_observation_detects_trajectory A hO (z-q) hd a b hab
    (fun s hs => sub_eq_zero.mpr (hout s hs))
  exact sub_eq_zero.mp he

/-- The complete actual observability conclusion for every real full-response
model. The determinant and positivity prerequisites are proved, not assumed. -/
theorem real_full_response_trajectory_observable {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i, 0 < r i)
    (hw : ∀ i, 0 < w i) (hm : (∑ i, w i)=1) (hx : HasStieltjesRootResponse t x r w)
    (u : ℝ → ℝ) (z q : ℝ → Fin (n+1) → ℝ)
    (hz : IsPhysicalForcedSolution t x u z) (hq : IsPhysicalForcedSolution t x u q)
    (a b : ℝ) (hab : a < b) (hout : ∀ s ∈ Set.Ioo a b, z s 0=q s 0) : z=q :=
  actual_trajectory_observability (compartmentMatrix t x)
    (real_full_response_kalman_nonsingular t x r w hr hpos hw hm hx).2 u z q hz hq a b hab hout

end HydrologyTree
