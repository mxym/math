import GaussianMomentSeparation
import GaussianWinningLimits

/-! Noncollision and self-moment passage for actual Gaussian winning diagrams.
Convergence and vanishing moment residuals are explicit hypotheses. No
covariance Hessian, spectral residual bound, or perimeter theorem is assumed. -/
open MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Topology
namespace GaussianFourGlobal
open GaussianMeasureBridge

/-- Actual moments converge to the predicted multiples of the score limits. -/
theorem tendsto_moment_of_residual {d : ℕ}
    (vSeq : ℕ → Fin 4 → Space d) (bSeq : ℕ → Fin 4 → ℝ)
    (hvn : ∀ n, Function.Injective (vSeq n))
    (muSeq : ℕ → ℝ) (v : Fin 4 → Space d) (mu : ℝ)
    (hv : ∀ i, Tendsto (fun n => vSeq n i) atTop (𝓝 (v i)))
    (hmu : Tendsto muSeq atTop (𝓝 mu))
    (hr : ∀ i, Tendsto (fun n =>
      (winningPartition (vSeq n) (bSeq n) (hvn n)).moment i - muSeq n • vSeq n i)
      atTop (𝓝 0)) (i : Fin 4) :
    Tendsto (fun n => (winningPartition (vSeq n) (bSeq n) (hvn n)).moment i)
      atTop (𝓝 (mu • v i)) := by
  simpa only [sub_add_cancel, zero_add] using (hr i).add (hmu.smul (hv i))

/-- Quantitative limit separation, with no assumed injectivity at the limit. -/
theorem residual_limit_pair_separation {d : ℕ}
    (vSeq : ℕ → Fin 4 → Space d) (bSeq : ℕ → Fin 4 → ℝ)
    (hvn : ∀ n, Function.Injective (vSeq n))
    (hbalance : ∀ n i, (gaussian d).real (winningCell (vSeq n) (bSeq n) i) = 1 / 4)
    (muSeq : ℕ → ℝ) (v : Fin 4 → Space d) (mu : ℝ)
    (hv : ∀ i, Tendsto (fun n => vSeq n i) atTop (𝓝 (v i)))
    (hmu : Tendsto muSeq atTop (𝓝 mu))
    (hr : ∀ i, Tendsto (fun n =>
      (winningPartition (vSeq n) (bSeq n) (hvn n)).moment i - muSeq n • vSeq n i)
      atTop (𝓝 0)) (i j : Fin 4) (hij : i ≠ j) :
    separationConstant ≤ |mu| * ‖v i - v j‖ := by
  have hi := tendsto_moment_of_residual vSeq bSeq hvn muSeq v mu hv hmu hr i
  have hj := tendsto_moment_of_residual vSeq bSeq hvn muSeq v mu hv hmu hr j
  have hle : separationConstant ≤ ‖mu • v i - mu • v j‖ :=
    isClosed_Ici.mem_of_tendsto (hi.sub hj).norm
      (Filter.Eventually.of_forall fun n => balanced_winning_moment_norm_separation
        (vSeq n) (bSeq n) (hvn n) (hbalance n) i j hij)
  simpa only [← smul_sub, norm_smul, Real.norm_eq_abs] using hle

/-- Injectivity at a possibly rank-deficient limit is a proved conclusion. -/
theorem residual_limit_injective {d : ℕ}
    (vSeq : ℕ → Fin 4 → Space d) (bSeq : ℕ → Fin 4 → ℝ)
    (hvn : ∀ n, Function.Injective (vSeq n))
    (hbalance : ∀ n i, (gaussian d).real (winningCell (vSeq n) (bSeq n) i) = 1 / 4)
    (muSeq : ℕ → ℝ) (v : Fin 4 → Space d) (mu : ℝ)
    (hv : ∀ i, Tendsto (fun n => vSeq n i) atTop (𝓝 (v i)))
    (hmu : Tendsto muSeq atTop (𝓝 mu))
    (hr : ∀ i, Tendsto (fun n =>
      (winningPartition (vSeq n) (bSeq n) (hvn n)).moment i - muSeq n • vSeq n i)
      atTop (𝓝 0)) : Function.Injective v := by
  intro i j heq
  by_contra hij
  have h := residual_limit_pair_separation vSeq bSeq hvn hbalance muSeq v mu hv hmu hr i j hij
  rw [heq, sub_self, norm_zero, mul_zero] at h
  exact (not_le_of_gt separationConstant_pos) h

/-- Nonnegative limiting multipliers cannot vanish. -/
theorem residual_limit_multiplier_pos {d : ℕ}
    (vSeq : ℕ → Fin 4 → Space d) (bSeq : ℕ → Fin 4 → ℝ)
    (hvn : ∀ n, Function.Injective (vSeq n))
    (hbalance : ∀ n i, (gaussian d).real (winningCell (vSeq n) (bSeq n) i) = 1 / 4)
    (muSeq : ℕ → ℝ) (v : Fin 4 → Space d) (mu : ℝ)
    (hv : ∀ i, Tendsto (fun n => vSeq n i) atTop (𝓝 (v i)))
    (hmu : Tendsto muSeq atTop (𝓝 mu)) (hmu_nonneg : 0 ≤ mu)
    (hr : ∀ i, Tendsto (fun n =>
      (winningPartition (vSeq n) (bSeq n) (hvn n)).moment i - muSeq n • vSeq n i)
      atTop (𝓝 0)) : 0 < mu := by
  have h := residual_limit_pair_separation vSeq bSeq hvn hbalance muSeq v mu hv hmu hr
    0 1 (by decide)
  have hne : mu ≠ 0 := by
    intro hz
    rw [hz, abs_zero, zero_mul] at h
    exact (not_le_of_gt separationConstant_pos) h
  exact lt_of_le_of_ne hmu_nonneg (Ne.symm hne)
/-- Balanced masses and actual moments survive the singular limiting passage.
The limiting distinctness and positivity are deduced, not supplied. -/
theorem balanced_residual_limit {d : ℕ}
    (vSeq : ℕ → Fin 4 → Space d) (bSeq : ℕ → Fin 4 → ℝ)
    (hvn : ∀ n, Function.Injective (vSeq n))
    (hbalance : ∀ n i, (gaussian d).real (winningCell (vSeq n) (bSeq n) i) = 1 / 4)
    (muSeq : ℕ → ℝ) (v : Fin 4 → Space d) (b : Fin 4 → ℝ) (mu : ℝ)
    (hv : ∀ i, Tendsto (fun n => vSeq n i) atTop (𝓝 (v i)))
    (hb : ∀ i, Tendsto (fun n => bSeq n i) atTop (𝓝 (b i)))
    (hmu : Tendsto muSeq atTop (𝓝 mu)) (hmu_nonneg : 0 ≤ mu)
    (hr : ∀ i, Tendsto (fun n =>
      (winningPartition (vSeq n) (bSeq n) (hvn n)).moment i - muSeq n • vSeq n i)
      atTop (𝓝 0)) :
    ∃ hv0 : Function.Injective v, 0 < mu ∧
      (∀ i, (gaussian d).real (winningCell v b i) = 1 / 4) ∧
      (∀ i, (winningPartition v b hv0).moment i = mu • v i) := by
  have hv0 := residual_limit_injective vSeq bSeq hvn hbalance muSeq v mu hv hmu hr
  refine ⟨hv0, residual_limit_multiplier_pos vSeq bSeq hvn hbalance muSeq v mu hv hmu
    hmu_nonneg hr, balanced_winning_limit vSeq bSeq v b (fun _ => 1 / 4) hv hb hv0 hbalance, ?_⟩
  intro i
  exact tendsto_nhds_unique (tendsto_winning_moment vSeq bSeq v b hv hb hvn hv0 i)
    (tendsto_moment_of_residual vSeq bSeq hvn muSeq v mu hv hmu hr i)

/-- Positive simultaneous score/price scaling leaves the actual cells intact. -/
theorem winningCell_pos_scale {d k : ℕ} (v : Fin k → Space d) (b : Fin k → ℝ)
    (c : ℝ) (hc : 0 < c) (i : Fin k) :
    winningCell (fun j => c • v j) (fun j => c * b j) i = winningCell v b i := by
  ext x
  simp only [winningCell, Set.mem_ofPred_eq, real_inner_smul_left, ← mul_sub,
    mul_lt_mul_iff_right₀ hc]

/-- Rescaling a limiting diagram by its positive multiplier makes it genuinely
self-induced by its actual Bochner first moments. -/
theorem balanced_limit_self_moment {d : ℕ}
    (v : Fin 4 → Space d) (b : Fin 4 → ℝ) (hv : Function.Injective v)
    (mu : ℝ) (hmu : 0 < mu)
    (hb : ∀ i, (gaussian d).real (winningCell v b i) = 1 / 4)
    (hm : ∀ i, (winningPartition v b hv).moment i = mu • v i) :
    ∃ hw : Function.Injective (fun i => mu • v i),
      (∀ i, (gaussian d).real (winningCell (fun i => mu • v i) (fun i => mu * b i) i) = 1 / 4) ∧
      (∀ i, (winningPartition (fun i => mu • v i) (fun i => mu * b i) hw).moment i = mu • v i) := by
  have hw : Function.Injective (fun i => mu • v i) := by
    intro i j hij
    apply hv
    exact (smul_right_injective (Space d) (ne_of_gt hmu)) hij
  refine ⟨hw, ?_, ?_⟩
  · intro i
    rw [winningCell_pos_scale v b mu hmu]
    exact hb i
  · intro i
    rw [winningPartition_moment_eq_setIntegral,
      winningCell_pos_scale v b mu hmu, ← winningPartition_moment_eq_setIntegral v b hv]
    exact hm i

end GaussianFourGlobal