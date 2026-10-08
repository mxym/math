import Entry005.IidWeightedAnchorSelection
import Entry005.IidAnchorAffineDeterminant
import Mathlib.Topology.Instances.Matrix

noncomputable section
open MeasureTheory Metric
open scoped BigOperators Topology

namespace Entry005

theorem continuous_iid_anchor_determinant {d : ℕ} :
    Continuous (fun w : Fin (d + 1) → Fin d → ℝ => (anchorMatrix w).det) := by
  apply Continuous.matrix_det
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  induction i using Fin.cases with
  | zero => simpa only [anchor_matrix_entry, Fin.cases_zero] using
      (continuous_const : Continuous (fun _ : Fin (d + 1) → Fin d → ℝ => (1 : ℝ)))
  | succ i => simpa only [anchor_matrix_entry, Fin.cases_succ, Function.comp_def] using
      (continuous_apply i).comp (continuous_apply j)

theorem continuous_iid_anchor_volume {d : ℕ} :
    Continuous (fun w : Fin (d + 1) → Fin d → ℝ => |(anchorMatrix w).det|) := by
  simpa only [Real.norm_eq_abs] using (continuous_iid_anchor_determinant (d := d)).norm

/-- A tuple of support points belongs to the support of the actual iid law. -/
theorem iid_support_tuple_mem_support {d n : ℕ}
    (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν]
    (w : Fin n → Fin d → ℝ) (hw : ∀ i, w i ∈ ν.support) :
    w ∈ (iidLaw ν n).support := by
  rw [Measure.mem_support_iff_forall]
  intro U hU
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hU
  have hball : 0 < iidLaw ν n (ball w ε) := by
    change 0 < Measure.pi (fun _ : Fin n => ν) (ball w ε)
    rw [Measure.pi_ball _ _ hε]
    apply pos_iff_ne_zero.mpr
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact ((Measure.mem_support_iff_forall (w i)).mp (hw i) (ball (w i) ε)
      (Metric.ball_mem_nhds _ hε)).ne'
  exact hball.trans_le (measure_mono hsub)

/-- A nonzero-determinant support tuple makes the absolute determinant first
moment strictly positive by continuity on the support of the iid law. -/
theorem iid_anchor_volume_integral_pos_of_support_det_ne_zero {d : ℕ}
    (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν]
    (hX : ∀ i, Integrable (fun x : Fin d → ℝ => x i) ν)
    (w : Fin (d + 1) → Fin d → ℝ) (hw : ∀ i, w i ∈ ν.support)
    (hdet : (anchorMatrix w).det ≠ 0) :
    0 < ∫ v : Fin (d + 1) → Fin d → ℝ,
      |(anchorMatrix v).det| ∂iidLaw ν (d + 1) := by
  apply (integral_pos_iff_support_of_nonneg (fun v => abs_nonneg (anchorMatrix v).det)
    (iid_anchor_volume_integrable ν hX)).2
  have hmem : w ∈ Function.support (fun v : Fin (d + 1) → Fin d → ℝ =>
      |(anchorMatrix v).det|) := by simpa only [Function.mem_support, abs_ne_zero] using hdet
  exact (Measure.mem_support_iff_forall w).mp (iid_support_tuple_mem_support ν w hw) _
    (continuous_iid_anchor_volume.isOpen_support.mem_nhds hmem)

theorem iid_anchor_volume_integral_pos_of_support_affineIndependent {d : ℕ}
    (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν]
    (hX : ∀ i, Integrable (fun x : Fin d → ℝ => x i) ν)
    (w : Fin (d + 1) → Fin d → ℝ) (hw : ∀ i, w i ∈ ν.support)
    (hlin : AffineIndependent ℝ (fun i => WithLp.toLp 2 (w i))) :
    0 < ∫ v : Fin (d + 1) → Fin d → ℝ,
      |(anchorMatrix v).det| ∂iidLaw ν (d + 1) :=
  iid_anchor_volume_integral_pos_of_support_det_ne_zero ν hX w hw
    (selected_anchor_det_ne_zero_of_affineIndependent w hlin)

theorem iid_anchor_volume_integral_pos_of_support_raw_affineIndependent {d : ℕ}
    (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν]
    (hX : ∀ i, Integrable (fun x : Fin d → ℝ => x i) ν)
    (w : Fin (d + 1) → Fin d → ℝ) (hw : ∀ i, w i ∈ ν.support)
    (hlin : AffineIndependent ℝ w) :
    0 < ∫ v : Fin (d + 1) → Fin d → ℝ,
      |(anchorMatrix v).det| ∂iidLaw ν (d + 1) :=
  iid_anchor_volume_integral_pos_of_support_det_ne_zero ν hX w hw
    (selected_anchor_det_ne_zero_of_raw_affineIndependent w hlin)

end Entry005
