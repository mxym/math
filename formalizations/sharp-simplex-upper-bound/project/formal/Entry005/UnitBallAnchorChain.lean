import Entry005.UnitBallDeterminant
import Entry005.RoundAnchorChain

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Entry005

theorem unit_ball_coordinate_integrable {d : ℕ}
    (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν]
    (hball : ∀ᵐ x ∂ν, ‖WithLp.toLp 2 x‖ ≤ 1) (i : Fin d) :
    Integrable (fun x : Fin d → ℝ => x i) ν := by
  apply (integrable_const (1 : ℝ)).mono' (measurable_pi_apply i).aestronglyMeasurable
  filter_upwards [hball] with x hx
  exact (PiLp.norm_apply_le (WithLp.toLp 2 x) i).trans hx

theorem unit_ball_coordinate_product_integrable {d : ℕ}
    (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν]
    (hball : ∀ᵐ x ∂ν, ‖WithLp.toLp 2 x‖ ≤ 1) (i j : Fin d) :
    Integrable (fun x : Fin d → ℝ => x i * x j) ν := by
  apply (integrable_const (1 : ℝ)).mono'
    ((measurable_pi_apply i).mul (measurable_pi_apply j)).aestronglyMeasurable
  filter_upwards [hball] with x hx
  have hi := (PiLp.norm_apply_le (WithLp.toLp 2 x) i).trans hx
  have hj := (PiLp.norm_apply_le (WithLp.toLp 2 x) j).trans hx
  change ‖x i * x j‖ ≤ 1
  rw [norm_mul]
  exact (mul_le_mul hi hj (norm_nonneg _) (by norm_num)).trans (by norm_num)

theorem unit_ball_iid_determinant_bound {d : ℕ} (hd : 1 ≤ d)
    (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν]
    (hball : ∀ᵐ x ∂ν, ‖WithLp.toLp 2 x‖ ≤ 1) :
    ∀ᵐ w : Fin (d + 1) → Fin d → ℝ ∂iidLaw ν (d + 1),
      |liftedDeterminant (fun i => w i.succ) (w 0)| ≤ (2 : ℝ) ^ d := by
  have hall : ∀ᵐ w : Fin (d + 1) → Fin d → ℝ ∂iidLaw ν (d + 1),
      ∀ i, ‖WithLp.toLp 2 (w i)‖ ≤ 1 := by
    apply ae_all_iff.2
    intro i
    exact (measurePreserving_eval (fun _ : Fin (d + 1) => ν) i).quasiMeasurePreserving.ae hball
  filter_upwards [hall] with w hw
  exact unit_ball_anchor_determinant hd w hw

theorem unit_ball_support_bound {d : ℕ}
    (ν : Measure (Fin d → ℝ)) (hball : ∀ᵐ x ∂ν, ‖WithLp.toLp 2 x‖ ≤ 1) :
    ∀ x ∈ ν.support, ‖WithLp.toLp 2 x‖ ≤ 1 := by
  have hclosed : IsClosed {x : Fin d → ℝ | ‖WithLp.toLp 2 x‖ ≤ 1} :=
    isClosed_le (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).norm
      continuous_const
  exact Measure.support_subset_of_isClosed hclosed hball

theorem unit_ball_round_witness_anchor {d : ℕ} (hd : 1 ≤ d) {ι : Type*} [Fintype ι]
    (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν]
    (hball : ∀ᵐ x ∂ν, ‖WithLp.toLp 2 x‖ ≤ 1)
    (hcenter : ∀ i, (∫ x : Fin d → ℝ, x i ∂ν) = 0)
    {b : ℝ} (hb : 0 < b)
    (hround : ∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 →
      2 * b ≤ negativeIntegral ν (fun x => dotProduct u x))
    (p : ι → Equiv.Perm (Fin (d + 2))) :
    ∃ w : Fin (d + 1) → Fin d → ℝ,
      (∀ i, w i ∈ ν.support ∧ ‖WithLp.toLp 2 (w i)‖ ≤ 1) ∧
      b ^ d ≤ |liftedDeterminant (fun i => w i.succ) (w 0)| ∧
      transportedWitnessSum ν (fun base x => liftedDeterminant base x)
        (fun i => iidWitnessTransport d (p i)) w ≤
        ((Fintype.card ι : ℝ) * determinantLawDefect (iidLaw ν d) ν id id) *
          (4 : ℝ) ^ d / (b ^ d) ^ 2 := by
  obtain ⟨w, hsupp, hV, hH⟩ := round_iid_witness_anchor hd ν
    (unit_ball_coordinate_integrable ν hball) hcenter
    (unit_ball_coordinate_product_integrable ν hball) hb (pow_pos (by norm_num) d)
    hround p (unit_ball_iid_determinant_bound hd ν hball)
  refine ⟨w, fun i => ⟨hsupp i, unit_ball_support_bound ν hball (w i) (hsupp i)⟩, hV, ?_⟩
  have hpow : ((2 : ℝ) ^ d) ^ 2 = (4 : ℝ) ^ d := by
    rw [pow_two, ← mul_pow]
    norm_num
  simpa only [hpow] using hH

end Entry005
