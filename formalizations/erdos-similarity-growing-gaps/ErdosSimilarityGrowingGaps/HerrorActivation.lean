import ErdosSimilarityGrowingGaps.SequenceGeometry

namespace ErdosSimilarityGrowingGaps

open Filter Topology Asymptotics

/-! A local, reusable herror reduction.  The first hypothesis is exactly the
upper activation inequality for an edge.  The second is the numerical margin
that the late origin/span selection has to provide; it is kept explicit so
the lemma can be used independently of a particular routing certificate. -/
theorem herror_of_activation_buffer_margin
    {s₀ s₁ : ℝ} {Z : LogScale} {m : ℕ}
    (r : PowerParams s₀ s₁) (edge origin span k α q b : ℝ)
    (hα : 0 < α) (hq : 0 ≤ q)
    (hact : edge < r.1.1 * Z.z m - k)
    (hmargin : origin + span ≤ edge + k + α * Z.z m)
    (hbuffer : q * (2 : ℝ) ^ (-(origin + span)) < b) :
    q * (input Z m) ^ (r.1.1 + α) < b := by
  have hexp : origin + span < (r.1.1 + α) * Z.z m := by
    linarith
  have hneg : -(r.1.1 + α) * Z.z m < -(origin + span) := by
    linarith
  have hpow : (2 : ℝ) ^ (-(r.1.1 + α) * Z.z m) <
      (2 : ℝ) ^ (-(origin + span)) := by
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hneg
  rw [input_rpow_eq]
  rcases hq.eq_or_lt with rfl | hq
  · simpa using hbuffer
  · have hpow' : (2 : ℝ) ^ (-Z.z m * (r.1.1 + α)) <
        (2 : ℝ) ^ (-(origin + span)) := by
      convert hpow using 1 <;> ring
    exact (mul_lt_mul_of_pos_left hpow' hq).trans hbuffer

end ErdosSimilarityGrowingGaps
