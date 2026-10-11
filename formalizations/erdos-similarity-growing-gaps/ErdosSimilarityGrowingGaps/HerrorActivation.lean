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

/-! A late-window selection supplies the explicit margin above whenever the
edge starts after the origin and the routing span is little-o of that origin.
This is the asymptotic part of the herror interface; the buffer comparison
itself remains the pointwise lemma above. -/
theorem eventually_activation_span_margin
    {ι : Type*} {l : Filter ι}
    (origin span edge z : ι → ℝ) (r α k : ℝ)
    (hr : 0 < r) (hα : 0 < α)
    (horigin : Tendsto origin l atTop)
    (hspan : span =o[l] origin)
    (hedge : ∀ᶠ i in l, origin i ≤ edge i)
    (hact : ∀ᶠ i in l, edge i < r * z i - k) :
    ∀ᶠ i in l, origin i + span i ≤ edge i + k + α * z i := by
  have hcoef : 0 < α / (2 * r) := by positivity
  have hsmall := hspan.bound hcoef
  let C : ℝ := -2 * k * (r + α) / α
  have hlarge : ∀ᶠ i in l, C ≤ origin i := horigin.eventually_ge_atTop C
  have hpositive : ∀ᶠ i in l, 0 ≤ origin i := horigin.eventually_ge_atTop 0
  filter_upwards [hsmall, hlarge, hpositive, hedge, hact] with i hi hCi hOi hEi hAi
  have hspani : span i ≤ (α / (2 * r)) * origin i := by
    have hi' : ‖span i‖ ≤ (α / (2 * r)) * ‖origin i‖ := hi
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hOi] at hi'
    exact (le_abs_self (span i)).trans hi'
  have hz : (origin i + k) / r < z i := by
    apply (div_lt_iff₀ hr).2
    linarith
  have hαz : α / r * (origin i + k) < α * z i := by
    have := mul_lt_mul_of_pos_left hz hα
    convert this using 1 <;> field_simp [ne_of_gt hr]
  have hnon : 0 ≤ α * origin i + 2 * k * (r + α) := by
    dsimp [C] at hCi
    field_simp [ne_of_gt hα] at hCi
    nlinarith
  have hspan_margin : span i ≤ k + α / r * (origin i + k) := by
    have hratio : (α / (2 * r)) * origin i ≤
        k + α / r * (origin i + k) := by
      field_simp [ne_of_gt hr]
      nlinarith
    exact hspani.trans hratio
  linarith

end ErdosSimilarityGrowingGaps
