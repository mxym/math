import ErdosSimilarityGrowingGaps.HerrorWindowBridge
import ErdosSimilarityGrowingGaps.GreedyTailBounds

namespace ErdosSimilarityGrowingGaps

open Filter Topology Asymptotics

theorem globalRoutingWindow_start_ge_origin
    {M d : ℕ} (c : RoutingTemplate M d)
    (i : Fin (Fintype.card (RoutingEdge M d))) :
    (c.origin : ℝ) ≤ (globalRoutingWindows c i).1 := by
  change (c.origin : ℝ) ≤ (c.edgeStart (globalRoutingEdgeEnumeration M d i) : ℝ)
  exact_mod_cast c.edgeStart_ge_origin (globalRoutingEdgeEnumeration M d i)

/-! The extra buffer exponent shift is fixed while the routing span is
little-o of the origin.  This margin is uniform in all active sample indices
and every exponent `r ∈ [1/K,K]`. -/
theorem eventually_span_shift_le_activation_slack
    {ι : Type*} {l : Filter ι} (U T : ι → ℝ) (K α k C : ℝ)
    (hK : 0 < K) (hα : 0 < α)
    (hU : Tendsto U l atTop) (hT : T =o[l] U) :
    ∀ᶠ i in l, T i + C ≤ k + α * ((U i + k) / K) := by
  have hconst : (fun _ : ι => C) =o[l] U := by
    simpa [Function.comp_def] using
      (isLittleO_const_id_atTop C).comp_tendsto hU
  have hsmall := (hT.add hconst).bound
    (show (0 : ℝ) < α / (2 * K) by positivity)
  have hlarge := hU.eventually_ge_atTop (-2 * k * (K + α) / α)
  have hpos := hU.eventually_ge_atTop 0
  filter_upwards [hsmall, hlarge, hpos] with i hi hLi hUi
  have hbound : T i + C ≤ α / (2 * K) * U i := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hUi] at hi
    exact (le_abs_self _).trans hi
  have hconst_margin : 0 ≤ α * U i + 2 * k * (K + α) := by
    have hL := (div_le_iff₀ hα).1 hLi
    nlinarith
  have hslack : α / (2 * K) * U i ≤ k + α * ((U i + k) / K) := by
    have hKne : K ≠ 0 := ne_of_gt hK
    have hrewrite : k + α * ((U i + k) / K) =
        (K * k + α * (U i + k)) / K := by
      field_simp [hKne]
    rw [hrewrite]
    apply (le_div_iff₀ hK).2
    field_simp [hKne]
    nlinarith [hconst_margin]
  exact hbound.trans hslack

/-! A pointwise span envelope is enough for the error margin.  This variant is
useful when the selected base length is only known to fit a fixed fraction of
the annulus origin; no little-o conversion is needed. -/
theorem eventually_span_shift_le_activation_slack_of_fixed_ratio
    {ι : Type*} {l : Filter ι} (U T : ι → ℝ) (K α k C t : ℝ)
    (hK : 0 < K) (hα : 0 < α)
    (ht : t ≤ α / (4 * K))
    (hU : Tendsto U l atTop)
    (hT : ∀ᶠ i in l, T i ≤ t * U i) :
    ∀ᶠ i in l, T i + C ≤ k + α * ((U i + k) / K) := by
  have hCbound := hU.eventually_ge_atTop
    (C / (α / (4 * K)))
  have hlarge := hU.eventually_ge_atTop (-2 * k * (K + α) / α)
  have hpos := hU.eventually_ge_atTop 0
  filter_upwards [hT, hCbound, hlarge, hpos] with i hTi hCi hLi hUi
  have hC : C ≤ (α / (4 * K)) * U i := by
    have hmul := (div_le_iff₀ (by positivity : 0 < α / (4 * K))).1 hCi
    linarith
  have hbound : T i + C ≤ α / (2 * K) * U i := by
    have hTu : T i ≤ α / (4 * K) * U i := by
      exact hTi.trans (mul_le_mul_of_nonneg_right ht hUi)
    have hcoef : α / (2 * K) = 2 * (α / (4 * K)) := by
      field_simp [ne_of_gt hK]
      ring
    rw [hcoef]
    nlinarith
  have hconst_margin : 0 ≤ α * U i + 2 * k * (K + α) := by
    have hL := (div_le_iff₀ hα).1 hLi
    nlinarith
  have hslack : α / (2 * K) * U i ≤ k + α * ((U i + k) / K) := by
    have hKne : K ≠ 0 := ne_of_gt hK
    have hrewrite : k + α * ((U i + k) / K) =
        (K * k + α * (U i + k)) / K := by
      field_simp [hKne]
    rw [hrewrite]
    apply (le_div_iff₀ hK).2
    field_simp [hKne]
    nlinarith [hconst_margin]
  exact hbound.trans hslack

theorem eventually_globalRoutingWindow_error
    {ι : Type*} {l : Filter ι} {Z : LogScale} {K : ℕ} {k : ℤ}
    {M d : ι → ℕ} (c : ∀ i, RoutingTemplate (M i) (d i))
    (p α q : ℝ) (hK : 2 ≤ K) (hp : 0 < p) (hα : 0 < α) (hq : 0 ≤ q)
    (hU : Tendsto (fun i => ((c i).origin : ℝ)) l atTop)
    (hT : (fun i => (RoutingTemplate.span (M i) (c i).gap
      (c i).baseLength (d i) : ℝ)) =o[l]
        (fun i => ((c i).origin : ℝ))) :
    ∀ᶠ i in l, ∀ (r : PowerParams (1 / (K : ℝ)) K) (n : ℕ),
      r ∈ sequenceWindowActivations Z n k (globalRoutingWindows (c i)) →
      q * (input Z n) ^ (r.1.1 + α) < routingBufferRadius (c i) p := by
  obtain ⟨C, hC⟩ := exists_buffer_shift p q hp hq
  have hC' : q * (2 : ℝ) ^ (-C) < p / 32 := by linarith
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hslack := eventually_span_shift_le_activation_slack
    (fun i => ((c i).origin : ℝ))
    (fun i => (RoutingTemplate.span (M i) (c i).gap (c i).baseLength (d i) : ℝ))
    (K : ℝ) α (k : ℝ) C hKpos hα hU hT
  have hpos := hU.eventually_ge_atTop (max 1 (-(k : ℝ)))
  filter_upwards [hslack, hpos] with i hi hOi
  intro r n hactive
  have hO : 1 ≤ (c i).origin := by
    have h : (1 : ℝ) ≤ ((c i).origin : ℝ) :=
      (le_max_left _ _).trans hOi
    exact_mod_cast h
  have hnum : 0 ≤ ((c i).origin : ℝ) + (k : ℝ) := by
    have h : -(k : ℝ) ≤ ((c i).origin : ℝ) :=
      (le_max_right _ _).trans hOi
    linarith
  obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hactive
  have hstart := globalRoutingWindow_start_ge_origin (c i) j
  have hrpos : 0 < r.1.1 := by
    exact lt_of_lt_of_le (by positivity) r.1.2.1
  have hzpos : 0 < Z.z n := by
    have hact := hj.1
    nlinarith
  have hprod : r.1.1 * Z.z n ≤ (K : ℝ) * Z.z n :=
    mul_le_mul_of_nonneg_right r.1.2.2 hzpos.le
  have hz : (((c i).origin : ℝ) + (k : ℝ)) / (K : ℝ) ≤ Z.z n := by
    apply (div_le_iff₀ hKpos).2
    linarith [hj.1]
  apply herror_of_global_window_margin_shift (c i) r n hO hα hq hp hC'
  · intro j'
    have hstart' := globalRoutingWindow_start_ge_origin (c i) j'
    have hαz := mul_le_mul_of_nonneg_left hz hα.le
    linarith
  · exact hactive

/-! The same global error estimate with a fixed pointwise span fraction.  The
little-o version above is convenient for abstract schedules; this version is
used by the scaled length selector, which keeps a prescribed fraction of the
annulus origin as its span budget. -/
theorem eventually_globalRoutingWindow_error_of_fixed_ratio
    {ι : Type*} {l : Filter ι} {Z : LogScale} {K : ℕ} {k : ℤ}
    {M d : ι → ℕ} (c : ∀ i, RoutingTemplate (M i) (d i))
    (p α q t : ℝ) (hK : 2 ≤ K) (hp : 0 < p) (hα : 0 < α) (hq : 0 ≤ q)
    (ht : t ≤ α / (4 * (K : ℝ)))
    (hU : Tendsto (fun i => ((c i).origin : ℝ)) l atTop)
    (hT : ∀ᶠ i in l, (RoutingTemplate.span (M i) (c i).gap
      (c i).baseLength (d i) : ℝ) ≤ t * ((c i).origin : ℝ)) :
    ∀ᶠ i in l, ∀ (r : PowerParams (1 / (K : ℝ)) K) (n : ℕ),
      r ∈ sequenceWindowActivations Z n k (globalRoutingWindows (c i)) →
      q * (input Z n) ^ (r.1.1 + α) < routingBufferRadius (c i) p := by
  obtain ⟨C, hC⟩ := exists_buffer_shift p q hp hq
  have hC' : q * (2 : ℝ) ^ (-C) < p / 32 := by linarith
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hslack := eventually_span_shift_le_activation_slack_of_fixed_ratio
    (fun i => ((c i).origin : ℝ))
    (fun i => (RoutingTemplate.span (M i) (c i).gap
      (c i).baseLength (d i) : ℝ))
    (K : ℝ) α (k : ℝ) C t hKpos hα ht hU hT
  have hpos := hU.eventually_ge_atTop (max 1 (-(k : ℝ)))
  filter_upwards [hslack, hpos] with i hi hOi
  intro r n hactive
  have hO : 1 ≤ (c i).origin := by
    have h : (1 : ℝ) ≤ ((c i).origin : ℝ) :=
      (le_max_left _ _).trans hOi
    exact_mod_cast h
  have hnum : 0 ≤ ((c i).origin : ℝ) + (k : ℝ) := by
    have h : -(k : ℝ) ≤ ((c i).origin : ℝ) :=
      (le_max_right _ _).trans hOi
    linarith
  obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hactive
  have hstart := globalRoutingWindow_start_ge_origin (c i) j
  have hrpos : 0 < r.1.1 := by
    exact lt_of_lt_of_le (by positivity) r.1.2.1
  have hzpos : 0 < Z.z n := by
    have hact := hj.1
    nlinarith
  have hprod : r.1.1 * Z.z n ≤ (K : ℝ) * Z.z n :=
    mul_le_mul_of_nonneg_right r.1.2.2 hzpos.le
  have hz : (((c i).origin : ℝ) + (k : ℝ)) / (K : ℝ) ≤ Z.z n := by
    apply (div_le_iff₀ hKpos).2
    linarith [hj.1]
  apply herror_of_global_window_margin_shift (c i) r n hO hα hq hp hC'
  · intro j'
    have hstart' := globalRoutingWindow_start_ge_origin (c i) j'
    have hαz := mul_le_mul_of_nonneg_left hz hα.le
    linarith
  · exact hactive

/-! A certificate's retained logarithmic anchor gives the original-index
tail, uniformly across all node lists. -/
theorem finiteSequenceRoutingTests_tail_of_log_lower
    {Z : LogScale} {K : ℕ} {k : ℤ} {p : ℝ}
    (s : FiniteSequenceRoutingCertificate Z K k p) (N : ℕ) (A : ℝ)
    (hprefix : ∀ m : ℕ, m < N → Z.z m < A)
    (hlower : ∀ v i, A ≤ Z.z (s.indices v i)) :
    ∀ n ∈ finiteSequenceRoutingTests s, N ≤ n := by
  intro n hn
  obtain ⟨v, _, hv⟩ := Finset.mem_biUnion.1 hn
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hv
  by_contra hN
  exact (not_lt_of_ge (hlower v i))
    (hprefix _ (Nat.lt_of_not_ge hN))

end ErdosSimilarityGrowingGaps
