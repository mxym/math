import ContinuumRemainder.Counting
import ContinuumRemainder.ErrorSchedule
import ContinuumGeometric.RoutingChoices
import ContinuumGeometric.RoutingEntropy
import ContinuumGeometric.RoutingTemplate

set_option autoImplicit false

namespace ContinuumRemainder

open Set ContinuumGeometric

noncomputable def sampleActivationRate {A : Set ℝ} {s₀ : ℝ} {h : ℕ}
    (s₁ : ℝ) (C : SampledLogConfiguration A s₀ h) : ℝ :=
  1 / (2 * (s₁ * C.B))

theorem sampleActivationRate_pos {A : Set ℝ} {s₀ : ℝ} {h : ℕ}
    (s₁ : ℝ) (C : SampledLogConfiguration A s₀ h) (hs₁ : 0 < s₁) :
    0 < sampleActivationRate s₁ C := by
  unfold sampleActivationRate
  positivity [C.B_pos]

/-- All choices are made for the actual prescribed set, before the random
tables or center. The double-buffer cost uses the actual finest grid. -/
structure SampleRoutingSchedule (A : Set ℝ) (s₀ s₁ α₀ : ℝ)
    (k : ℤ) (q h : ℕ) (p : ℝ) where
  sample : SampledLogConfiguration A s₀ h
  branching : ℕ
  depth : ℕ
  template : RoutingTemplate branching depth
  branching_ge_two : 2 ≤ branching
  depth_pos : 0 < depth
  length_pos : 0 < template.baseLength
  active_count_guard : 2 * (s₁ * sample.B) ≤ template.baseLength
  start_guard : s₁ * sample.z 0 - k ≤ template.origin
  origin_ge_four : 4 ≤ template.origin
  gap_guard : template.gap + 1 ≤ template.origin
  coefficient_guard : k.natAbs ≤ template.origin
  origin_shift_nonneg : 0 ≤ (template.origin : ℝ) + (k : ℝ)
  span_fits : RoutingTemplate.span branching template.gap template.baseLength depth ≤
    template.origin
  decay_pos : 0 < p * sampleActivationRate s₁ sample * ((branching : ℝ) - 1) / 2 -
    4 * Real.log 2
  no_default_small : (1 - (2 : ℝ) ^ (1 - (branching : ℝ))) ^ depth < p
  stable_boundary_small : (Fintype.card (RoutingEdge branching depth) : ℝ) *
    (2 : ℝ) ^ (3 - (template.gap : ℝ)) < p
  continuum_entropy_small :
    46080 * (branching : ℝ) ^ 2 * ((template.origin : ℝ) + 1) ^ 2 *
      Real.exp (-(p * sampleActivationRate s₁ sample * ((branching : ℝ) - 1) / 2 -
        4 * Real.log 2) * (template.baseLength : ℝ)) < p
  radius_pos : 0 < errorRadius q k α₀ s₁ template.origin
  actual_buffer_small :
    4 * ((2 ^ (template.origin + RoutingTemplate.span branching template.gap
      template.baseLength depth + 2) : ℕ) : ℝ) *
        errorRadius q k α₀ s₁ template.origin < p

/-- The source hypothesis discharges sampling, and the coupled logarithmic
schedule meets all entropy and positive-error budgets arbitrarily late. -/
theorem exists_sample_routing_schedule_late (A : Set ℝ) (hA : LogSyndetic A)
    (s₀ s₁ α₀ : ℝ) (hs₀ : 0 < s₀) (hs₁ : s₀ < s₁) (hα : 0 < α₀)
    (k : ℤ) (q h : ℕ) (p : ℝ) (hp : 0 < p) (Ufloor : ℕ) :
    ∃ S : SampleRoutingSchedule A s₀ s₁ α₀ k q h p, Ufloor ≤ S.template.origin := by
  obtain ⟨C⟩ := hA.exists_sampledLogConfiguration s₀ hs₀ h
  have hs₁pos : 0 < s₁ := hs₀.trans hs₁
  have hη := sampleActivationRate_pos s₁ C hs₁pos
  obtain ⟨M, hM, _, hκ⟩ := exists_branching_decay p (sampleActivationRate s₁ C) hp hη
  obtain ⟨d, hd, hdefault⟩ := exists_default_depth_budget M hM p hp
  obtain ⟨g, _, hboundary⟩ := exists_stable_gap_budget
    (Fintype.card (RoutingEdge M d)) p hp 4
  let Lmin := Nat.ceil (2 * (s₁ * C.B)) + 1
  let start := Nat.ceil (s₁ * C.z 0 + |(k : ℝ)|) + 4
  let Umin := max Ufloor (max start (max (g + 1) k.natAbs))
  have hMr : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  obtain ⟨U, L, hU, hL, hspan, hUk, hentropy, hrad, hbuffer⟩ :=
    exists_late_robust_schedule (46080 * (M : ℝ) ^ 2) p
      (p * sampleActivationRate s₁ C * ((M : ℝ) - 1) / 2 - 4 * Real.log 2)
      α₀ s₁ (by positivity) hp hκ hα hs₁pos q k
      (RoutingTemplate.lengthCoefficient M d)
      (RoutingTemplate.gapCoefficient M d * g) Lmin Umin
  let c : RoutingTemplate M d := ⟨g, L, U⟩
  have hLL : 0 < L := by dsimp [Lmin] at hL; omega
  have hactive : 2 * (s₁ * C.B) ≤ (L : ℝ) := by
    have hceil := Nat.le_ceil (2 * (s₁ * C.B))
    have hLr : (Lmin : ℝ) ≤ L := by exact_mod_cast hL
    dsimp [Lmin] at hLr
    push_cast at hLr
    linarith
  have hstart : start ≤ U :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hU)
  have hgap : g + 1 ≤ U :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hU))
  have hcoeff : k.natAbs ≤ U :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hU))
  have hstartReal : s₁ * C.z 0 - k ≤ (U : ℝ) := by
    have hc := Nat.le_ceil (s₁ * C.z 0 + |(k : ℝ)|)
    have hu : (start : ℝ) ≤ U := by exact_mod_cast hstart
    have hk := neg_abs_le (k : ℝ)
    dsimp [start] at hu
    push_cast at hu
    linarith
  have hfour : 4 ≤ U := by dsimp [start] at hstart; omega
  refine ⟨{
    sample := C
    branching := M
    depth := d
    template := c
    branching_ge_two := hM
    depth_pos := hd
    length_pos := hLL
    active_count_guard := hactive
    start_guard := hstartReal
    origin_ge_four := hfour
    gap_guard := hgap
    coefficient_guard := hcoeff
    origin_shift_nonneg := hUk
    span_fits := ?_
    decay_pos := hκ
    no_default_small := hdefault
    stable_boundary_small := hboundary
    continuum_entropy_small := ?_
    radius_pos := hrad
    actual_buffer_small := ?_
  }, (le_max_left _ _).trans hU⟩
  · simpa only [c, RoutingTemplate.span_affine] using hspan
  · simpa only [c, mul_assoc] using hentropy
  · simpa only [c, RoutingTemplate.span_affine] using hbuffer

theorem exists_sample_routing_schedule (A : Set ℝ) (hA : LogSyndetic A)
    (s₀ s₁ α₀ : ℝ) (hs₀ : 0 < s₀) (hs₁ : s₀ < s₁) (hα : 0 < α₀)
    (k : ℤ) (q h : ℕ) (p : ℝ) (hp : 0 < p) :
    Nonempty (SampleRoutingSchedule A s₀ s₁ α₀ k q h p) := by
  obtain ⟨S, _⟩ := exists_sample_routing_schedule_late A hA s₀ s₁ α₀ hs₀ hs₁ hα k q h p hp 0
  exact ⟨S⟩

theorem sampleSchedule_node_entropy_lt {A : Set ℝ} {s₀ s₁ α₀ : ℝ}
    {k : ℤ} {q h : ℕ} {p : ℝ}
    (S : SampleRoutingSchedule A s₀ s₁ α₀ k q h p) (P ell : ℕ)
    (hP : P ≤ (S.branching - 1) * candidateLabelBudget S.template.origin
      (RoutingTemplate.span S.branching S.template.gap S.template.baseLength S.depth) k)
    (hell : S.template.baseLength ≤ ell) :
    ((20 * (P * (3 + 2 ^ (2 * ell + 3)) + 5) ^ 2 : ℕ) : ℝ) *
      Real.exp (-(p * sampleActivationRate s₁ S.sample * ((S.branching : ℝ) - 1) / 2) *
        (ell : ℝ)) < p := by
  let T := RoutingTemplate.span S.branching S.template.gap S.template.baseLength S.depth
  have hbudget := candidateLabelBudget_le_nat S.template.origin T k
  have hcount : P ≤ S.branching * (S.template.origin + T + k.natAbs + 2) :=
    hP.trans ((Nat.mul_le_mul_left _ hbudget).trans
      (Nat.mul_le_mul_right _ (Nat.sub_le S.branching 1)))
  have habs : (k.natAbs : ℝ) = |(k : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
  have hPr : (P : ℝ) ≤ (S.branching : ℝ) *
      ((S.template.origin : ℝ) + T + |(k : ℝ)| + 2) := by
    rw [← habs]
    exact_mod_cast hcount
  have hkr : |(k : ℝ)| ≤ (S.template.origin : ℝ) := by
    rw [← habs]
    exact_mod_cast S.coefficient_guard
  have hb := (signature_entropy_position_bound S.branching P S.template.origin T ell
    S.template.baseLength (k : ℝ)
    (p * sampleActivationRate s₁ S.sample * ((S.branching : ℝ) - 1) / 2)
    (by have := S.branching_ge_two; omega) S.span_fits hkr hPr hell S.decay_pos).trans_lt
      S.continuum_entropy_small
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat] using hb


end ContinuumRemainder
