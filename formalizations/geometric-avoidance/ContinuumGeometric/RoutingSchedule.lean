import ContinuumGeometric.RoutingEntropy
import ContinuumGeometric.CandidateBounds
import ContinuumGeometric.RoutingTemplate

/-!
All finite template parameters are chosen in dependency order: stride,
branching, depth, gap, and finally the logarithmic output position/window.
The table outcome and the center are absent from these choices.
-/
namespace ContinuumGeometric

noncomputable def routingActivationRate (K : ℕ) : ℝ :=
  1 / (2 * (candidateStride (1 / (K : ℝ)) : ℝ) * (K : ℝ))

theorem routingActivationRate_pos (K : ℕ) (hK : 2 ≤ K) :
    0 < routingActivationRate K := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hm := (candidateStride_gap (1 / (K : ℝ)) (by positivity)).1
  have hmr : (0 : ℝ) < candidateStride (1 / (K : ℝ)) := by exact_mod_cast hm
  unfold routingActivationRate
  positivity

structure RoutingSchedule (K : ℕ) (k : ℤ) (N : ℕ) (p : ℝ) where
  branching : ℕ
  depth : ℕ
  template : RoutingTemplate branching depth
  branching_ge_two : 2 ≤ branching
  depth_pos : 0 < depth
  length_pos : 0 < template.baseLength
  active_count_guard : 2 * (candidateStride (1 / (K : ℝ)) : ℝ) * (K : ℝ) ≤
    template.baseLength
  tail_guard : candidateTailStart K N k ≤ template.origin
  gap_guard : template.gap + 1 ≤ template.origin
  coefficient_guard : k.natAbs ≤ template.origin
  span_fits : RoutingTemplate.span branching template.gap template.baseLength depth ≤
    template.origin
  decay_pos : 0 < p * routingActivationRate K * ((branching : ℝ) - 1) / 2 -
    4 * Real.log 2
  no_default_small : (1 - (2 : ℝ) ^ (1 - (branching : ℝ))) ^ depth < p
  stable_boundary_small : (Fintype.card (RoutingEdge branching depth) : ℝ) *
    (2 : ℝ) ^ (3 - (template.gap : ℝ)) < p
  continuum_entropy_small :
    46080 * (branching : ℝ) ^ 2 * ((template.origin : ℝ) + 1) ^ 2 *
      Real.exp (-(p * routingActivationRate K * ((branching : ℝ) - 1) / 2 -
        4 * Real.log 2) * (template.baseLength : ℝ)) < p

/-- The actual finite complete tree can meet every numerical budget at once. -/
theorem exists_routing_schedule (K : ℕ) (hK : 2 ≤ K) (k : ℤ) (N : ℕ)
    (p : ℝ) (hp : 0 < p) : Nonempty (RoutingSchedule K k N p) := by
  have hη := routingActivationRate_pos K hK
  obtain ⟨M, hM, _, hκ⟩ := exists_branching_decay p (routingActivationRate K) hp hη
  obtain ⟨d, hd, hdefault⟩ := exists_default_depth_budget M hM p hp
  obtain ⟨g, _, hboundary⟩ := exists_stable_gap_budget
    (Fintype.card (RoutingEdge M d)) p hp 4
  let Lmin := Nat.ceil (2 * (candidateStride (1 / (K : ℝ)) : ℝ) * (K : ℝ)) + 1
  let Umin := max (candidateTailStart K N k) (max (g + 1) k.natAbs)
  have hMr : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  obtain ⟨U, L, hU, hL, hspan, hentropy⟩ := exists_late_entropy_schedule
    (46080 * (M : ℝ) ^ 2) p
    (p * routingActivationRate K * ((M : ℝ) - 1) / 2 - 4 * Real.log 2)
    (by positivity) hp hκ (RoutingTemplate.lengthCoefficient M d)
    (RoutingTemplate.gapCoefficient M d * g) Lmin Umin
  let c : RoutingTemplate M d := ⟨g, L, U⟩
  have hLL : 0 < L := by dsimp [Lmin] at hL; omega
  have hactive : 2 * (candidateStride (1 / (K : ℝ)) : ℝ) * (K : ℝ) ≤ (L : ℝ) := by
    have hceil := Nat.le_ceil (2 * (candidateStride (1 / (K : ℝ)) : ℝ) * (K : ℝ))
    have hLr : (Lmin : ℝ) ≤ L := by exact_mod_cast hL
    dsimp [Lmin] at hLr
    push_cast at hLr
    linarith
  have htail : candidateTailStart K N k ≤ U := (le_max_left _ _).trans hU
  have hgap : g + 1 ≤ U := (le_max_left _ _).trans ((le_max_right _ _).trans hU)
  have hcoeff : k.natAbs ≤ U := (le_max_right _ _).trans ((le_max_right _ _).trans hU)
  refine ⟨{
    branching := M
    depth := d
    template := c
    branching_ge_two := hM
    depth_pos := hd
    length_pos := hLL
    active_count_guard := hactive
    tail_guard := htail
    gap_guard := hgap
    coefficient_guard := hcoeff
    span_fits := ?_
    decay_pos := hκ
    no_default_small := hdefault
    stable_boundary_small := hboundary
    continuum_entropy_small := ?_
  }⟩
  · simpa only [c, RoutingTemplate.span_affine] using hspan
  · simpa only [c, mul_assoc] using hentropy

/-- Every actual node's finite candidate budget fits the chosen strict entropy
budget; its edge length may exceed the base length. -/
theorem routingSchedule_node_entropy_lt {K : ℕ} {k : ℤ} {N : ℕ} {p : ℝ}
    (s : RoutingSchedule K k N p) (P ell : ℕ)
    (hP : P ≤ (s.branching - 1) * candidateLabelBudget s.template.origin
      (RoutingTemplate.span s.branching s.template.gap s.template.baseLength s.depth) k)
    (hell : s.template.baseLength ≤ ell) :
    ((20 * (P * (3 + 2 ^ (2 * ell + 3)) + 5) ^ 2 : ℕ) : ℝ) *
      Real.exp (-(p * routingActivationRate K * ((s.branching : ℝ) - 1) / 2) *
        (ell : ℝ)) < p := by
  let T := RoutingTemplate.span s.branching s.template.gap s.template.baseLength s.depth
  have hbudget := candidateLabelBudget_le_nat s.template.origin T k
  have hcount : P ≤ s.branching * (s.template.origin + T + k.natAbs + 2) :=
    hP.trans ((Nat.mul_le_mul_left _ hbudget).trans
      (Nat.mul_le_mul_right _ (Nat.sub_le s.branching 1)))
  have habs : (k.natAbs : ℝ) = |(k : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
  have hPr : (P : ℝ) ≤ (s.branching : ℝ) *
      ((s.template.origin : ℝ) + T + |(k : ℝ)| + 2) := by
    rw [← habs]
    exact_mod_cast hcount
  have hkr : |(k : ℝ)| ≤ (s.template.origin : ℝ) := by
    rw [← habs]
    exact_mod_cast s.coefficient_guard
  have h := (signature_entropy_position_bound s.branching P s.template.origin T ell
    s.template.baseLength (k : ℝ)
    (p * routingActivationRate K * ((s.branching : ℝ) - 1) / 2)
    (by have := s.branching_ge_two; omega) s.span_fits hkr hPr hell s.decay_pos).trans_lt
      s.continuum_entropy_small
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat] using h

end ContinuumGeometric
