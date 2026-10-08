import ContinuumRemainder.LogRouting
import ContinuumGeometric.RoutingEntropy

namespace ContinuumRemainder
open ContinuumGeometric
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency false

noncomputable def logActiveLocalCandidates {M d P : ℕ} (c : RoutingTemplate M d)
    (v : InternalNode M d) (children : Fin P → Fin (M - 1)) (logs : Fin P → ℝ)
    {s₀ s₁ : ℝ} (k : ℤ) (r : PowerParams s₀ s₁) : Finset (Fin P) :=
  Finset.univ.filter fun i => r ∈ logActivation (logs i) k
    (c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v, children i⟩))
    ((c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v, children i⟩) : ℝ) +
      c.edgeLength (RoutingTemplate.selectorRoutingEdge ⟨v, children i⟩))

noncomputable def logActiveLocalIndex {M d P : ℕ} (c : RoutingTemplate M d)
    (v : InternalNode M d) (children : Fin P → Fin (M - 1)) (logs : Fin P → ℝ)
    {s₀ s₁ : ℝ} (k : ℤ) (r : PowerParams s₀ s₁) :
    Fin (logActiveLocalCandidates c v children logs k r).card → Fin P :=
  fun j => ((logActiveLocalCandidates c v children logs k r).equivFin.symm j).val

theorem logActiveLocalIndex_injective {M d P : ℕ} (c : RoutingTemplate M d)
    (v : InternalNode M d) (children : Fin P → Fin (M - 1)) (logs : Fin P → ℝ)
    {s₀ s₁ : ℝ} (k : ℤ) (r : PowerParams s₀ s₁) :
    Function.Injective (logActiveLocalIndex c v children logs k r) := by
  intro i j hij
  exact ((logActiveLocalCandidates c v children logs k r).equivFin.symm).injective
    (Subtype.ext hij)

theorem logActiveLocalIndex_active {M d P : ℕ} (c : RoutingTemplate M d)
    (v : InternalNode M d) (children : Fin P → Fin (M - 1)) (logs : Fin P → ℝ)
    {s₀ s₁ : ℝ} (k : ℤ) (r : PowerParams s₀ s₁)
    (j : Fin (logActiveLocalCandidates c v children logs k r).card) :
    r ∈ logActivation (logs (logActiveLocalIndex c v children logs k r j)) k
      (c.edgeStart (RoutingTemplate.selectorRoutingEdge
        ⟨v, children (logActiveLocalIndex c v children logs k r j)⟩))
      ((c.edgeStart (RoutingTemplate.selectorRoutingEdge
        ⟨v, children (logActiveLocalIndex c v children logs k r j)⟩) : ℝ) +
        c.edgeLength (RoutingTemplate.selectorRoutingEdge
          ⟨v, children (logActiveLocalIndex c v children logs k r j)⟩)) := by
  exact (Finset.mem_filter.1
    (((logActiveLocalCandidates c v children logs k r).equivFin.symm j).property)).2

theorem logLocalAllMiss_iff_active_tests {M d P : ℕ} (c : RoutingTemplate M d)
    (hM : 0 < M) (hd : 0 < d) (s₀ s₁ x : ℝ) (k : ℤ)
    (v : InternalNode M d) (children : Fin P → Fin (M - 1)) (logs : Fin P → ℝ)
    (r : PowerParams s₀ s₁)
    (ω : FiniteRoutingTables (SelectorAddress c) (TerminalAddress c hd)) :
    logLocalAllMiss c hM hd s₀ s₁ x k (fun i => ⟨v, children i⟩) logs r ω ↔
      localRoutingAllMiss
        (localOwnAddresses c v (fun j => children (logActiveLocalIndex c v children logs k r j))
          (fun j => powerPoint (logInput (logs (logActiveLocalIndex c v children logs k r j)))
            ((2 : ℝ) ^ k) (x, r)))
        (localTerminalAddresses c hM hd v
          (fun j => children (logActiveLocalIndex c v children logs k r j))
          (fun j => powerPoint (logInput (logs (logActiveLocalIndex c v children logs k r j)))
            ((2 : ℝ) ^ k) (x, r))) ω := by
  constructor
  · intro h j
    exact h _ (logActiveLocalIndex_active c v children logs k r j)
  · intro h i hi
    have himem : i ∈ logActiveLocalCandidates c v children logs k r :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩
    obtain ⟨j, hj⟩ := ((logActiveLocalCandidates c v children logs k r).equivFin.symm).surjective
      ⟨i, himem⟩
    have heq : logActiveLocalIndex c v children logs k r j = i := congrArg Subtype.val hj
    simpa only [localRoutingSuccess, localOwnAddresses, localTerminalAddresses, heq] using h j

/-- Exact joint failure on the genuine center atom for EVERY fixed real
parameter. Both own and terminal separation come from actual dyadic geometry. -/
theorem log_fixed_parameter_joint_miss {M d P : ℕ} (c : RoutingTemplate M d)
    (hM : 0 < M) (hd : 0 < d) (hL : 0 < c.baseLength) (hU : 4 ≤ c.origin)
    (p s₀ s₁ x : ℝ) (k : ℤ)
    (bits : SelectorEdge M d → Bool) (v : InternalNode M d)
    (children : Fin P → Fin (M - 1)) (logs : Fin P → ℝ)
    (hgap : ∀ r : PowerParams s₀ s₁, ∀ i j, i ≠ j → children i = children j →
      3 ≤ |r.1.1 * logs j - r.1.1 * logs i|) (r : PowerParams s₀ s₁) :
    tableProbability p (fun ω => centerExposureAtom (actualCenterExposure c x bits) ω.selectors ∧
      logLocalAllMiss c hM hd s₀ s₁ x k (fun i => ⟨v, children i⟩) logs r ω) =
    tableProbability (T := TerminalAddress c hd) p
      (fun ω => centerExposureAtom (actualCenterExposure c x bits) ω.selectors) *
        (1 - p / 2) ^ (logActiveLocalCandidates c v children logs k r).card := by
  let ix := logActiveLocalIndex c v children logs k r
  have hsep := log_local_address_separation c hM hd hL hU s₀ s₁ x k bits v
    (fun j => children (ix j)) (fun j => logs (ix j)) r (by
      intro i j hij hc
      exact hgap r (ix i) (ix j)
        (fun he => hij (logActiveLocalIndex_injective c v children logs k r he)) hc)
    (fun j => logActiveLocalIndex_active c v children logs k r j)
  have hevent : (fun ω => centerExposureAtom (actualCenterExposure c x bits) ω.selectors ∧
      logLocalAllMiss c hM hd s₀ s₁ x k (fun i => ⟨v, children i⟩) logs r ω) =
    (fun ω => centerExposureAtom (actualCenterExposure c x bits) ω.selectors ∧
      localRoutingAllMiss
        (localOwnAddresses c v (fun j => children (ix j))
          (fun j => powerPoint (logInput (logs (ix j))) ((2 : ℝ) ^ k) (x, r)))
        (localTerminalAddresses c hM hd v (fun j => children (ix j))
          (fun j => powerPoint (logInput (logs (ix j))) ((2 : ℝ) ^ k) (x, r))) ω) := by
    funext ω
    exact propext (and_congr_right fun _ => logLocalAllMiss_iff_active_tests
      c hM hd s₀ s₁ x k v children logs r ω)
  rw [hevent]
  exact joint_center_atom_all_miss p (actualCenterExposure c x bits) _ _ hsep

/-- The representative union bound now concerns ACTUAL routing successes, with
the actual real parameter rectangle and the exact active-index joint law. -/
theorem log_continuum_joint_miss_bound {M d P : ℕ} (c : RoutingTemplate M d)
    (hM : 0 < M) (hd : 0 < d) (hL : 0 < c.baseLength) (hU : 4 ≤ c.origin)
    (p s₀ s₁ x η : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (hs : s₀ ≤ s₁)
    (k : ℤ)
    (bits : SelectorEdge M d → Bool) (v : InternalNode M d)
    (children : Fin P → Fin (M - 1)) (logs : Fin P → ℝ)
    (hgap : ∀ r : PowerParams s₀ s₁, ∀ i j, i ≠ j → children i = children j →
      3 ≤ |r.1.1 * logs j - r.1.1 * logs i|) (ell : ℕ)
    (hell : ∀ i, c.edgeLength (RoutingTemplate.selectorRoutingEdge ⟨v, children i⟩) = ell)
    (hmany : ∀ r : PowerParams s₀ s₁, η * ((M : ℝ) - 1) * ell ≤
      (logActiveLocalCandidates c v children logs k r).card) :
    tableProbability p (fun ω => centerExposureAtom (actualCenterExposure c x bits) ω.selectors ∧
      ∃ r : PowerParams s₀ s₁,
        logLocalAllMiss c hM hd s₀ s₁ x k (fun i => ⟨v, children i⟩) logs r ω) ≤
    tableProbability (T := TerminalAddress c hd) p
      (fun ω => centerExposureAtom (actualCenterExposure c x bits) ω.selectors) *
      (20 * (P * (3 + 2 ^ (2 * ell + 3)) + 5) ^ 2 : ℕ) *
      Real.exp (-(p * η * ((M : ℝ) - 1) / 2) * ell) := by
  classical
  obtain ⟨reps, hcard, hrep⟩ := log_routing_local_representatives c hM hd hL s₀ s₁ x hs k
    (fun i => ⟨v, children i⟩) logs ell hell
  have hub := tableProbability_union_bound p hp₀ hp₁ reps
    (fun ω => centerExposureAtom (actualCenterExposure c x bits) ω.selectors ∧
      ∃ r : PowerParams s₀ s₁,
        logLocalAllMiss c hM hd s₀ s₁ x k (fun i => ⟨v, children i⟩) logs r ω)
    (fun r ω => centerExposureAtom (actualCenterExposure c x bits) ω.selectors ∧
      logLocalAllMiss c hM hd s₀ s₁ x k (fun i => ⟨v, children i⟩) logs r ω) (by
        intro ω hω
        obtain ⟨ha, r, hr⟩ := hω
        obtain ⟨r', hr', heq⟩ := hrep r
        exact ⟨r', hr', ha, (heq ω).2 hr⟩)
  apply hub.trans
  have ha := tableProbability_nonneg (T := TerminalAddress c hd) p hp₀ hp₁
    (fun ω => centerExposureAtom (actualCenterExposure c x bits) ω.selectors)
  calc
    _ ≤ ∑ _r ∈ reps,
        tableProbability (T := TerminalAddress c hd) p
          (fun ω => centerExposureAtom (actualCenterExposure c x bits) ω.selectors) *
        Real.exp (-(p * η * ((M : ℝ) - 1) / 2) * ell) := by
      apply Finset.sum_le_sum
      intro r _
      rw [log_fixed_parameter_joint_miss c hM hd hL hU p s₀ s₁ x k bits v
        children logs hgap r]
      exact mul_le_mul_of_nonneg_left (fair_selector_terminal_miss_window_bound p η hp₀ hp₁
        M _ ell (hmany r)) ha
    _ = tableProbability (T := TerminalAddress c hd) p
        (fun ω => centerExposureAtom (actualCenterExposure c x bits) ω.selectors) *
      (reps.card : ℝ) * Real.exp (-(p * η * ((M : ℝ) - 1) / 2) * ell) := by
      simp [mul_comm, mul_left_comm, mul_assoc]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      apply mul_le_mul_of_nonneg_left _ ha
      exact_mod_cast hcard

end ContinuumRemainder
