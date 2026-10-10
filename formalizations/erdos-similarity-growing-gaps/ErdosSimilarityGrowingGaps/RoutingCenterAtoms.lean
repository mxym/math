import ErdosSimilarityGrowingGaps.NoDefaultProbability
import ErdosSimilarityGrowingGaps.RoutingProbabilityFinite

/-! Adapted in this repository from the finite geometric routing construction.
The real-logarithm sampler and variable schedule are supplied separately. -/

/-!
Actual center atoms partition the finite routing outcomes.  Every route that
uses a default child has an actual prefix vertex whose selector reads are all
false.  A single such vertex and prefix persist for every assignment in its
center atom, because the atom fixes the actual center readouts.
-/
namespace ErdosSimilarityGrowingGaps

open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency false

/-- An actual default route supplies an actual all-false vertex on that route. -/
theorem actual_default_vertex_exists {M d : ℕ} (c : RoutingTemplate M d)
    (hM : 0 < M) (σ : SelectorAddress c → Bool) (x : ℝ)
    (hnot : ¬routeHasNoDefault c hM σ x) :
    ∃ v : InternalNode M d,
      (List.ofFn v.2).IsPrefix (List.ofFn (routeLeaf c hM σ x)) ∧
        ∀ i : Fin (M - 1), nodeSelectorBits c σ x v i = false := by
  have hex : ∃ j : Fin d, routeLeaf c hM σ x j = defaultChild M hM := by
    simpa only [routeHasNoDefault, not_forall, not_not] using hnot
  obtain ⟨j, hj⟩ := hex
  let v : InternalNode M d := nodeOfPrefix ((List.ofFn (routeLeaf c hM σ x)).take j.val)
    (by simp)
  refine ⟨v, ?_, ?_⟩
  · simp only [v, nodeOfPrefix_path]
    exact List.take_prefix _ _
  · have hc := (routeLeaf_eq_iff_prefix_choices c hM σ x (routeLeaf c hM σ x)).1 rfl j
    apply (chooseRoutingChild_eq_default_iff_all_false M hM _).1
    exact hc.trans hj

/-- Canonical full-table extension of a center's edge-bit readout. -/
def centerTableAssignment {M d : ℕ} (c : RoutingTemplate M d)
    (bits : SelectorEdge M d → Bool) : SelectorAddress c → Bool := fun s => bits s.1

theorem centerTableAssignment_satisfies_atom {M d : ℕ} (c : RoutingTemplate M d)
    (x : ℝ) (bits : SelectorEdge M d → Bool) :
    centerExposureAtom (actualCenterExposure c x bits) (centerTableAssignment c bits) := by
  apply (actual_center_atom_iff_reads c x bits _).2
  intro e
  rfl

/-- The canonical assignment's default vertex has all its exposed edge bits false. -/
theorem centerTableAssignment_default_vertex_exists {M d : ℕ} (c : RoutingTemplate M d)
    (hM : 0 < M) (x : ℝ) (bits : SelectorEdge M d → Bool)
    (hnot : ¬routeHasNoDefault c hM (centerTableAssignment c bits) x) :
    ∃ v : InternalNode M d,
      (List.ofFn v.2).IsPrefix (List.ofFn (routeLeaf c hM (centerTableAssignment c bits) x)) ∧
        ∀ i : Fin (M - 1), bits ⟨v, i⟩ = false := by
  obtain ⟨v, hp, hb⟩ := actual_default_vertex_exists c hM (centerTableAssignment c bits) x hnot
  refine ⟨v, hp, ?_⟩
  intro i
  exact hb i

/-- One vertex works for EVERY selector assignment satisfying the same actual atom.
The common vertex is chosen using the canonical full-table extension only.
-/
theorem center_atom_default_vertex_exists {M d : ℕ} (c : RoutingTemplate M d)
    (hM : 0 < M) (x : ℝ) (bits : SelectorEdge M d → Bool)
    (hnot : ¬routeHasNoDefault c hM (centerTableAssignment c bits) x) :
    ∃ v : InternalNode M d, (∀ i : Fin (M - 1), bits ⟨v, i⟩ = false) ∧
      ∀ σ : SelectorAddress c → Bool,
        centerExposureAtom (actualCenterExposure c x bits) σ →
          (List.ofFn v.2).IsPrefix (List.ofFn (routeLeaf c hM σ x)) := by
  obtain ⟨v, hp, hb⟩ := centerTableAssignment_default_vertex_exists c hM x bits hnot
  refine ⟨v, hb, ?_⟩
  intro σ hσ
  rw [← center_atom_routeLeaf_eq c hM x bits (centerTableAssignment c bits) σ
    (centerTableAssignment_satisfies_atom c x bits) hσ]
  exact hp

noncomputable def centerAssignmentReadout {M d : ℕ} (c : RoutingTemplate M d)
    (x : ℝ) (σ : SelectorAddress c → Bool) : SelectorEdge M d → Bool :=
  fun e => σ (selectorAddress c e x)

/-- Membership in a center atom is exactly equality to its unique actual readout. -/
theorem actual_center_atom_iff_readout {M d : ℕ} (c : RoutingTemplate M d)
    (x : ℝ) (bits : SelectorEdge M d → Bool) (σ : SelectorAddress c → Bool) :
    centerExposureAtom (actualCenterExposure c x bits) σ ↔ bits = centerAssignmentReadout c x σ := by
  rw [actual_center_atom_iff_reads]
  constructor
  · intro h
    funext e
    exact (h e).symm
  · intro h e
    exact (congrFun h e).symm

theorem tableProbability_congr {S T : Type*} [Fintype S] [Fintype T]
    (p : ℝ) (E F : FiniteRoutingTables S T → Prop) (hEF : ∀ ω, E ω ↔ F ω) :
    tableProbability p E = tableProbability p F := by
  have heq : E = F := funext (fun ω => propext (hEF ω))
  rw [heq]

/-- Exact partition by the ACTUAL center atoms for any finite-table event.
No positivity restriction on p is needed for this finite algebra identity.
-/
theorem actual_center_atom_partition {M d : ℕ} (c : RoutingTemplate M d)
    (hd : 0 < d) (p x : ℝ)
    (E : FiniteRoutingTables (SelectorAddress c) (TerminalAddress c hd) → Prop) :
    tableProbability p E = ∑ bits : SelectorEdge M d → Bool,
      tableProbability p (fun ω => centerExposureAtom (actualCenterExposure c x bits) ω.selectors ∧ E ω) := by
  simp_rw [tableProbability_eq_weight_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  rw [← Finset.mul_sum]
  apply congrArg (fun a : ℝ => finiteRoutingWeight p ω * a)
  by_cases hE : E ω
  · simp only [hE, and_true, ite_true]
    simp_rw [actual_center_atom_iff_readout]
    simp
  · simp [hE]

end ErdosSimilarityGrowingGaps
