import Entry002.Graphs

/-!
# Finite nonisolated vertices and the exceptional graph

Section 9 of the v3 paper bounds the vertices belonging to close pairs; the
exceptional set itself need not be finite. The graph lemma below consumes just
that finite close-pair conclusion. Isolated vertices contribute singleton
components, and every other component lies in the finite nonisolated set.
-/

namespace Entry002

universe u

variable {V : Type u} (G : SimpleGraph V)

/-- Vertices appearing in some graph edge. -/
def nonisolatedVertices : Set V := {x | ∃ y, G.Adj x y}

/-- The endpoint of a walk is either its starting vertex or has a neighbor. -/
theorem reachable_eq_or_nonisolated {x y : V} (h : G.Reachable x y) :
    y = x ∨ y ∈ nonisolatedVertices G := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact Or.inl rfl
  | @cons x z y hxz p ih =>
      rcases ih with heq | hy
      · subst y
        exact Or.inr ⟨x, hxz.symm⟩
      · exact Or.inr hy

/-- A component containing a nonisolated vertex consists entirely of
nonisolated vertices. -/
theorem component_subset_nonisolated {x : V} (hx : x ∈ nonisolatedVertices G) :
    componentVertices G x ⊆ nonisolatedVertices G := by
  intro y hy
  rcases reachable_eq_or_nonisolated G hy with heq | hy'
  · simpa [heq] using hx
  · exact hy'

/-- A vertex with no neighbors has exactly its singleton as component. -/
theorem component_eq_singleton_of_isolated {x : V}
    (hx : x ∉ nonisolatedVertices G) : componentVertices G x = {x} := by
  ext y
  constructor
  · intro hy
    rcases reachable_eq_or_nonisolated G hy.symm with heq | hx'
    · exact Set.mem_singleton_iff.mpr heq.symm
    · exact (hx hx').elim
  · intro hy
    have heq := Set.mem_singleton_iff.mp hy
    subst y
    exact SimpleGraph.Reachable.rfl

/-- Finitely many vertices belonging to edges give a uniform component bound.
No finiteness assumption is made on the full vertex set or the isolated vertices. -/
theorem uniformComponentBound_of_finite_nonisolated
    (hfinite : (nonisolatedVertices G).Finite) :
    UniformComponentBound G (max 1 (nonisolatedVertices G).ncard) := by
  intro x
  by_cases hx : x ∈ nonisolatedVertices G
  · have hsub := component_subset_nonisolated G hx
    exact ⟨hfinite.subset hsub,
      (Set.ncard_le_ncard hsub hfinite).trans (Nat.le_max_right _ _)⟩
  · rw [component_eq_singleton_of_isolated G hx]
    exact ⟨Set.finite_singleton x, by
      simp only [Set.ncard_singleton]
      exact Nat.le_max_left 1 (nonisolatedVertices G).ncard⟩

end Entry002
