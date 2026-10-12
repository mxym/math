import Entry002.Sieve
import Entry002.Embedding

/-!
# The genuine small-step branch

Finite balls and injectivity of an arbitrary full planar integral-coordinate
embedding imply a positive lower bound on nonzero vector lengths. At smaller
step sizes every actual lattice graph is edgeless, so the empty signed-prime
selection gives the `Q² = 1` component bound in v3 Section 2.
-/

namespace Entry002

open Module

variable {L : Type*} [AddCommGroup L]
    (b : Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)

/-- Every allowed full planar lattice embedding has a positive minimum
separation from zero. This uses proved finite lattice balls, not a discreteness
or shortest-vector premise. -/
theorem planarEmbedding_positive_separation :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : L, x ≠ 0 → δ ≤ ‖planarEmbedding b e x‖ := by
  classical
  let C : Set L := {x | ‖planarEmbedding b e x‖ ≤ 1 ∧ x ≠ 0}
  have hf : C.Finite := (planarEmbedding_finite_balls b e 1).subset
    (fun _ hx => hx.1)
  by_cases hne : C.Nonempty
  · obtain ⟨z, hz, hmin⟩ := Set.exists_min_image C (fun x => ‖planarEmbedding b e x‖) hf hne
    have hz0 : planarEmbedding b e z ≠ 0 := by
      intro heq
      apply hz.2
      apply planarEmbedding_injective b e
      simpa using heq
    refine ⟨min 1 ‖planarEmbedding b e z‖, lt_min zero_lt_one (norm_pos_iff.mpr hz0), ?_⟩
    intro x hx
    by_cases hnorm : ‖planarEmbedding b e x‖ ≤ 1
    · exact (min_le_right _ _).trans (hmin x ⟨hnorm, hx⟩)
    · exact (min_le_left _ _).trans (not_le.mp hnorm).le
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x hx
    by_cases hnorm : ‖planarEmbedding b e x‖ ≤ 1
    · exact (hne ⟨x, hnorm, hx⟩).elim
    · exact (not_le.mp hnorm).le

@[simp] theorem planarEmbedding_sub_lattice (x y : L) :
    planarEmbedding b e (x - y) = planarEmbedding b e x - planarEmbedding b e y := by
  unfold planarEmbedding
  calc
    _ = e ((fun i => (b.repr x i : ℝ)) - (fun i => (b.repr y i : ℝ))) := by
      congr 1
      funext i
      simp
    _ = _ := e.map_sub _ _

/-- No two distinct actual lattice vertices can be adjacent below the
proved separation scale. -/
theorem latticeGraph_tiny_eq_bot (A : Set L) {δ D : ℝ}
    (hδ : ∀ x : L, x ≠ 0 → δ ≤ ‖planarEmbedding b e x‖) (hD : D < δ) :
    latticeGraph b e D A = ⊥ := by
  apply SimpleGraph.eq_bot_iff_forall_not_adj.mpr
  intro x y hxy
  have hne : x.val ≠ y.val := fun h => hxy.1 (Subtype.ext h)
  have hsep := hδ (x.val - y.val) (sub_ne_zero.mpr hne)
  rw [planarEmbedding_sub_lattice] at hsep
  exact (not_lt_of_ge hsep) (hxy.2.trans_lt hD)

/-- The actual reachable component is a singleton at small step size. -/
theorem latticeGraph_tiny_component_eq_singleton (A : Set L) {δ D : ℝ}
    (hδ : ∀ x : L, x ≠ 0 → δ ≤ ‖planarEmbedding b e x‖) (hD : D < δ) (root : A) :
    componentVertices (latticeGraph b e D A) root = {root} := by
  ext y
  simp [componentVertices, latticeGraph_tiny_eq_bot b e A hδ hD,
    SimpleGraph.reachable_bot, eq_comm]

theorem latticeGraph_tiny_component_bound (A : Set L) {δ D : ℝ}
    (hδ : ∀ x : L, x ≠ 0 → δ ≤ ‖planarEmbedding b e x‖) (hD : D < δ) :
    UniformComponentBound (latticeGraph b e D A) 1 := by
  intro root
  rw [latticeGraph_tiny_component_eq_singleton b e A hδ hD root]
  exact ⟨Set.finite_singleton root, by simp⟩

/-- The actual no-infinite-injective-walk conclusion at the small-step scale. -/
theorem latticeGraph_tiny_no_infinite_walk (A : Set L) {δ D : ℝ}
    (hδ : ∀ x : L, x ≠ 0 → δ ≤ ‖planarEmbedding b e x‖) (hD : D < δ)
    (w : ℕ → A) (hinj : Function.Injective w)
    (hstep : ∀ n, (latticeGraph b e D A).Adj (w n) (w (n + 1))) : False :=
  no_infinite_injective_walk _ (latticeGraph_tiny_component_bound b e A hδ hD)
    w hstep hinj

/-- The manuscript's small-step sieve conclusion is proved with no analytic
sieve input: use the empty selected-prime family and `Q² = 1`. -/
theorem finiteSieve_small_step_branch (data : SignedResidueData L) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ D : ℝ, D < δ →
      ∃ S : Finset ℕ, (∀ p ∈ S, p ∈ data.primes) ∧
        UniformComponentBound (latticeGraph b e D (avoiding data S)) (S.prod id ^ 2) := by
  obtain ⟨δ, hδpos, hδ⟩ := planarEmbedding_positive_separation b e
  refine ⟨δ, hδpos, ?_⟩
  intro D hD
  refine ⟨∅, by simp, ?_⟩
  simpa using latticeGraph_tiny_component_bound b e (avoiding data ∅) hδ hD

end Entry002
