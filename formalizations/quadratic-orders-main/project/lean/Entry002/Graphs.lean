import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card

/-!
# The graph consequence in the quadratic-order moat theorem

The main arithmetic and sieve theorem must supply `UniformComponentBound`.
This file proves its finite injective-walk consequence without assuming a bound
on walks separately. All components are the actual `SimpleGraph.Reachable` sets.
-/

namespace Entry002

universe u

variable {V : Type u} (G : SimpleGraph V)

/-- The connected component containing `x`, presented as a set of vertices. -/
def componentVertices (x : V) : Set V := {y | G.Reachable x y}

/-- Every actual graph component is finite and has at most `B` vertices. -/
def UniformComponentBound (B : ℕ) : Prop :=
  ∀ x, (componentVertices G x).Finite ∧ (componentVertices G x).ncard ≤ B

/-- An injective finite family in a single component cannot exceed its cardinality. -/
theorem injective_terms_le_of_reachable {B n : ℕ}
    (hB : UniformComponentBound G B) (x : V) (w : Fin n → V)
    (hinj : Function.Injective w) (hreach : ∀ i, G.Reachable x (w i)) : n ≤ B := by
  have hsub : Set.range w ⊆ componentVertices G x := by
    rintro y ⟨i, rfl⟩
    exact hreach i
  have hcard := Set.ncard_le_ncard hsub (hB x).1
  rw [Set.ncard_range_of_injective hinj, Nat.card_fin] at hcard
  exact hcard.trans (hB x).2

/-- Consecutive vertices in a finite sequence are joined by graph edges. -/
def IsFiniteWalk {n : ℕ} (w : Fin n → V) : Prop :=
  ∀ i j : Fin n, j.val = i.val + 1 → G.Adj (w i) (w j)

/-- Every term of a nonempty finite walk is reachable from its first term. -/
theorem finiteWalk_reachable {n : ℕ} (w : Fin n → V) (hn : 0 < n)
    (hwalk : IsFiniteWalk G w) : ∀ i, G.Reachable (w ⟨0, hn⟩) (w i) := by
  have hreach : ∀ k (hk : k < n), G.Reachable (w ⟨0, hn⟩) (w ⟨k, hk⟩) := by
    intro k
    induction k with
    | zero =>
        intro hk
        exact SimpleGraph.Reachable.rfl
    | succ k ih =>
        intro hk
        exact (ih (by omega)).trans (hwalk ⟨k, by omega⟩ ⟨k + 1, hk⟩ rfl).reachable
  intro i
  exact hreach i.val i.isLt

/-- The "at most `B` terms" consequence for injective finite walks, including
the empty sequence. This is the graph-theoretic consequence in v3, Theorem 1.1. -/
theorem finite_injective_walk_terms_le {B n : ℕ}
    (hB : UniformComponentBound G B) (w : Fin n → V)
    (hinj : Function.Injective w) (hwalk : IsFiniteWalk G w) : n ≤ B := by
  by_cases hn : 0 < n
  · exact injective_terms_le_of_reachable G hB (w ⟨0, hn⟩) w hinj
      (finiteWalk_reachable G w hn hwalk)
  · omega

/-- The same consequence for mathlib's actual walks with no repeated vertices.
The number of terms is the number of edges plus one. -/
theorem path_terms_le {B : ℕ} (hB : UniformComponentBound G B)
    {x y : V} (p : G.Walk x y) (hp : p.IsPath) : p.length + 1 ≤ B := by
  classical
  let w : Fin (p.length + 1) → V := fun i => p.getVert i.val
  have hinj : Function.Injective w := by
    intro i j hij
    apply Fin.ext
    exact hp.getVert_injOn (x₁ := i.val) (x₂ := j.val)
      (Nat.le_of_lt_succ i.isLt) (Nat.le_of_lt_succ j.isLt) hij
  exact injective_terms_le_of_reachable G hB x w hinj
    (fun i => (p.take i.val).reachable)

/-- A uniform finite component bound rules out infinite injective edge walks.
It suffices to apply the finite theorem to the first `B + 1` terms. -/
theorem no_infinite_injective_walk {B : ℕ} (hB : UniformComponentBound G B)
    (w : ℕ → V) (hwalk : ∀ k, G.Adj (w k) (w (k + 1))) :
    ¬ Function.Injective w := by
  intro hinj
  let v : Fin (B + 1) → V := fun i => w i.val
  have hv : Function.Injective v := by
    intro i j hij
    exact Fin.ext (hinj hij)
  have hvwalk : IsFiniteWalk G v := by
    intro i j hij
    change G.Adj (w i.val) (w j.val)
    rw [hij]
    exact hwalk i.val
  have hle := finite_injective_walk_terms_le G hB v hv hvwalk
  omega

end Entry002
