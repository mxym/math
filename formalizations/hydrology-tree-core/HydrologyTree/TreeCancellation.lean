import HydrologyTree.PhysicalCancellation

/-! Complete all-size common-root classification for the original physical
characteristic/cofactor polynomials. Spectral collisions are located at actual
sibling principal blocks, not arbitrary recursively postulated polynomials. -/
noncomputable section
namespace HydrologyTree

variable {K : Type*} [Field K] [Algebra ℝ K]

/-- A spectral collision between two distinct sibling blocks at some vertex.
All descendants are the actual rate-preserving principal child models. -/
def SiblingCollisionSomewhere {n : ℕ} (t : OrderedTree n) (x : TreeRates n) (z : K) : Prop :=
  SiblingCollisionAtRoot t x z ∨
    ∃ c : RootChild t, SiblingCollisionSomewhere (childTree t c) (childRates t c x) z
termination_by n
decreasing_by exact childEdgeCount_lt t c

/-- Complete classification of common zeros of the actual root cofactor and
characteristic polynomial, for every finite tree and every field extension.
Internal rates need only be nonzero; positivity and root-leak nonzero are unnecessary. -/
theorem physicalCommonRoot_iff_siblingCollision {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (hx : NonzeroTreeEdges x) (z : K) :
    PhysicalCommonRoot t x z ↔ SiblingCollisionSomewhere t x z := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [physicalCommonRoot_local_iff t x hx, SiblingCollisionSomewhere]
    apply or_congr Iff.rfl
    apply exists_congr
    intro c
    exact ih (childEdgeCount t c) (childEdgeCount_lt t c) (childTree t c)
      (childRates t c x) (nonzero_child_edges t c x hx)

/-- Absence of every sibling collision rules out all cancellations at that value. -/
theorem no_common_root_of_no_sibling_collision {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (hx : NonzeroTreeEdges x) (z : K) (hz : ¬SiblingCollisionSomewhere t x z) :
    ¬PhysicalCommonRoot t x z := by
  exact mt (physicalCommonRoot_iff_siblingCollision t x hx z).mp hz

/-- Every detected sibling collision actually cancels the original root response:
both original, unreduced polynomials vanish. -/
theorem sibling_collision_gives_common_root {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (hx : NonzeroTreeEdges x) (z : K) (hz : SiblingCollisionSomewhere t x z) :
    Polynomial.aeval z (physicalRootCofactor t x) = 0 ∧
      Polynomial.aeval z (physicalCharacteristic t x) = 0 := by
  exact (physicalCommonRoot_iff_siblingCollision t x hx z).mpr hz

end HydrologyTree
