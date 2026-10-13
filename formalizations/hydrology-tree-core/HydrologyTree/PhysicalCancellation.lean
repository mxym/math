import HydrologyTree.PhysicalRecursion
import HydrologyTree.FiniteCancellation
import HydrologyTree.ChildIndex

/-! Common roots over any field extension of the reals of the actual characteristic polynomial and actual
root cofactor: exact local cancellation classification from physical rates. -/
open Polynomial
noncomputable section
namespace HydrologyTree

/-- Only internal directed rates must be nonzero; the original root leak is unrestricted. -/
def NonzeroTreeEdges {n : ℕ} (x : TreeRates n) : Prop :=
  (∀ e : Fin n, x.1 e.succ ≠ 0) ∧ (∀ e : Fin n, x.2 e ≠ 0)

lemma inward_nonroot_ne_zero {n : ℕ} (x : TreeRates n) (hx : NonzeroTreeEdges x)
    (v : Fin (n+1)) (hv : v ≠ 0) : x.1 v ≠ 0 := by
  rw [← Fin.succ_pred v hv]
  exact hx.1 _

lemma outward_nonroot_ne_zero {n : ℕ} (x : TreeRates n) (hx : NonzeroTreeEdges x)
    (v : Fin (n+1)) (hv : v ≠ 0) : outwardByVertex x.2 v ≠ 0 := by
  rw [← Fin.succ_pred v hv, outwardByVertex_succ]
  exact hx.2 _

/-- Nonzero physical edge rates pass to every genuinely extracted child model. -/
theorem nonzero_child_edges {n : ℕ} (t : OrderedTree n) (c : RootChild t)
    (x : TreeRates n) (hx : NonzeroTreeEdges x) : NonzeroTreeEdges (childRates t c x) := by
  constructor
  · intro e
    exact inward_nonroot_ne_zero x hx _ (branchVertex_ne_zero t c (childEnumeration t c e.succ))
  · intro e
    exact outward_nonroot_ne_zero x hx _ (branchVertex_ne_zero t c (childEnumeration t c e.succ))

variable {K : Type*} [Field K] [Algebra ℝ K]

/-- An actual common zero, with no cancellation of the stored polynomials. -/
def PhysicalCommonRoot {n : ℕ} (t : OrderedTree n) (x : TreeRates n) (z : K) : Prop :=
  aeval z (physicalRootCofactor t x) = 0 ∧ aeval z (physicalCharacteristic t x) = 0

def SiblingCollisionAtRoot {n : ℕ} (t : OrderedTree n) (x : TreeRates n) (z : K) : Prop :=
  ∃ c d : RootChild t, c ≠ d ∧
    aeval z (childCharacteristic t x c) = 0 ∧ aeval z (childCharacteristic t x d) = 0

/-- Exact common-root recursion, including simultaneous cancellations in several children. -/
theorem physicalCommonRoot_local_iff {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (hx : NonzeroTreeEdges x) (z : K) :
    PhysicalCommonRoot t x z ↔ SiblingCollisionAtRoot t x z ∨
      ∃ c : RootChild t, PhysicalCommonRoot (childTree t c) (childRates t c x) z := by
  classical
  let p : RootChild t → K := fun c => aeval z (childCharacteristic t x c)
  let f : RootChild t → K := fun c => aeval z (childCofactor t x c)
  let a : RootChild t → K := fun c => algebraMap ℝ K (x.1 c.val * outwardByVertex x.2 c.val)
  have ha : ∀ c, a c ≠ 0 := by
    intro c
    exact (map_ne_zero (algebraMap ℝ K)).mpr (mul_ne_zero (inward_nonroot_ne_zero x hx _ c.property.1)
      (outward_nonroot_ne_zero x hx _ c.property.1))
  have h := finite_branch_cancellation_iff (z + algebraMap ℝ K ((rateChart t x).1 0)) p f a ha
  have he : PhysicalCommonRoot t x z ↔
      ∃ c, p c = 0 ∧ (f c = 0 ∨ ∃ j, j ≠ c ∧ p j = 0) := by
    rw [PhysicalCommonRoot, physicalRootCofactor_child_product,
      physicalCharacteristic_child_recursion]
    simpa only [map_prod, map_sub, map_mul, map_sum, map_add, aeval_X, aeval_C,
      mul_one,
      p, f, a, branchValueNumerator] using h
  rw [he]
  constructor
  · rintro ⟨c,hp,hc⟩
    rcases hc with hf | ⟨j,hjc,hj⟩
    · exact Or.inr ⟨c,hf,hp⟩
    · exact Or.inl ⟨c,j,Ne.symm hjc,hp,hj⟩
  · rintro (⟨c,d,hcd,hc,hd⟩ | ⟨c,hf,hp⟩)
    · exact ⟨c,hc,Or.inr ⟨d,Ne.symm hcd,hd⟩⟩
    · exact ⟨c,hp,Or.inl hf⟩

end HydrologyTree
