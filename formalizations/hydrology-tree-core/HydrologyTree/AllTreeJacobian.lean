import HydrologyTree.TreeJacobianRecurrence

/-! All-size all-rate Jacobian factorization of the actual physical branching
tree coefficient map, first in precise recursive subtree-product form. Exact
flattening to the original vertex set is proved in the subsequent module. -/
open Polynomial
noncomputable section
namespace HydrologyTree

/-- Fixed orientation depending only on the actual tree and coefficient ordering. -/
def treeProofOrientation {n : ℕ} (t : OrderedTree n) : ℝ :=
  treeCoordinateDet t * (-1 : ℝ)^n * ∏ c : RootChild t, treeProofOrientation (childTree t c)
termination_by n
decreasing_by exact childEdgeCount_lt t c

/-- Actual connector rate monomials and actual sibling resultants over every
subtree. This is not defined to be a Jacobian or to assume the factorization. -/
def allTreeJacobianWeight {n : ℕ} (t : OrderedTree n) (x : TreeRates n) : ℝ :=
  treeSiblingResultant t x ^ 2 * treeRootRateFactor t x *
    ∏ c : RootChild t, allTreeJacobianWeight (childTree t c) (childRates t c x)
termination_by n
decreasing_by exact childEdgeCount_lt t c

lemma treeProofOrientation_sq {n : ℕ} (t : OrderedTree n) : treeProofOrientation t ^ 2 = 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [treeProofOrientation,mul_pow,mul_pow,treeCoordinateDet_sq,one_mul]
    have hp : (∏ c : RootChild t, treeProofOrientation (childTree t c))^2 = 1 := by
      rw [← Finset.prod_pow]
      have hsub : ∀ c : RootChild t, treeProofOrientation (childTree t c)^2 = 1 :=
        fun c => ih (childEdgeCount t c) (childEdgeCount_lt t c) (childTree t c)
      simp only [hsub,Finset.prod_const_one]
    rw [hp,mul_one,← pow_mul,Nat.mul_comm n 2,pow_mul]
    norm_num

/-- The sign is fixed for the tree, not allowed to vary with the rate vector. -/
lemma treeProofOrientation_sign {n : ℕ} (t : OrderedTree n) :
    treeProofOrientation t = 1 ∨ treeProofOrientation t = -1 :=
  real_sq_one_sign _ (treeProofOrientation_sq t)

/-- UNCONDITIONAL actual canonical Jacobian factorization for every finite
rooted tree and every real rate vector, including every zero-rate or repeated-root
boundary. Only fixed coordinate orientation remains outside the explicit factors. -/
theorem all_tree_canonical_jacobian {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    treeCanonicalJacobian t x = treeProofOrientation t * allTreeJacobianWeight t x := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hsub : (∏ c : RootChild t, treeCanonicalJacobian (childTree t c) (childRates t c x)) =
        (∏ c : RootChild t, treeProofOrientation (childTree t c)) *
          (∏ c : RootChild t, allTreeJacobianWeight (childTree t c) (childRates t c x)) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro c _
      exact ih (childEdgeCount t c) (childEdgeCount_lt t c) (childTree t c) (childRates t c x)
    calc
      treeCanonicalJacobian t x = treeCoordinateDet t * (treeCoordinateDet t * treeCanonicalJacobian t x) := by
        rw [← mul_assoc,← pow_two,treeCoordinateDet_sq,one_mul]
      _ = _ := by
        rw [treeCanonicalJacobian_recurrence,hsub,treeProofOrientation,allTreeJacobianWeight]
        ring

/-- Quantified fixed-sign formulation: the same orientation works for all rates. -/
theorem all_tree_canonical_jacobian_fixed_sign {n : ℕ} (t : OrderedTree n) :
    ∃ ε : ℝ, (ε=1 ∨ ε= -1) ∧ ∀ x : TreeRates n,
      treeCanonicalJacobian t x = ε * allTreeJacobianWeight t x :=
  ⟨treeProofOrientation t,treeProofOrientation_sign t,all_tree_canonical_jacobian t⟩

/-- The all-rate orientation-independent polynomial identity. -/
theorem all_tree_canonical_jacobian_sq {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    treeCanonicalJacobian t x ^ 2 = allTreeJacobianWeight t x ^ 2 := by
  rw [all_tree_canonical_jacobian,mul_pow,treeProofOrientation_sq,one_mul]

end HydrologyTree
