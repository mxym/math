import HydrologyTree.ResultantFamilyEnumeration
import HydrologyTree.TreeJacobianRecurrence

/-! Exact local resultant recurrence for the actual unreduced physical tree
characteristic and cofactor. All degree identities and enumeration bridges
are proved; no positivity, nonzero rates, or absence of common roots is assumed. -/
open Polynomial
noncomputable section
namespace HydrologyTree

/-- Degree-only sign for the actual root's fixed child enumeration. -/
def treeLocalResultantSign {n : ℕ} (t : OrderedTree n) : ℝ :=
  (-1 : ℝ)^n * resultantPairSign ((resultantEnumeration (RootChild t)).map
    fun c => childEdgeCount t c+1)

lemma treeLocalResultantSign_sq {n : ℕ} (t : OrderedTree n) : treeLocalResultantSign t ^ 2 = 1 := by
  rw [treeLocalResultantSign,mul_pow,resultantPairSign_sq,mul_one,
    ← pow_mul,Nat.mul_comm n 2,pow_mul]
  norm_num

/-- The actual characteristic/cofactor resultant, not a reduced fraction or a
recursively prescribed replacement for the physical polynomial pair. -/
def physicalResultant {n : ℕ} (t : OrderedTree n) (x : TreeRates n) : ℝ :=
  (physicalCharacteristic t x).resultant (physicalRootCofactor t x)

/-- An exact all-rate, all-size recurrence, retaining the complete constants
and signs omitted by zero-set-only cancellation classifications. -/
theorem physicalResultant_child_recursion {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    physicalResultant t x = treeLocalResultantSign t * treeSiblingResultant t x ^ 2 *
      ∏ c : RootChild t, (x.1 c.val*outwardByVertex x.2 c.val)^(childEdgeCount t c+1) *
        physicalResultant (childTree t c) (childRates t c x) := by
  let p := childCharacteristic t x
  let r := fun c : RootChild t => C (x.1 c.val*outwardByVertex x.2 c.val) * childCofactor t x c
  have hm (c : RootChild t) : (p c).Monic := physicalCharacteristic_monic _ _
  have hr := resultant_root_update (physicalRootCofactor t x)
    (∑ c : RootChild t, r c * ∏ j ∈ Finset.univ.erase c, p j)
    (physicalCharacteristic t x) (physicalRootCofactor_monic t x) ((rateChart t x).1 0)
    (by rw [physicalRootCofactor_child_product]; exact physicalCharacteristic_child_recursion t x)
    (by rw [physicalCharacteristic_natDegree,physicalRootCofactor_natDegree])
  have hd (c : RootChild t) : (p c).natDegree = childEdgeCount t c+1 :=
    physicalCharacteristic_natDegree _ _
  have hscale (c : RootChild t) : (p c).resultant (r c) =
      (x.1 c.val*outwardByVertex x.2 c.val)^(childEdgeCount t c+1) *
        physicalResultant (childTree t c) (childRates t c x) := by
    have h := monic_resultant_scale (p c) (childCofactor t x c) (hm c)
      (x.1 c.val*outwardByVertex x.2 c.val)
    exact h.trans (congrArg (fun k : ℕ =>
      (x.1 c.val*outwardByVertex x.2 c.val)^k *
        physicalResultant (childTree t c) (childRates t c x)) (hd c))
  have he : pairwiseResultants ((resultantEnumeration (RootChild t)).map p) =
      treeSiblingResultant t x := by
    simp only [resultantEnumeration,List.map_ofFn,Function.comp_def,treeSiblingResultant,p]
  have hr' : physicalResultant t x = (-1 : ℝ)^n *
      (physicalRootCofactor t x).resultant
        (∑ c : RootChild t, r c * ∏ j ∈ Finset.univ.erase c, p j) := by
    exact hr.trans (congrArg (fun k : ℕ => (-1 : ℝ)^k *
      (physicalRootCofactor t x).resultant
        (∑ c : RootChild t, r c * ∏ j ∈ Finset.univ.erase c, p j))
      (physicalRootCofactor_natDegree t x))
  rw [hr',physicalRootCofactor_child_product]
  change (-1 : ℝ)^n * (∏ c : RootChild t, p c).resultant
    (∑ c : RootChild t, r c * ∏ j ∈ Finset.univ.erase c, p j) = _
  rw [finite_family_signed_resultant p r hm,he]
  simp only [hscale]
  have hdegrees : ((resultantEnumeration (RootChild t)).map fun c => (p c).natDegree) =
      ((resultantEnumeration (RootChild t)).map fun c => childEdgeCount t c+1) := by
    apply List.map_congr_left
    intro c _
    exact hd c
  rw [hdegrees]
  unfold treeLocalResultantSign
  ring

end HydrologyTree
