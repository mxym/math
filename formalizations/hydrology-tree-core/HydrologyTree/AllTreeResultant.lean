import HydrologyTree.PhysicalResultantRecurrence
import HydrologyTree.SubtreeProducts

/-! Exact signed resultant/Jacobian identity for all original finite physical
trees and all real rates, including every zero-rate boundary. -/
open Polynomial
noncomputable section
namespace HydrologyTree

/-- Product of the outward rates on the original edges. -/
def outwardRateProduct {n : ℕ} (x : TreeRates n) : ℝ := ∏ e : Fin n, x.2 e

lemma outwardRateProduct_recursion {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    outwardRateProduct x = (∏ c : RootChild t, outwardByVertex x.2 c.val) *
      ∏ c : RootChild t, outwardRateProduct (childRates t c x) := by
  rw [outwardRateProduct,← (numberedEdgeEquiv t).prod_comp,Fintype.prod_sigma,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro c _
  simp only [outward_at_numbered_child,Fin.prod_univ_succ,childEnumeration_zero]
  rfl

lemma resultant_connector_powers {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    (∏ c : RootChild t, (x.1 c.val*outwardByVertex x.2 c.val)^(childEdgeCount t c+1)) =
      treeRootRateFactor t x * ∏ c : RootChild t, outwardByVertex x.2 c.val := by
  rw [treeRootRateFactor,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro c _
  rw [mul_pow,pow_succ (outwardByVertex x.2 c.val)]
  ring

/-- A sign determined solely by the actual tree and degree conventions. -/
def treeResultantOrientation {n : ℕ} (t : OrderedTree n) : ℝ :=
  treeLocalResultantSign t * ∏ c : RootChild t, treeResultantOrientation (childTree t c)
termination_by n
decreasing_by exact childEdgeCount_lt t c

lemma treeResultantOrientation_sq {n : ℕ} (t : OrderedTree n) : treeResultantOrientation t ^ 2 = 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [treeResultantOrientation,mul_pow,treeLocalResultantSign_sq,one_mul,← Finset.prod_pow]
    have hc : ∀ c : RootChild t, treeResultantOrientation (childTree t c)^2 = 1 :=
      fun c => ih _ (childEdgeCount_lt t c) (childTree t c)
    simp only [hc,Finset.prod_const_one]

/-- Full explicit factorization of the ACTUAL characteristic/cofactor resultant. -/
theorem physicalResultant_eq_allTreeWeight {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    physicalResultant t x = treeResultantOrientation t * outwardRateProduct x *
      allTreeJacobianWeight t x := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hc (c : RootChild t) : physicalResultant (childTree t c) (childRates t c x) =
        treeResultantOrientation (childTree t c) * outwardRateProduct (childRates t c x) *
          allTreeJacobianWeight (childTree t c) (childRates t c x) :=
      ih _ (childEdgeCount_lt t c) (childTree t c) (childRates t c x)
    rw [physicalResultant_child_recursion,treeResultantOrientation,
      outwardRateProduct_recursion,allTreeJacobianWeight]
    simp only [hc,Finset.prod_mul_distrib]
    rw [resultant_connector_powers]
    ring

/-- The exact relative sign between the resultant and standard coefficient Jacobian. -/
def resultantJacobianOrientation {n : ℕ} (t : OrderedTree n) : ℝ :=
  treeResultantOrientation t * treeProofOrientation t

lemma resultantJacobianOrientation_sq {n : ℕ} (t : OrderedTree n) :
    resultantJacobianOrientation t ^ 2 = 1 := by
  rw [resultantJacobianOrientation,mul_pow,treeResultantOrientation_sq,treeProofOrientation_sq,one_mul]

lemma resultantJacobianOrientation_sign {n : ℕ} (t : OrderedTree n) :
    resultantJacobianOrientation t = 1 ∨ resultantJacobianOrientation t = -1 :=
  real_sq_one_sign _ (resultantJacobianOrientation_sq t)

/-- MAIN IDENTITY: every real rate vector, original physical polynomial pair,
actual standard-basis Frechet Jacobian, with one fixed sign for the whole tree.
No positivity or nonzero-rate assumption and no cancellation of zero factors. -/
theorem physicalResultant_eq_signed_jacobian {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    (physicalCharacteristic t x).resultant (physicalRootCofactor t x) =
      resultantJacobianOrientation t * (∏ e : Fin n, x.2 e) * treeCanonicalJacobian t x := by
  change physicalResultant t x = _
  rw [physicalResultant_eq_allTreeWeight,all_tree_canonical_jacobian,resultantJacobianOrientation]
  change treeResultantOrientation t * outwardRateProduct x * allTreeJacobianWeight t x =
    (treeResultantOrientation t * treeProofOrientation t) * outwardRateProduct x *
      (treeProofOrientation t * allTreeJacobianWeight t x)
  calc
    _ = treeResultantOrientation t * treeProofOrientation t^2 * outwardRateProduct x *
        allTreeJacobianWeight t x := by rw [treeProofOrientation_sq,mul_one]
    _ = _ := by ring

/-- The existential sign is fixed before quantifying over ALL rate vectors. -/
theorem full_tree_resultant_jacobian {n : ℕ} (t : OrderedTree n) :
    ∃ ε : ℝ, (ε=1 ∨ ε= -1) ∧ ∀ x : TreeRates n,
      (physicalCharacteristic t x).resultant (physicalRootCofactor t x) =
        ε * (∏ e : Fin n, x.2 e) * treeCanonicalJacobian t x :=
  ⟨resultantJacobianOrientation t,resultantJacobianOrientation_sign t,
    physicalResultant_eq_signed_jacobian t⟩

/-- Orientation-independent exact identity, valid on the full boundary as well. -/
theorem physicalResultant_jacobian_square {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    (physicalCharacteristic t x).resultant (physicalRootCofactor t x)^2 =
      ((∏ e : Fin n, x.2 e) * treeCanonicalJacobian t x)^2 := by
  rw [physicalResultant_eq_signed_jacobian]
  rw [mul_assoc,mul_pow,resultantJacobianOrientation_sq,one_mul]

end HydrologyTree
