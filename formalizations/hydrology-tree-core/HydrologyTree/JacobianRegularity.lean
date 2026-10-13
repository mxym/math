import HydrologyTree.AllTreeJacobian
import HydrologyTree.SubtreeAssignment
import HydrologyTree.TreeCancellation

/-! Exact Jacobian regularity for actual branching trees with nonzero internal
rates. The full determinant, rather than a presumed minimality equivalence,
is the input proved by the preceding all-tree induction. -/
open Polynomial
noncomputable section
namespace HydrologyTree

lemma list_map_prod_ne_zero {α : Type*} (f : α → ℝ) (l : List α) :
    (l.map f).prod ≠ 0 ↔ ∀ a ∈ l, f a ≠ 0 := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

lemma monic_resultant_ne_zero_iff (p q : ℝ[X]) (hp : p.Monic) :
    p.resultant q ≠ 0 ↔ IsCoprime p q := by
  rw [← isUnit_iff_ne_zero,Polynomial.isUnit_resultant_iff_isCoprime hp]

lemma pairwiseResultants_ne_zero_iff (ps : List ℝ[X]) (hm : ∀ p ∈ ps, p.Monic) :
    pairwiseResultants ps ≠ 0 ↔ ps.Pairwise IsCoprime := by
  induction ps with
  | nil => simp [pairwiseResultants]
  | cons p ps ih =>
    have hp : p.Monic := hm p (by simp)
    have ht : ∀ q ∈ ps, q.Monic := fun q hq => hm q (by simp [hq])
    simp only [pairwiseResultants,mul_ne_zero_iff,List.pairwise_cons]
    rw [list_map_prod_ne_zero,ih ht]
    exact and_congr (forall_congr' fun q => forall_congr' fun _ =>
      monic_resultant_ne_zero_iff p q hp) Iff.rfl

lemma treeSiblingResultant_ne_zero_iff {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    treeSiblingResultant t x ≠ 0 ↔
      ∀ c d : RootChild t, c ≠ d → IsCoprime (childCharacteristic t x c) (childCharacteristic t x d) := by
  let e := Fintype.equivFin (RootChild t)
  have hm : ∀ p ∈ List.ofFn (fun i : Fin (Fintype.card (RootChild t)) => childCharacteristic t x (e.symm i)),
      p.Monic := by
    intro p hp
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
    exact physicalCharacteristic_monic _ _
  rw [treeSiblingResultant,pairwiseResultants_ne_zero_iff _ hm,List.pairwise_ofFn]
  constructor
  · intro h c d hcd
    have hn : e c ≠ e d := fun he => hcd (e.injective he)
    rcases lt_or_gt_of_ne hn with hlt | hgt
    · simpa only [Equiv.symm_apply_apply] using h hlt
    · simpa only [Equiv.symm_apply_apply] using (h hgt).symm
  · intro h i j hij
    exact h _ _ (fun he => (ne_of_lt hij) (e.symm.injective he))

lemma treeRootRateFactor_ne_zero {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (hx : NonzeroTreeEdges x) : treeRootRateFactor t x ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro c _
  exact mul_ne_zero (pow_ne_zero _ (inward_nonroot_ne_zero x hx c.val c.property.1))
    (pow_ne_zero _ (outward_nonroot_ne_zero x hx c.val c.property.1))

lemma real_square_ne_zero_iff (a : ℝ) : a^2 ≠ 0 ↔ a ≠ 0 := by
  constructor
  · intro h ha
    apply h
    rw [ha]
    norm_num
  · exact pow_ne_zero 2

/-- All recursive factors are nonzero precisely when each actual sibling
polynomial family is coprime. There is no positivity premise. -/
theorem allTreeWeight_ne_zero_iff_coprime {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (hx : NonzeroTreeEdges x) :
    allTreeJacobianWeight t x ≠ 0 ↔ CoprimeAtEveryBranch t x := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hchildren : (∏ c : RootChild t, allTreeJacobianWeight (childTree t c) (childRates t c x)) ≠ 0 ↔
        ∀ c : RootChild t, CoprimeAtEveryBranch (childTree t c) (childRates t c x) := by
      simp only [Finset.prod_ne_zero_iff,Finset.mem_univ,true_implies]
      exact forall_congr' fun c => ih (childEdgeCount t c) (childEdgeCount_lt t c)
        (childTree t c) (childRates t c x) (nonzero_child_edges t c x hx)
    rw [allTreeJacobianWeight,mul_ne_zero_iff,mul_ne_zero_iff,real_square_ne_zero_iff,
      treeSiblingResultant_ne_zero_iff,hchildren,CoprimeAtEveryBranch]
    constructor
    · rintro ⟨⟨hs,_⟩,hc⟩
      exact ⟨hs,hc⟩
    · rintro ⟨hs,hc⟩
      exact ⟨⟨hs,treeRootRateFactor_ne_zero t x hx⟩,hc⟩

/-- Actual full coefficient-map regularity, not the simpler matrix-coordinate
Jacobian: every nonzero-edge real reference is regular iff all siblings are coprime. -/
theorem treeJacobian_ne_zero_iff_coprime {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (hx : NonzeroTreeEdges x) : treeCanonicalJacobian t x ≠ 0 ↔ CoprimeAtEveryBranch t x := by
  have he : treeProofOrientation t ≠ 0 := by
    rcases treeProofOrientation_sign t with h | h <;> rw [h] <;> norm_num
  rw [all_tree_canonical_jacobian,mul_ne_zero_iff,allTreeWeight_ne_zero_iff_coprime t x hx]
  exact ⟨fun h => h.2,fun h => ⟨he,h⟩⟩

lemma coprime_no_common_aeval {K : Type*} [Field K] [Algebra ℝ K]
    (p q : ℝ[X]) (hpq : IsCoprime p q) (z : K) :
    ¬(aeval z p = 0 ∧ aeval z q = 0) := by
  rintro ⟨hp,hq⟩
  obtain ⟨a,b,h⟩ := hpq
  have hval := congrArg (fun r : ℝ[X] => aeval z r) h
  simp only [map_add,map_mul,map_one,hp,hq,mul_zero,zero_add] at hval
  exact zero_ne_one hval

/-- Coprime actual sibling polynomials exclude common roots over every real
field extension, not only at a finite set of tested eigenvalues. -/
theorem coprime_branches_no_sibling_collisions {K : Type*} [Field K] [Algebra ℝ K]
    {n : ℕ} (t : OrderedTree n) (x : TreeRates n) (hcop : CoprimeAtEveryBranch t x) :
    ∀ z : K, ¬SiblingCollisionSomewhere t x z := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [CoprimeAtEveryBranch] at hcop
    intro z hz
    rw [SiblingCollisionSomewhere] at hz
    rcases hz with ⟨c,d,hcd,hc,hd⟩ | ⟨c,hc⟩
    · exact coprime_no_common_aeval _ _ (hcop.1 c d hcd) z ⟨hc,hd⟩
    · exact ih (childEdgeCount t c) (childEdgeCount_lt t c) (childTree t c)
        (childRates t c x) (hcop.2 c) z hc

end HydrologyTree
