import HydrologyTree.PositiveFiberEquivalence
import HydrologyTree.TreeFiberCombinatorics
import Mathlib.SetTheory.Cardinal.Finite

/-! Complete recursive classification. The target is a finite combinatorial
allocation type depending only on the labelled tree, not on a candidate list
of physical models or on an assumed solution count. -/
open Polynomial
noncomputable section
namespace HydrologyTree

/-- Every level records only its labelled pole allocation; child enumerations
inside a block are canonical and are not counted as different assignments. -/
def RecursivePoleAllocations {n : ℕ} (t : OrderedTree n) : Type :=
  Σ _a : TreePoleAllocation t, (c : RootChild t) → RecursivePoleAllocations (childTree t c)
termination_by n
decreasing_by exact childEdgeCount_lt t c

lemma recursivePoleAllocations_finite_card {n : ℕ} (t : OrderedTree n) :
    Finite (RecursivePoleAllocations t) ∧ Nat.card (RecursivePoleAllocations t)=treeFiberDegree t := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hc (c : RootChild t) : Finite (RecursivePoleAllocations (childTree t c)) ∧
        Nat.card (RecursivePoleAllocations (childTree t c))=treeFiberDegree (childTree t c) :=
      ih _ (childEdgeCount_lt t c) (childTree t c)
    letI : ∀ c : RootChild t, Finite (RecursivePoleAllocations (childTree t c)) := fun c => (hc c).1
    rw [RecursivePoleAllocations]
    refine ⟨inferInstance,?_⟩
    rw [Nat.card_sigma]
    simp only [Nat.card_pi]
    simp only [fun c => (hc c).2]
    rw [Finset.sum_const,Finset.card_univ,Nat.nsmul_eq_mul,treeFiberDegree]

/-- Changing only equal polynomial descriptions preserves the actual rate vector. -/
def positivePolynomialFiberCongr {n : ℕ} (t : OrderedTree n) (P F Q G : ℝ[X])
    (hP : P=Q) (hF : F=G) : PositivePolynomialFiber t P F ≃ PositivePolynomialFiber t Q G where
  toFun x := ⟨x.val,x.property.1,x.property.2.1.trans hP,x.property.2.2.trans hF⟩
  invFun x := ⟨x.val,x.property.1,x.property.2.1.trans hP.symm,x.property.2.2.trans hF.symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- EVERY actual positive realization is classified by a unique recursive
labelled pole allocation, and EVERY recursive allocation is realized. All child
bijections are constructed by induction, with no classification premise. -/
theorem positive_stieltjes_recursive_equiv_exists {n : ℕ} (t : OrderedTree n)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i, 0 < r i)
    (hw : ∀ i, 0 < w i) (hm : (∑ i, w i)=1) :
    Nonempty (PositiveStieltjesFiber t r w ≃ RecursivePoleAllocations t) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    obtain ⟨b,g,d,hb,hbpos,hg,hF,hP,hl⟩ :=
      exists_positive_reciprocal_data_unordered r w hr hpos hw hm
    have hc (a : TreePoleAllocation t) (c : RootChild t) :
        Nonempty (PositiveStieltjesFiber (childTree t c)
          (allocatedRates b a c) (allocatedWeights t g a c) ≃ RecursivePoleAllocations (childTree t c)) :=
      ih _ (childEdgeCount_lt t c) (childTree t c)
        (allocatedRates b a c) (allocatedWeights t g a c)
        (allocatedRates_injective t b hb.injective a c) (fun i => hbpos _)
        (allocatedWeights_pos t g hg a c) (allocatedWeights_sum t g hg a c)
    let E : AllocatedFiberData t b g ≃ RecursivePoleAllocations t := by
      rw [RecursivePoleAllocations]
      exact Equiv.sigmaCongrRight (fun a => Equiv.piCongrRight (fun c => Classical.choice (hc a c)))
    exact ⟨(positivePolynomialFiberCongr t _ _ _ _ hP hF).trans
      ((positiveReciprocalFiberEquiv t b g d hb.injective hbpos hg hl).trans E)⟩

/-- A proved full bijection, not merely equinumerosity or an upper bound. -/
def positiveStieltjesRecursiveEquiv {n : ℕ} (t : OrderedTree n)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i, 0 < r i)
    (hw : ∀ i, 0 < w i) (hm : (∑ i, w i)=1) :
    PositiveStieltjesFiber t r w ≃ RecursivePoleAllocations t :=
  Classical.choice (positive_stieltjes_recursive_equiv_exists t r w hr hpos hw hm)

end HydrologyTree
