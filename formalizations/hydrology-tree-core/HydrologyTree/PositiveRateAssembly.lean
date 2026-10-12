import HydrologyTree.CouplingSemantics
import HydrologyTree.PhysicalRecursion

/-! Actual assembly of independent positive child models and connectors into
the original physical tree. The coordinate permutation is already proved;
all positivity and extraction properties are derived here. -/
noncomputable section
namespace HydrologyTree

/-- Strict positivity of all physical rates, including the root leak. -/
def PositiveRateVector {n : ℕ} (x : TreeRates n) : Prop :=
  (∀ v, 0 < x.1 v) ∧ ∀ e, 0 < x.2 e

def assemblePositiveRates {n : ℕ} (t : OrderedTree n) (l : ℝ)
    (f : RootChild t → ℝ) (y : ChildStates t) : TreeRates n :=
  (ratePartitionEquiv t).symm (l,fun c => (f c,y c))

lemma assembledRates_root {n : ℕ} (t : OrderedTree n) (l : ℝ)
    (f : RootChild t → ℝ) (y : ChildStates t) :
    (assemblePositiveRates t l f y).1 0 = l := by
  have h := congrArg Prod.fst ((ratePartitionEquiv t).apply_symm_apply (l,fun c => (f c,y c)))
  exact h

lemma assembledRates_extract {n : ℕ} (t : OrderedTree n) (l : ℝ)
    (f : RootChild t → ℝ) (y : ChildStates t) (c : RootChild t) :
    outwardByVertex (assemblePositiveRates t l f y).2 c.val = f c ∧
      childRates t c (assemblePositiveRates t l f y) = y c := by
  have h := congrArg (fun z : PartitionedRates t => z.2 c)
    ((ratePartitionEquiv t).apply_symm_apply (l,fun c => (f c,y c)))
  change (ratePartitionEquiv t (assemblePositiveRates t l f y)).2 c = (f c,y c) at h
  rw [ratePartition_child] at h
  exact Prod.mk.inj h

lemma assembledRates_child {n : ℕ} (t : OrderedTree n) (l : ℝ)
    (f : RootChild t → ℝ) (y : ChildStates t) (c : RootChild t) :
    childRates t c (assemblePositiveRates t l f y) = y c := (assembledRates_extract t l f y c).2

lemma assembledRates_connector {n : ℕ} (t : OrderedTree n) (l : ℝ)
    (f : RootChild t → ℝ) (y : ChildStates t) (c : RootChild t) :
    outwardByVertex (assemblePositiveRates t l f y).2 c.val = f c :=
  (assembledRates_extract t l f y c).1

lemma assembledRates_child_leak {n : ℕ} (t : OrderedTree n) (l : ℝ)
    (f : RootChild t → ℝ) (y : ChildStates t) (c : RootChild t) :
    (assemblePositiveRates t l f y).1 c.val = (y c).1 0 := by
  rw [← childRates_leak t c (assemblePositiveRates t l f y),assembledRates_child]

lemma assembledRates_diagonal {n : ℕ} (t : OrderedTree n) (l : ℝ)
    (f : RootChild t → ℝ) (y : ChildStates t) :
    (rateChart t (assemblePositiveRates t l f y)).1 0 = l+∑ c, f c := by
  change (assemblePositiveRates t l f y).1 0 + parentCLM t (assemblePositiveRates t l f y).2 0 = _
  rw [assembledRates_root,rootConnectors_sum]
  simp only [assembledRates_connector]

/-- Positivity is transferred to all ORIGINAL edge coordinates, not only to
an auxiliary block model. -/
theorem assemblePositiveRates_positive {n : ℕ} (t : OrderedTree n) (l : ℝ)
    (f : RootChild t → ℝ) (y : ChildStates t) (hl : 0 < l)
    (hf : ∀ c, 0 < f c) (hy : ∀ c, PositiveRateVector (y c)) :
    PositiveRateVector (assemblePositiveRates t l f y) := by
  constructor
  · intro v
    refine Fin.cases ?_ (fun e => ?_) v
    · rwa [assembledRates_root]
    · obtain ⟨⟨c,i⟩,he⟩ := (numberedEdgeEquiv t).surjective e
      rw [← he]
      change 0 < (assemblePositiveRates t l f y).1 (numberedEdgeIndex t ⟨c,i⟩).succ
      rw [numberedEdgeIndex_succ]
      change 0 < (childRates t c (assemblePositiveRates t l f y)).1 i
      rw [assembledRates_child]
      exact (hy c).1 i
  · intro e
    obtain ⟨⟨c,i⟩,he⟩ := (numberedEdgeEquiv t).surjective e
    rw [← he,outward_at_numbered_child t (assemblePositiveRates t l f y).2 c i]
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [childEnumeration_zero]
      exact (assembledRates_connector t l f y c).symm ▸ hf c
    · change 0 < (childRates t c (assemblePositiveRates t l f y)).2 j
      rw [assembledRates_child]
      exact (hy c).2 j

end HydrologyTree
