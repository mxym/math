import HydrologyTree.ChildRates

/-! Rate-independent coordinate bijections for the complete child partition. -/
noncomputable section
namespace HydrologyTree

abbrev NumberedChildNodes {n : ℕ} (t : OrderedTree n) :=
  Σ c : RootChild t, Fin (childEdgeCount t c+1)

/-- Exact reindexing from the original vertices to root and numbered children. -/
def numberedRootEquiv {n : ℕ} (t : OrderedTree n) : Unit ⊕ NumberedChildNodes t ≃ Fin (n+1) :=
  (Equiv.sumCongr (Equiv.refl Unit)
    (Equiv.sigmaCongrRight fun c => (childEnumeration t c).toEquiv)).trans (rootPartitionEquiv t)

@[simp] theorem numberedRootEquiv_zero {n : ℕ} (t : OrderedTree n) :
    numberedRootEquiv t (.inl ()) = 0 := rfl

@[simp] theorem numberedRootEquiv_child {n : ℕ} (t : OrderedTree n)
    (c : RootChild t) (i : Fin (childEdgeCount t c+1)) :
    numberedRootEquiv t (.inr ⟨c,i⟩) = (childEnumeration t c i).val := rfl

/-- Each nonroot vertex labels precisely one outward rate, including connector edges. -/
def numberedEdgeIndex {n : ℕ} (t : OrderedTree n) (z : NumberedChildNodes t) : Fin n :=
  (childEnumeration t z.1 z.2).val.pred (branchVertex_ne_zero t z.1 _)

@[simp] lemma numberedEdgeIndex_succ {n : ℕ} (t : OrderedTree n) (z : NumberedChildNodes t) :
    (numberedEdgeIndex t z).succ = (childEnumeration t z.1 z.2).val := Fin.succ_pred _ _

lemma numberedEdgeIndex_injective {n : ℕ} (t : OrderedTree n) :
    Function.Injective (numberedEdgeIndex t) := by
  intro z w h
  have hs := congrArg Fin.succ h
  rw [numberedEdgeIndex_succ, numberedEdgeIndex_succ] at hs
  have he : numberedRootEquiv t (.inr z) = numberedRootEquiv t (.inr w) := hs
  exact Sum.inr_injective ((numberedRootEquiv t).injective he)

lemma numberedEdgeIndex_surjective {n : ℕ} (t : OrderedTree n) :
    Function.Surjective (numberedEdgeIndex t) := by
  intro e
  obtain ⟨z,hz⟩ := (numberedRootEquiv t).surjective e.succ
  rcases z with u | z
  · cases u
    exact False.elim (Fin.succ_ne_zero e hz.symm)
  · refine ⟨z, ?_⟩
    apply Fin.succ_injective
    exact (numberedEdgeIndex_succ t z).trans hz

/-- This is a bijection, not an assumption that the extracted rates are independent. -/
def numberedEdgeEquiv {n : ℕ} (t : OrderedTree n) : NumberedChildNodes t ≃ Fin n :=
  Equiv.ofBijective (numberedEdgeIndex t)
    ⟨numberedEdgeIndex_injective t, numberedEdgeIndex_surjective t⟩

theorem outward_at_numbered_child {n : ℕ} (t : OrderedTree n) (f : EdgeValues n)
    (c : RootChild t) (i : Fin (childEdgeCount t c+1)) :
    f (numberedEdgeEquiv t ⟨c,i⟩) = outwardByVertex f (childEnumeration t c i).val := by
  rw [← numberedEdgeIndex_succ t ⟨c,i⟩]
  rfl

/-- Exact dimension count for the complete child partition. -/
theorem sum_child_vertices {n : ℕ} (t : OrderedTree n) :
    (∑ c : RootChild t, (childEdgeCount t c+1)) = n := by
  have h := Fintype.card_congr (numberedEdgeEquiv t)
  simpa only [Fintype.card_sigma, Fintype.card_fin] using h

end HydrologyTree
