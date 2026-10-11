import HydrologyTree.ChildIndex

/-! Exact linear equivalence between original rate coordinates and independent
root connector/child-model coordinates. All maps are rate-independent permutations. -/
noncomputable section
namespace HydrologyTree

/-- Reindex real coordinate functions along an explicit finite index bijection. -/
def vectorReindex {ι κ : Type*} (e : ι ≃ κ) : (κ → ℝ) ≃ₗ[ℝ] (ι → ℝ) where
  toFun f i := f (e i)
  invFun g j := g (e.symm j)
  left_inv f := by funext j; simp
  right_inv g := by funext i; simp
  map_add' f g := rfl
  map_smul' c f := rfl

/-- Separate the singleton root from the numbered branch-coordinate functions. -/
def splitRootFamily {C : Type*} (m : C → ℕ) :
    (Unit ⊕ (Σ c : C, Fin (m c+1)) → ℝ) ≃ₗ[ℝ]
      ℝ × ((c : C) → VertexValues (m c)) where
  toFun f := (f (.inl ()), fun c i => f (.inr ⟨c,i⟩))
  invFun z v := match v with
    | .inl _ => z.1
    | .inr v => z.2 v.1 v.2
  left_inv f := by funext v; rcases v with u | ⟨c,i⟩; cases u <;> rfl; rfl
  right_inv z := rfl
  map_add' f g := rfl
  map_smul' c f := rfl

def curryChildValues {C : Type*} (m : C → ℕ) :
    ((Σ c : C, Fin (m c+1)) → ℝ) ≃ₗ[ℝ] ((c : C) → VertexValues (m c)) where
  toFun f c i := f ⟨c,i⟩
  invFun g v := g v.1 v.2
  left_inv f := rfl
  right_inv g := rfl
  map_add' f g := rfl
  map_smul' c f := rfl

/-- The only regrouping: the first outward coordinate is a connector rate,
while the remaining outward coordinates are internal to the child. -/
def regroupChildRates {C : Type*} (m : C → ℕ) :
    ((ℝ × ((c : C) → VertexValues (m c))) × ((c : C) → VertexValues (m c))) ≃ₗ[ℝ]
      ℝ × ((c : C) → ℝ × TreeRates (m c)) where
  toFun z := (z.1.1, fun c => (z.2 c 0, (z.1.2 c, fun i => z.2 c i.succ)))
  invFun z := ((z.1, fun c => (z.2 c).2.1), fun c => Fin.cons (z.2 c).1 (z.2 c).2.2)
  left_inv z := by
    apply Prod.ext
    · rfl
    · funext c i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv z := rfl
  map_add' f g := rfl
  map_smul' c f := rfl

abbrev ChildRateData {n : ℕ} (t : OrderedTree n) :=
  (c : RootChild t) → ℝ × TreeRates (childEdgeCount t c)
abbrev PartitionedRates {n : ℕ} (t : OrderedTree n) := ℝ × ChildRateData t

/-- Exact bijective linear coordinate permutation; no independence premise is used. -/
def ratePartitionEquiv {n : ℕ} (t : OrderedTree n) :
    TreeRates n ≃ₗ[ℝ] PartitionedRates t :=
  ((vectorReindex (numberedRootEquiv t)).trans (splitRootFamily (childEdgeCount t))).prodCongr
    ((vectorReindex (numberedEdgeEquiv t)).trans (curryChildValues (childEdgeCount t))) |>.trans
      (regroupChildRates (childEdgeCount t))

@[simp] theorem ratePartition_root {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    (ratePartitionEquiv t x).1 = x.1 0 := rfl

/-- The forward permutation agrees with the actual previously proved physical child rates. -/
theorem ratePartition_child {n : ℕ} (t : OrderedTree n) (x : TreeRates n) (c : RootChild t) :
    (ratePartitionEquiv t x).2 c = (outwardByVertex x.2 c.val, childRates t c x) := by
  apply Prod.ext
  · change x.2 (numberedEdgeEquiv t ⟨c,0⟩) = _
    rw [outward_at_numbered_child t x.2 c 0, childEnumeration_zero]
    rfl
  · apply Prod.ext
    · rfl
    · funext i
      exact outward_at_numbered_child t x.2 c i.succ

/-- Arbitrary connector rates and arbitrary physical child parameters occur,
uniquely, in an original rate vector. No generic-rank or positivity premise. -/
theorem ratePartition_existsUnique {n : ℕ} (t : OrderedTree n) (z : PartitionedRates t) :
    ∃! x : TreeRates n, ratePartitionEquiv t x = z := by
  exact ⟨(ratePartitionEquiv t).symm z, (ratePartitionEquiv t).apply_symm_apply z,
    fun y hy => (ratePartitionEquiv t).injective (hy.trans ((ratePartitionEquiv t).apply_symm_apply z).symm)⟩

/-- The permutation is continuous and has its actual derivative equal to itself. -/
theorem hasFDerivAt_ratePartition {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    HasFDerivAt (ratePartitionEquiv t)
      (ratePartitionEquiv t).toContinuousLinearEquiv.toContinuousLinearMap x :=
  (ratePartitionEquiv t).toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt

end HydrologyTree
