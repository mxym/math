import HydrologyTree.IndependentChildCoordinates
import HydrologyTree.CouplingSemantics

/-! Exact independent-child coordinates of the ORIGINAL physical rate arrays,
with a proved coefficient-dot identity. These are permutations, not rescalings. -/
noncomputable section
namespace HydrologyTree

variable {I : Type*} [Fintype I]

def regroupRootChildren (m : I → ℕ) :
    (ℝ × ((i : I) → ℝ × TreeRates (m i))) ≃ₗ[ℝ] IndependentChildData m where
  toFun z := (fun i => (z.2 i).2,(z.1,fun i => (z.2 i).1))
  invFun z := (z.2.1,fun i => (z.2.2 i,z.1 i))
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def originalWorkEquiv {n : ℕ} (t : OrderedTree n) :
    TreeRates n ≃ₗ[ℝ] IndependentChildData (childEdgeCount t) :=
  (ratePartitionEquiv t).trans (regroupRootChildren (childEdgeCount t))

lemma originalWorkEquiv_apply {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    originalWorkEquiv t x =
      (fun c => childRates t c x,(x.1 0,fun c => outwardByVertex x.2 c.val)) := by
  apply Prod.ext
  · funext c
    exact congrArg Prod.snd (ratePartition_child t x c)
  · apply Prod.ext
    · rfl
    · funext c
      exact congrArg Prod.fst (ratePartition_child t x c)

lemma original_inward_dot {n : ℕ} (t : OrderedTree n) (x y : TreeRates n) :
    (∑ v : Fin (n+1), x.1 v*y.1 v) = x.1 0*y.1 0 +
      ∑ c : RootChild t, ∑ i : Fin (childEdgeCount t c+1),
        (childRates t c x).1 i * (childRates t c y).1 i := by
  rw [← (numberedRootEquiv t).sum_comp (fun v => x.1 v*y.1 v),Fintype.sum_sum_type]
  simp only [Fintype.sum_unique,Fintype.sum_sigma]
  rfl

lemma original_outward_dot {n : ℕ} (t : OrderedTree n) (x y : TreeRates n) :
    (∑ e : Fin n, x.2 e*y.2 e) =
      ∑ c : RootChild t, (outwardByVertex x.2 c.val * outwardByVertex y.2 c.val +
        ∑ i : Fin (childEdgeCount t c), (childRates t c x).2 i * (childRates t c y).2 i) := by
  rw [← (numberedEdgeEquiv t).sum_comp (fun e => x.2 e*y.2 e),Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro c _
  simp only [outward_at_numbered_child, Fin.sum_univ_succ,childEnumeration_zero]
  rfl

/-- No unproved Jacobian normalization: the actual finite rate arrays and the
independent child/connector coordinates have identical coefficient dot products. -/
theorem originalWorkEquiv_dot {n : ℕ} (t : OrderedTree n) (x y : TreeRates n) :
    independentChildDot (childEdgeCount t) (originalWorkEquiv t x) (originalWorkEquiv t y) =
      physicalRateDot n x y := by
  rw [originalWorkEquiv_apply,originalWorkEquiv_apply]
  unfold independentChildDot
  change (∑ c : RootChild t, physicalRateDot (childEdgeCount t c) (childRates t c x) (childRates t c y)) +
      x.1 0*y.1 0 + (∑ c : RootChild t, outwardByVertex x.2 c.val*outwardByVertex y.2 c.val) = _
  unfold physicalRateDot
  rw [original_inward_dot t x y,original_outward_dot t x y]
  simp only [Finset.sum_add_distrib]
  ring

lemma originalWorkEquiv_originalCoupling {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    originalWorkEquiv t x = originalCouplingInputs t x :=
  originalWorkEquiv_apply t x

end HydrologyTree
