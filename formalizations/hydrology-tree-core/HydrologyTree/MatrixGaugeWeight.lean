import HydrologyTree.MatrixSiblingWeight
import HydrologyTree.DiagonalGauge
import HydrologyTree.PhysicalConstants

/-! Exact diagonal-gauge invariance of actual principal resultants and edge
weights, and the all-rate physical root factorization without divided rates. -/
open Matrix Polynomial
noncomputable section
namespace HydrologyTree

lemma principalChild_gauge {n : ℕ} (t : OrderedTree n) (A : TreeMatrix n)
    (h : Fin (n+1) → ℝ) (c : RootChild t) :
    principalChildOver t (diagonalGauge h A) c=
      diagonalGauge (fun i => h (childEnumeration t c i).val) (principalChildOver t A c) := by
  ext i j
  simp [principalChildOver,diagonalGauge_apply]

lemma principalChildPolynomialList_gauge {n : ℕ} (t : OrderedTree n) (A : TreeMatrix n)
    (h : Fin (n+1) → ℝ) (hh : ∀ v,h v ≠ 0) :
    principalChildPolynomialList t (diagonalGauge h A)=principalChildPolynomialList t A := by
  simp only [principalChildPolynomialList,principalChild_gauge,diagonalGauge_charpoly _ (fun _ => hh _)]

/-- Every actual principal-child spectral residual is gauge invariant. -/
theorem matrixSiblingResidual_gauge {n : ℕ} (t : OrderedTree n) (A : TreeMatrix n)
    (h : Fin (n+1) → ℝ) (hh : ∀ v,h v ≠ 0) :
    matrixSiblingResidual t (diagonalGauge h A)=matrixSiblingResidual t A := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [matrixSiblingResidual]
    conv_rhs => rw [matrixSiblingResidual]
    rw [principalChildPolynomialList_gauge t A h hh]
    congr 1
    apply Finset.prod_congr rfl
    intro c _
    rw [principalChild_gauge]
    exact ih _ (childEdgeCount_lt t c) (childTree t c) _ _ (fun _ => hh _)

lemma diagonalGauge_edge_product {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (h : V → ℝ) (hh : ∀ v,h v ≠ 0) (i j : V) :
    diagonalGauge h A i j*diagonalGauge h A j i=A i j*A j i := by
  simp only [diagonalGauge_apply]
  field_simp [hh i,hh j]
  <;> ring

theorem matrixEdgeWeight_gauge {n : ℕ} (t : OrderedTree n) (A : TreeMatrix n)
    (h : Fin (n+1) → ℝ) (hh : ∀ v,h v ≠ 0) :
    matrixEdgeWeight t (diagonalGauge h A)=matrixEdgeWeight t A := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [matrixEdgeWeight]
    conv_rhs => rw [matrixEdgeWeight]
    apply Finset.prod_congr rfl
    intro c _
    rw [diagonalGauge_edge_product A h hh,principalChild_gauge,
      ih _ (childEdgeCount_lt t c) (childTree t c) _ _ (fun _ => hh _)]

theorem matrixCoreWeight_gauge {n : ℕ} (t : OrderedTree n) (A : TreeMatrix n)
    (h : Fin (n+1) → ℝ) (hh : ∀ v,h v ≠ 0) :
    matrixCoreWeight t (diagonalGauge h A)=matrixCoreWeight t A := by
  rw [matrixCoreWeight,matrixEdgeWeight_gauge t A h hh,matrixSiblingResidual_gauge t A h hh]
  rfl

/-- Exact physical factorization: one inward factor per edge times the fully
gauge-invariant actual matrix weight. Zero rates are included without division. -/
theorem allTreeWeight_eq_inward_matrixWeight {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    allTreeJacobianWeight t x=(∏ e : Fin n,x.1 e.succ)*matrixCoreWeight t (compartmentMatrix t x) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hsub : (∏ c : RootChild t, allTreeJacobianWeight (childTree t c) (childRates t c x))=
        ∏ c : RootChild t,(∏ e : Fin (childEdgeCount t c),(childRates t c x).1 e.succ)*
          matrixCoreWeight (childTree t c) (compartmentMatrix (childTree t c) (childRates t c x)) := by
      exact Finset.prod_congr rfl (fun c _ => ih _ (childEdgeCount_lt t c) (childTree t c) (childRates t c x))
    have hin : (∏ e : Fin n,x.1 e.succ)=∏ c : RootChild t,
        x.1 c.val*(∏ e : Fin (childEdgeCount t c),(childRates t c x).1 e.succ) := by
      rw [← child_inward_product t x]
      simp only [Fin.prod_univ_succ,childRates_leak]
    have hres : pairwiseResultantsOver (principalChildPolynomialList t (compartmentMatrix t x))=treeSiblingResultant t x := by
      have hl : principalChildPolynomialList t (compartmentMatrix t x)=childCharacteristicListOver t x := by
        simp only [principalChildPolynomialList,childCharacteristicListOver,childRatesOver_real,
          modelCharacteristicOver_real,principalChildOver_real,supportedChild_physical,physicalCharacteristic]
      rw [hl,childCharacteristicListOver_real]
    rw [allTreeJacobianWeight,hsub,hin,matrixCoreWeight,matrixEdgeWeight,matrixSiblingResidual,hres,treeRootRateFactor]
    simp only [principalChildOver_real,supportedChild_physical,root_inward_child,root_outward_child]
    simp only [matrixCoreWeight]
    simp only [pow_succ,mul_pow,Finset.prod_mul_distrib]
    ring

/-- Main root coefficient Jacobian expressed in actual matrix invariants. -/
theorem root_jacobian_matrixWeight {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    treeCanonicalJacobian t x=treeProofOrientation t*(∏ e : Fin n,x.1 e.succ)*
      matrixCoreWeight t (compartmentMatrix t x) := by
  rw [all_tree_canonical_jacobian,allTreeWeight_eq_inward_matrixWeight]
  ring

end HydrologyTree
