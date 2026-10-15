import HydrologyTree.SingleLeakResidence
import HydrologyTree.RealLocatedPositivity

/-! Independent multi-leak model and actual-matrix fibre. Positive rates refer
to the original graph edges; nonnegative losses are actual column sums. -/
open Matrix Polynomial
noncomputable section
namespace HydrologyTree
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Every vertex has its own external loss coefficient. -/
abbrev MultiLeakRates (G : SimpleGraph V) := (V → ℝ) × (G.Dart → ℝ)

def multiLeakMatrix (G : SimpleGraph V) [DecidableRel G.Adj] (y : MultiLeakRates G) : Matrix V V ℝ :=
  (∑ d : G.Dart,graphTransfer (0,y.2) d)-Matrix.diagonal y.1

lemma multiLeakMatrix_eq (o : V) (y : MultiLeakRates G) :
    multiLeakMatrix G y=graphCompartmentMatrix G o (0,y.2)-Matrix.diagonal y.1 := by
  simp [multiLeakMatrix,graphCompartmentMatrix]

lemma multiLeakMatrix_column_sum (y : MultiLeakRates G) (j : V) :
    (∑ i,multiLeakMatrix G y i j) = -y.1 j := by
  rw [multiLeakMatrix_eq j]
  simp only [Matrix.sub_apply,Finset.sum_sub_distrib,graphCompartment_column_sum,ite_true,neg_zero,zero_sub]
  simp [Matrix.diagonal_apply]

@[simp] lemma matrixLeak_multiLeakMatrix (y : MultiLeakRates G) (j : V) :
    matrixLeak (multiLeakMatrix G y) j=y.1 j := by
  rw [matrixLeak,multiLeakMatrix_column_sum,neg_neg]

@[simp] lemma multiLeakMatrix_dart (y : MultiLeakRates G) (d : G.Dart) :
    multiLeakMatrix G y d.snd d.fst=y.2 d := by
  rw [multiLeakMatrix_eq d.fst]
  simp only [Matrix.sub_apply,graphCompartment_dart_entry,Matrix.diagonal_apply,
    if_neg d.snd_ne_fst,sub_zero]

def PhysicalMultiLeakMatrix (G : SimpleGraph V) (A : Matrix V V ℝ) : Prop :=
  (∀ i j,i ≠ j → ¬G.Adj i j → A i j=0) ∧
    (∀ i j,G.Adj i j → 0 < A i j) ∧ ∀ j,0 ≤ matrixLeak A j

/-- The full ACTUAL physical matrix fibre; no assumed diagonal representation,
root-only leak, or classified solution set occurs in its membership predicate. -/
abbrev MultiLeakMatrixFiber {n : ℕ} (G : SimpleGraph V) (o : V) (r w : Fin (n+1) → ℝ) :=
  {A : Matrix V V ℝ // PhysicalMultiLeakMatrix G A ∧ A.charpoly=stieltjesDenominator r ∧
    diagonalCofactor A o=stieltjesNumerator r w}

lemma positive_graph_edge_entry (o : V) (y : GraphRates G) (hy : PositiveGraphRates y)
    (i j : V) (hij : G.Adj i j) : 0 < graphCompartmentMatrix G o y i j := by
  let d : G.Dart := ⟨(j,i),hij.symm⟩
  have h := graphCompartment_dart_entry o y d
  change graphCompartmentMatrix G o y i j=y.2 d at h
  rw [h]
  exact hy.2 d

/-- The signs of both actual models and one normalized scale force all state
scales positive by connectivity. No positive-gauge existence is assumed. -/
theorem connected_gauge_positive (hG : G.Connected) (o : V) (A B : Matrix V V ℝ)
    (h : V → ℝ) (hh : ∀ i,h i ≠ 0) (ho : h o=1)
    (hA : ∀ i j,G.Adj i j → 0 < A i j)
    (hB : ∀ i j,G.Adj i j → 0 < B i j)
    (he : A=diagonalGauge h B) : ∀ i,0 < h i := by
  have hedge {u v : V} (huv : G.Adj u v) (hu : 0<h u) : 0<h v := by
    have hv := hA v u huv.symm
    rw [he,diagonalGauge_apply] at hv
    exact (mul_pos_iff_of_pos_right (hB v u huv.symm)).mp
      ((mul_pos_iff_of_pos_right (inv_pos.mpr hu)).mp hv)
  have walkpos {u v : V} (p : G.Walk u v) : 0<h u → 0<h v := by
    induction p with
    | nil => exact id
    | cons hab p ih => exact fun hu => ih (hedge hab hu)
  intro i
  apply walkpos (Classical.choice (hG o i))
  rw [ho]
  norm_num

/-- Every normalized nonnegative-leak gauge of a positive reference is a
physical multi-leak matrix in the original graph, with its exact target pair. -/
def gaugeToMultiLeakMatrixFiber {n : ℕ} {o : V} (p : RootedTreePresentation n G o)
    (r w : Fin (n+1) → ℝ) (x : PositiveStieltjesFiber p.tree r w)
    (h : NonnegativeLeakGauge (graphCompartmentMatrix G o (graphRateEquiv p x.val)) o) :
    MultiLeakMatrixFiber G o r w := by
  let B := graphCompartmentMatrix G o (graphRateEquiv p x.val)
  have hx := (graphRateEquiv_positive_iff p x.val).mpr x.property.1
  have hn : ∀ i,h.val i ≠ 0 := fun i => ne_of_gt (h.property.1 i)
  refine ⟨diagonalGauge h.val B,⟨?_,?_,h.property.2.2⟩,?_,?_⟩
  · intro i j hij hnG
    rw [diagonalGauge_apply]
    change h.val i * graphCompartmentMatrix G o (graphRateEquiv p x.val) i j * (h.val j)⁻¹=0
    rw [graphCompartment_nonedge o _ i j hij hnG,mul_zero,zero_mul]
  · intro i j hij
    rw [diagonalGauge_apply]
    exact mul_pos (mul_pos (h.property.1 i) (positive_graph_edge_entry o _ hx i j hij))
      (inv_pos.mpr (h.property.1 j))
  · rw [diagonalGauge_charpoly _ hn]
    exact (graphCharacteristic_transport p x.val).trans x.property.2.1
  · rw [diagonalGauge_cofactor _ hn]
    exact (graphRootCofactor_transport p x.val).trans x.property.2.2

end HydrologyTree
