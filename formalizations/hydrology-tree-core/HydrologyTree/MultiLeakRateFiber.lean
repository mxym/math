import HydrologyTree.MultiLeakClassification
import HydrologyTree.MatrixStieltjesIdentification

/-! Actual multi-leak parameter vectors, their conservative matrices and the
response-only fibre. Coefficient observations are not silently added as data. -/
open Matrix Polynomial
noncomputable section
namespace HydrologyTree
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma multiLeakMatrix_nonedge (y : MultiLeakRates G) (i j : V)
    (hij : i ≠ j) (hn : ¬G.Adj i j) : multiLeakMatrix G y i j=0 := by
  rw [multiLeakMatrix_eq i]
  simp only [Matrix.sub_apply,graphCompartment_nonedge i _ i j hij hn,
    Matrix.diagonal_apply,if_neg hij,sub_zero]

def MultiLeakAdmissible (y : MultiLeakRates G) : Prop :=
  (∀ j,0 ≤ y.1 j) ∧ ∀ d,0 < y.2 d

lemma multiLeakMatrix_physical (y : MultiLeakRates G) (hy : MultiLeakAdmissible y) :
    PhysicalMultiLeakMatrix G (multiLeakMatrix G y) := by
  refine ⟨multiLeakMatrix_nonedge y,?_,?_⟩
  · intro i j hij
    let d : G.Dart := ⟨(j,i),hij.symm⟩
    have he := multiLeakMatrix_dart y d
    change multiLeakMatrix G y i j=y.2 d at he
    rw [he]
    exact hy.2 d
  · intro j
    rw [matrixLeak_multiLeakMatrix]
    exact hy.1 j

def ratesOfMultiMatrix (A : Matrix V V ℝ) : MultiLeakRates G :=
  (matrixLeak A,fun d => A d.snd d.fst)

lemma multiLeakMatrix_reconstruct (A : Matrix V V ℝ) (hA : PhysicalMultiLeakMatrix G A) :
    multiLeakMatrix G (ratesOfMultiMatrix A)=A := by
  apply matrix_eq_of_offdiag_of_column_sum
  · intro i j hij
    by_cases ha : G.Adj i j
    · let d : G.Dart := ⟨(j,i),ha.symm⟩
      exact multiLeakMatrix_dart (ratesOfMultiMatrix A) d
    · rw [multiLeakMatrix_nonedge _ i j hij ha,hA.1 i j hij ha]
  · intro j
    rw [multiLeakMatrix_column_sum]
    exact neg_neg _

lemma ratesOfMultiMatrix_admissible (A : Matrix V V ℝ) (hA : PhysicalMultiLeakMatrix G A) :
    MultiLeakAdmissible (ratesOfMultiMatrix (G := G) A) :=
  ⟨hA.2.2,fun d => hA.2.1 _ _ d.adj.symm⟩

lemma ratesOfMultiMatrix_left_inverse (y : MultiLeakRates G) :
    ratesOfMultiMatrix (multiLeakMatrix G y)=y := by
  apply Prod.ext
  · funext j
    exact matrixLeak_multiLeakMatrix y j
  · funext d
    exact multiLeakMatrix_dart y d

/-- Every actual rate vector is determined by the independently defined matrix. -/
theorem multiLeakMatrix_injective : Function.Injective (multiLeakMatrix G) := by
  intro x y h
  have he := congrArg (ratesOfMultiMatrix (G := G)) h
  simpa only [ratesOfMultiMatrix_left_inverse] using he

abbrev MultiLeakCoefficientFiber {n : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (o : V) (r w : Fin (n+1) → ℝ) :=
  {y : MultiLeakRates G // MultiLeakAdmissible y ∧
    (multiLeakMatrix G y).charpoly=stieltjesDenominator r ∧
    diagonalCofactor (multiLeakMatrix G y) o=stieltjesNumerator r w}

def multiLeakRateMatrixEquiv {n : ℕ} (o : V) (r w : Fin (n+1) → ℝ) :
    MultiLeakCoefficientFiber G o r w ≃ MultiLeakMatrixFiber G o r w where
  toFun y := ⟨multiLeakMatrix G y.val,multiLeakMatrix_physical y.val y.property.1,y.property.2⟩
  invFun A := ⟨ratesOfMultiMatrix A.val,ratesOfMultiMatrix_admissible A.val A.property.1,
    by rw [multiLeakMatrix_reconstruct A.val A.property.1]; exact A.property.2⟩
  left_inv y := Subtype.ext (ratesOfMultiMatrix_left_inverse y.val)
  right_inv A := Subtype.ext (multiLeakMatrix_reconstruct A.val A.property.1)

abbrev MultiLeakResponseFiber {n : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (o : V) (r w : Fin (n+1) → ℝ) :=
  {y : MultiLeakRates G // MultiLeakAdmissible y ∧
    ∀ s : ℝ,(multiLeakMatrix G y).charpoly.eval s ≠ 0 → (∀ i,s+r i ≠ 0) →
      (Matrix.scalar V s-multiLeakMatrix G y)⁻¹ o o=∑ i,w i/(s+r i)}

/-- Actual inverse-entry equality alone recovers the complete target pair. -/
def multiLeakResponseCoefficientEquiv {n : ℕ} (o : V) (hN : Fintype.card V=n+1)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i,0<r i)
    (hw : ∀ i,0<w i) (hm : (∑ i,w i)=1) :
    MultiLeakResponseFiber G o r w ≃ MultiLeakCoefficientFiber G o r w where
  toFun y := ⟨y.val,y.property.1,
    (matrix_stieltjes_response_iff_pair _ o hN r w hr hpos hw hm).mp y.property.2⟩
  invFun y := ⟨y.val,y.property.1,
    (matrix_stieltjes_response_iff_pair _ o hN r w hr hpos hw hm).mpr y.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Full physical RATE fibre from only the actual root response, with the exact
discrete index and every nonnegative-leak face. Nothing assumes a gauge form. -/
def multiLeakResponseSimplexEquiv {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (r w : Fin (n+1) → ℝ)
    (hr : Function.Injective r) (hpos : ∀ i,0<r i) (hw : ∀ i,0<w i) (hm : (∑ i,w i)=1) :
    MultiLeakResponseFiber G o r w ≃ RecursivePoleAllocations p.tree × LeakSimplex V :=
  (multiLeakResponseCoefficientEquiv o (presentation_card p) r w hr hpos hw hm).trans
    ((multiLeakRateMatrixEquiv o r w).trans (multiLeakRecursiveSimplexEquiv hG p r w hr hpos hw hm))

/-- No supplied tree numbering, hidden inverse-positivity assumption, or missing
existence/counting input remains in the actual parameter/response theorem. -/
theorem finite_graph_multileak_response_classification {n : ℕ}
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree) (o : V) (hN : Fintype.card V=n+1)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i,0<r i)
    (hw : ∀ i,0<w i) (hm : (∑ i,w i)=1) :
    ∃ p : RootedTreePresentation n G o,
      Nonempty (MultiLeakResponseFiber G o r w ≃ RecursivePoleAllocations p.tree × LeakSimplex V) ∧
      Finite (RecursivePoleAllocations p.tree) ∧
      Nat.card (RecursivePoleAllocations p.tree)=n.factorial/(∏ e : Fin n,subtreeVertexCount p.tree e.succ) := by
  obtain ⟨p⟩ := finite_rooted_tree_presentation n G o hG hN
  have hc := recursivePoleAllocations_finite_card p.tree
  exact ⟨p,⟨multiLeakResponseSimplexEquiv hG p r w hr hpos hw hm⟩,hc.1,
    hc.2.trans (treeFiberDegree_eq_factorial_quotient p.tree)⟩

end HydrologyTree
