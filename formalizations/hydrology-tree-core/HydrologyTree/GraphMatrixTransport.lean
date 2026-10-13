import HydrologyTree.GraphRateTransport
import HydrologyTree.Resolvent

/-! The actual graph-conservative matrix is defined independently of any
presentation. Equality after the rate and vertex transports is proved. -/
open Matrix Polynomial
noncomputable section
namespace HydrologyTree

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def graphTransfer (y : GraphRates G) (d : G.Dart) : Matrix V V ℝ :=
  y.2 d • (Matrix.single d.snd d.fst (1 : ℝ)-Matrix.single d.fst d.fst (1 : ℝ))

def graphCompartmentMatrix (G : SimpleGraph V) [DecidableRel G.Adj] (o : V) (y : GraphRates G) :
    Matrix V V ℝ := (∑ d : G.Dart, graphTransfer y d)-y.1 • Matrix.single o o (1 : ℝ)

lemma graph_single_transport {n : ℕ} (e : Fin (n+1) ≃ V) (u v : Fin (n+1)) (c : ℝ) :
    (Matrix.single (e u) (e v) c).submatrix e e=Matrix.single u v c := by
  ext i j
  simp [Matrix.single_apply,Matrix.submatrix_apply]

lemma graphTransfer_inward_transport {n : ℕ} {o : V} (p : RootedTreePresentation n G o)
    (x : TreeRates n) (i : Fin n) :
    (graphTransfer (graphRateEquiv p x) (treeDartEquiv p (.inl i))).submatrix p.vertices p.vertices =
      x.1 i.succ • (Matrix.single (p.tree.parent i) i.succ (1 : ℝ)-Matrix.single i.succ i.succ (1 : ℝ)) := by
  have hrate := graphRateEquiv_inward p x i
  ext u v
  simp only [graphTransfer,Matrix.submatrix_apply,Matrix.smul_apply,Matrix.sub_apply,hrate]
  change x.1 i.succ • ((Matrix.single (p.vertices (p.tree.parent i)) (p.vertices i.succ) (1 : ℝ))
      (p.vertices u) (p.vertices v) - (Matrix.single (p.vertices i.succ) (p.vertices i.succ) (1 : ℝ))
      (p.vertices u) (p.vertices v)) = _
  simp [Matrix.single_apply]

lemma graphTransfer_outward_transport {n : ℕ} {o : V} (p : RootedTreePresentation n G o)
    (x : TreeRates n) (i : Fin n) :
    (graphTransfer (graphRateEquiv p x) (treeDartEquiv p (.inr i))).submatrix p.vertices p.vertices =
      x.2 i • (Matrix.single i.succ (p.tree.parent i) (1 : ℝ)-
        Matrix.single (p.tree.parent i) (p.tree.parent i) (1 : ℝ)) := by
  have hrate := graphRateEquiv_outward p x i
  ext u v
  simp only [graphTransfer,Matrix.submatrix_apply,Matrix.smul_apply,Matrix.sub_apply,hrate]
  change x.2 i • ((Matrix.single (p.vertices i.succ) (p.vertices (p.tree.parent i)) (1 : ℝ))
      (p.vertices u) (p.vertices v) -
      (Matrix.single (p.vertices (p.tree.parent i)) (p.vertices (p.tree.parent i)) (1 : ℝ))
      (p.vertices u) (p.vertices v)) = _
  simp [Matrix.single_apply]

theorem graphCompartmentMatrix_transport {n : ℕ} {o : V} (p : RootedTreePresentation n G o)
    (x : TreeRates n) :
    (graphCompartmentMatrix G o (graphRateEquiv p x)).submatrix p.vertices p.vertices =
      compartmentMatrix p.tree x := by
  have hsum : (∑ d : G.Dart, (graphTransfer (graphRateEquiv p x) d).submatrix p.vertices p.vertices) =
      ∑ i : Fin n, edgeMatrix p.tree x i := by
    rw [← (treeDartEquiv p).sum_comp (fun d => (graphTransfer (graphRateEquiv p x) d).submatrix p.vertices p.vertices),
      Fintype.sum_sum_type]
    simp only [graphTransfer_inward_transport,graphTransfer_outward_transport]
    rw [← Finset.sum_add_distrib]
    rfl
  ext u v
  have hs := congrArg (fun M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ => M u v) hsum
  simp only [Matrix.sum_apply,Matrix.submatrix_apply] at hs
  simp only [graphCompartmentMatrix,Matrix.submatrix_apply,Matrix.sub_apply,Matrix.sum_apply,
    Matrix.smul_apply,graphRateEquiv_leak,compartmentMatrix]
  rw [hs]
  simp [← p.root_eq,Matrix.single_apply]

def graphCharacteristic (o : V) (y : GraphRates G) : ℝ[X] :=
  (graphCompartmentMatrix G o y).charpoly

def graphRootCofactor (o : V) (y : GraphRates G) : ℝ[X] :=
  diagonalCofactor (graphCompartmentMatrix G o y) o

def graphRootResponse (o : V) (y : GraphRates G) (s : ℝ) : ℝ :=
  (Matrix.scalar V s-graphCompartmentMatrix G o y)⁻¹ o o

lemma graphCharacteristic_transport {n : ℕ} {o : V} (p : RootedTreePresentation n G o)
    (x : TreeRates n) : graphCharacteristic o (graphRateEquiv p x)=physicalCharacteristic p.tree x := by
  rw [graphCharacteristic,← charpoly_submatrix_equiv _ p.vertices,graphCompartmentMatrix_transport]
  rfl

lemma diagonalCofactor_submatrix_equiv {n : ℕ} (A : Matrix V V ℝ)
    (e : Fin (n+1) ≃ V) (i : Fin (n+1)) :
    diagonalCofactor (A.submatrix e e) i=diagonalCofactor A (e i) := by
  have h : Matrix.charmatrix (A.submatrix e e)=(Matrix.charmatrix A).submatrix e e :=
    Matrix.charmatrix_reindex A e.symm
  rw [diagonalCofactor,h,Matrix.adjugate_submatrix_equiv_self]
  rfl

lemma diagonalCofactor_physical_root {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    diagonalCofactor (compartmentMatrix t x) 0=physicalRootCofactor t x := by
  have hroot : (Matrix.charmatrix (compartmentMatrix t x)).adjugate 0 0 =
      ((Matrix.charmatrix (compartmentMatrix t x)).submatrix Fin.succ Fin.succ).det := by
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
    simp
  rw [diagonalCofactor,hroot]
  change ((Matrix.charmatrix (compartmentMatrix t x)).submatrix Fin.succ Fin.succ).det =
    (Matrix.charmatrix ((compartmentMatrix t x).submatrix Fin.succ Fin.succ)).det
  congr 1
  ext i j
  by_cases h : i=j
  · subst j
    simp [Matrix.charmatrix_apply_eq]
  · simp [Matrix.charmatrix_apply_ne,h]

lemma graphRootCofactor_transport {n : ℕ} {o : V} (p : RootedTreePresentation n G o)
    (x : TreeRates n) : graphRootCofactor o (graphRateEquiv p x)=physicalRootCofactor p.tree x := by
  have h := diagonalCofactor_submatrix_equiv (graphCompartmentMatrix G o (graphRateEquiv p x)) p.vertices 0
  simpa only [graphCompartmentMatrix_transport,p.root_eq,diagonalCofactor_physical_root,
    graphRootCofactor] using h.symm

lemma scalar_sub_equiv_transport {n : ℕ} (A : Matrix V V ℝ) (e : Fin (n+1) ≃ V) (s : ℝ) :
    (Matrix.scalar V s-A).submatrix e e=Matrix.scalar (Fin (n+1)) s-A.submatrix e e := by
  ext i j
  simp [Matrix.submatrix_apply,Matrix.scalar_apply,Matrix.diagonal_apply]

/-- Exact root inverse entry transport; its physical interpretation is made
only off characteristic roots, without using totalized values at poles. -/
theorem graphRootResponse_transport {n : ℕ} {o : V} (p : RootedTreePresentation n G o)
    (x : TreeRates n) (s : ℝ) :
    graphRootResponse o (graphRateEquiv p x) s=physicalRootResponse p.tree x s := by
  have h := Matrix.inv_submatrix_equiv (Matrix.scalar V s-graphCompartmentMatrix G o (graphRateEquiv p x))
    p.vertices p.vertices
  rw [scalar_sub_equiv_transport,graphCompartmentMatrix_transport] at h
  have he := congrArg (fun M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ => M 0 0) h
  simpa only [Matrix.submatrix_apply,p.root_eq,graphRootResponse,physicalRootResponse] using he.symm

end HydrologyTree
