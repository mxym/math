import HydrologyTree.TreeMomentRigidity
import HydrologyTree.GraphMatrixTransport
import HydrologyTree.MatrixGaugeWeight
import HydrologyTree.LeakRelocationWalk
import HydrologyTree.GraphLeakCofactor

/-! Low-order collocated observations on an independent finite tree. The actual
first two diagonal matrix moments identify every parameter at a specified leak
site, including nongeneric and nonminimal positive references. -/
open Matrix
noncomputable section
namespace HydrologyTree
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The two nonconstant coefficients of the local resolvent expansion, also
identified below with derivatives of actual zero-initial constant-input outputs. -/
def diagonalTwoJet (A : Matrix V V ℝ) : (V → ℝ) × (V → ℝ) :=
  (fun v => A v v,fun v => (A*A) v v)

lemma matrix_square_submatrix_equiv {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix V V ℝ) (e : I ≃ V) (i j : I) :
    (A.submatrix e e*A.submatrix e e) i j=(A*A) (e i) (e j) := by
  simp only [Matrix.mul_apply,Matrix.submatrix_apply]
  exact e.sum_comp (fun v => A (e i) v*A v (e j))

/-- Nonzero diagonal gauges preserve both actual low-order coefficients. -/
theorem diagonalTwoJet_gauge (A : Matrix V V ℝ) (h : V → ℝ) (hh : ∀ v,h v ≠ 0) :
    diagonalTwoJet (diagonalGauge h A)=diagonalTwoJet A := by
  apply Prod.ext
  · funext v
    change diagonalGauge h A v v=A v v
    rw [diagonalGauge_apply]
    field_simp [hh v]
  · funext v
    change (diagonalGauge h A*diagonalGauge h A) v v=(A*A) v v
    simp only [Matrix.mul_apply]
    exact Finset.sum_congr rfl (fun j _ => diagonalGauge_edge_product A h hh v j)

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- For a known leak site, two diagonal moments at all original vertices give
global identifiability. The reference need only have nonzero rates directed
toward that site; the competing real rates have NO sign or rank restrictions. -/
theorem graph_two_diagonal_jets_identify {n : ℕ} {ell : V}
    (q : RootedTreePresentation n G ell) (x y : GraphRates G)
    (ha : ∀ e : Fin n, x.2 (treeDartEquiv q (.inl e)) ≠ 0)
    (h : diagonalTwoJet (graphCompartmentMatrix G ell x)=
      diagonalTwoJet (graphCompartmentMatrix G ell y)) : x=y := by
  obtain ⟨u,rfl⟩ := (graphRateEquiv q).surjective x
  obtain ⟨v,rfl⟩ := (graphRateEquiv q).surjective y
  apply congrArg (graphRateEquiv q)
  apply physical_two_diagonal_moments_identify q.tree u v
  · intro e
    simpa only [graphRateEquiv_inward] using ha e
  · intro i
    have hh := congrArg (fun z : (V → ℝ) × (V → ℝ) => z.1 (q.vertices i)) h
    have hU := congrArg (fun A : TreeMatrix n => A i i) (graphCompartmentMatrix_transport q u)
    have hV := congrArg (fun A : TreeMatrix n => A i i) (graphCompartmentMatrix_transport q v)
    exact hU.symm.trans (hh.trans hV)
  · intro i
    have hh := congrArg (fun z : (V → ℝ) × (V → ℝ) => z.2 (q.vertices i)) h
    have hU := matrix_square_submatrix_equiv (graphCompartmentMatrix G ell (graphRateEquiv q u)) q.vertices i i
    have hV := matrix_square_submatrix_equiv (graphCompartmentMatrix G ell (graphRateEquiv q v)) q.vertices i i
    rw [graphCompartmentMatrix_transport] at hU hV
    exact hU.trans (hh.trans hV.symm)

/-- Leak relocation exhausts the remaining ambiguity in all-node two-jet data.
Preservation itself requires no full-mode or simple-spectrum premise. -/
lemma relocated_diagonalTwoJet (hG : G.IsTree) (ell ell' : V)
    (x : PositiveGraphRateSpace G) :
    diagonalTwoJet (graphCompartmentMatrix G ell' (relocatePositiveLeak hG ell ell' x).val)=
      diagonalTwoJet (graphCompartmentMatrix G ell x.val) := by
  obtain ⟨h,hh,hM⟩ := relocatePositiveLeak_similarity hG ell ell' x
  rw [hM]
  exact diagonalTwoJet_gauge _ h (fun v => ne_of_gt (hh v))

/-- Unrestricted-real uniqueness at ANY specified site follows from just
all-node low-order data of an arbitrary positive reference at any other site. -/
theorem graph_diagonalTwoJet_fiber_unique {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (ell : V) (x : PositiveGraphRateSpace G)
    (y : GraphRates G)
    (hy : diagonalTwoJet (graphCompartmentMatrix G ell y)=
      diagonalTwoJet (graphCompartmentMatrix G o x.val)) :
    y=(relocatePositiveLeak hG o ell x).val := by
  let z := relocatePositiveLeak hG o ell x
  apply (graph_two_diagonal_jets_identify (leakRootPresentation hG p ell) z.val y
    (fun e => ne_of_gt (z.property.2 _)) ?_).symm
  exact (relocated_diagonalTwoJet hG o ell x).trans hy.symm

end HydrologyTree
