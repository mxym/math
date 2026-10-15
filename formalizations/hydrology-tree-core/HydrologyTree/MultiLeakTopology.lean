import HydrologyTree.MultiLeakRateFiber
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Separation.Hausdorff

/-! Topological, not merely set-theoretic, simplex classification. Compactness,
continuity in the original matrix/rate coordinates and inverse continuity are
proved. The finite root-reference factor has its inherited discrete topology. -/
open Matrix Polynomial
noncomputable section
set_option maxHeartbeats 1000000
namespace HydrologyTree
variable {V : Type*} [Fintype V] [DecidableEq V]

instance leakSimplexCompact : CompactSpace (LeakSimplex V) := by
  change CompactSpace (stdSimplex ℝ V)
  infer_instance

lemma continuous_simplexGauge (R : Matrix V V ℝ) (o : V) : Continuous (simplexGauge R o) := by
  apply continuous_pi
  intro j
  simp only [simplexGauge,simplexLossWeight,Matrix.vecMul,dotProduct,div_eq_mul_inv]
  fun_prop

lemma continuous_gaugeShares (B : Matrix V V ℝ) (o : V)
    (hR : ∀ i j,0<residenceMatrix B i j) :
    Continuous (fun p : LeakSimplex V => diagonalGauge (simplexGauge (residenceMatrix B) o p.val) B) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simp only [diagonalGauge_apply]
  have hh : Continuous (fun p : LeakSimplex V => simplexGauge (residenceMatrix B) o p.val) :=
    (continuous_simplexGauge (residenceMatrix B) o).comp continuous_subtype_val
  exact (((continuous_apply i).comp hh).mul continuous_const).mul
    (((continuous_apply j).comp hh).inv₀ (fun p => ne_of_gt (simplexGauge_pos _ o hR p j)))

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The forward physical map is continuous on every closed simplex, including
its zero-leak faces, and on the finite disjoint union of all root references. -/
theorem continuous_multiLeakModelFromShares {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (r w : Fin (n+1) → ℝ)
    (hr : Function.Injective r) (hpos : ∀ i,0<r i) (hw : ∀ i,0<w i) (hm : (∑ i,w i)=1) :
    Continuous (multiLeakModelFromShares hG p r w) := by
  letI : Finite (PositiveStieltjesFiber p.tree r w) :=
    (positive_stieltjes_fiber_finite_card p.tree r w hr hpos hw hm).1
  apply continuous_prod_of_discrete_left.mpr
  intro x
  have hc : Continuous (fun s : LeakSimplex V =>
      diagonalGauge (simplexGauge (residenceMatrix (graphCompartmentMatrix G o (graphRateEquiv p x.val))) o s.val)
        (graphCompartmentMatrix G o (graphRateEquiv p x.val))) :=
    continuous_gaugeShares _ o (positive_graph_residence_entry_pos hG p _
      ((graphRateEquiv_positive_iff p x.val).mpr x.property.1))
  have hv : (fun s : LeakSimplex V => (multiLeakModelFromShares hG p r w (x,s)).val) =
      (fun s : LeakSimplex V =>
        diagonalGauge (simplexGauge (residenceMatrix (graphCompartmentMatrix G o (graphRateEquiv p x.val))) o s.val)
          (graphCompartmentMatrix G o (graphRateEquiv p x.val))) := rfl
  apply continuous_induced_rng.mpr
  change Continuous (fun s : LeakSimplex V => (multiLeakModelFromShares hG p r w (x,s)).val)
  rw [hv]
  exact hc

/-- The actual full physical matrix fibre is HOMEOMORPHIC to a finite discrete
set of root representatives times the full closed standard simplex. -/
def multiLeakMatrixFiberHomeomorph {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (r w : Fin (n+1) → ℝ)
    (hr : Function.Injective r) (hpos : ∀ i,0<r i) (hw : ∀ i,0<w i) (hm : (∑ i,w i)=1) :
    MultiLeakMatrixFiber G o r w ≃ₜ PositiveStieltjesFiber p.tree r w × LeakSimplex V := by
  letI : Finite (PositiveStieltjesFiber p.tree r w) :=
    (positive_stieltjes_fiber_finite_card p.tree r w hr hpos hw hm).1
  let E := (multiLeakMatrixFiberEquiv hG p r w hr hpos hw hm).symm
  have hc : Continuous E := continuous_multiLeakModelFromShares hG p r w hr hpos hw hm
  exact (E.toHomeomorphOfContinuousClosed hc hc.isClosedMap).symm

lemma continuous_multiLeakMatrix : Continuous (multiLeakMatrix G) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simp only [multiLeakMatrix,graphTransfer,Matrix.sub_apply,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  fun_prop

lemma continuous_ratesOfMultiMatrix : Continuous (ratesOfMultiMatrix (G := G)) := by
  apply Continuous.prodMk
  · apply continuous_pi
    intro j
    simp only [ratesOfMultiMatrix,matrixLeak]
    fun_prop
  · apply continuous_pi
    intro d
    fun_prop [ratesOfMultiMatrix]

def multiLeakRateMatrixHomeomorph {n : ℕ} (o : V) (r w : Fin (n+1) → ℝ) :
    MultiLeakCoefficientFiber G o r w ≃ₜ MultiLeakMatrixFiber G o r w where
  toEquiv := multiLeakRateMatrixEquiv o r w
  continuous_toFun := Continuous.subtype_mk (continuous_multiLeakMatrix.comp continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk (continuous_ratesOfMultiMatrix.comp continuous_subtype_val) _

def multiLeakResponseCoefficientHomeomorph {n : ℕ} (o : V) (hN : Fintype.card V=n+1)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i,0<r i)
    (hw : ∀ i,0<w i) (hm : (∑ i,w i)=1) :
    MultiLeakResponseFiber G o r w ≃ₜ MultiLeakCoefficientFiber G o r w where
  toEquiv := multiLeakResponseCoefficientEquiv o hN r w hr hpos hw hm
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val _
  continuous_invFun := Continuous.subtype_mk continuous_subtype_val _

/-- Exact topological classification in original physical RATE coordinates from
only root-response data. Not just a parametrized surrogate or rational samples. -/
def multiLeakResponseHomeomorph {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (r w : Fin (n+1) → ℝ)
    (hr : Function.Injective r) (hpos : ∀ i,0<r i) (hw : ∀ i,0<w i) (hm : (∑ i,w i)=1) :
    MultiLeakResponseFiber G o r w ≃ₜ PositiveStieltjesFiber p.tree r w × LeakSimplex V :=
  (multiLeakResponseCoefficientHomeomorph o (presentation_card p) r w hr hpos hw hm).trans
    ((multiLeakRateMatrixHomeomorph o r w).trans (multiLeakMatrixFiberHomeomorph hG p r w hr hpos hw hm))

/-- Independent graph entry: exactly the known hook-count number of topological
simplices, with the standard simplex carrying all its boundary faces. -/
theorem finite_graph_multileak_response_homeomorphism {n : ℕ}
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree) (o : V) (hN : Fintype.card V=n+1)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i,0<r i)
    (hw : ∀ i,0<w i) (hm : (∑ i,w i)=1) :
    ∃ p : RootedTreePresentation n G o,
      Nonempty (MultiLeakResponseFiber G o r w ≃ₜ PositiveStieltjesFiber p.tree r w × LeakSimplex V) ∧
      Finite (PositiveStieltjesFiber p.tree r w) ∧
      Nat.card (PositiveStieltjesFiber p.tree r w)=n.factorial/(∏ e : Fin n,subtreeVertexCount p.tree e.succ) := by
  obtain ⟨p⟩ := finite_rooted_tree_presentation n G o hG hN
  have hc := positive_stieltjes_fiber_exact_card p.tree r w hr hpos hw hm
  exact ⟨p,⟨multiLeakResponseHomeomorph hG p r w hr hpos hw hm⟩,hc⟩

end HydrologyTree
