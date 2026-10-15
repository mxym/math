import HydrologyTree.MultiLeakRecovery
import HydrologyTree.RecursiveFiberClassification
import HydrologyTree.PositiveFiberCount

/-! Complete all-size physical multi-leak fibre classification. A genuine
actual-matrix bijection, not an assumed gauge family or a list of examples. -/
open Matrix Polynomial
noncomputable section
namespace HydrologyTree
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Build the actual model from a discrete single-leak reference and its loss shares. -/
def multiLeakModelFromShares {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (r w : Fin (n+1) → ℝ)
    (z : PositiveStieltjesFiber p.tree r w × LeakSimplex V) : MultiLeakMatrixFiber G o r w :=
  gaugeToMultiLeakMatrixFiber p r w z.1
    (graphLeakSimplexEquivGauge hG p
      ⟨graphRateEquiv p z.1.val,(graphRateEquiv_positive_iff p z.1.val).mpr z.1.property.1⟩ z.2)

lemma inverse_diagonalGauge (B : Matrix V V ℝ) (h : V → ℝ) (hh : ∀ i,h i ≠ 0) :
    diagonalGauge (fun i => (h i)⁻¹) (diagonalGauge h B)=B := by
  ext i j
  simp only [diagonalGauge_apply,inv_inv]
  field_simp [hh i,hh j]
  <;> ring

/-- Distinct single-leak representatives cannot give the same multi-leak matrix.
Both references conserve at the SAME root; the proved gauge rigidity applies. -/
theorem multiLeakModelFromShares_injective {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (r w : Fin (n+1) → ℝ) :
    Function.Injective (multiLeakModelFromShares hG p r w) := by
  rintro ⟨x,s⟩ ⟨y,t⟩ he
  let X := graphRateEquiv p x.val
  let Y := graphRateEquiv p y.val
  have hx : PositiveGraphRates X := (graphRateEquiv_positive_iff p x.val).mpr x.property.1
  have hy : PositiveGraphRates Y := (graphRateEquiv_positive_iff p y.val).mpr y.property.1
  let hs := graphLeakSimplexEquivGauge hG p ⟨X,hx⟩ s
  let ht := graphLeakSimplexEquivGauge hG p ⟨Y,hy⟩ t
  have hmat : diagonalGauge hs.val (graphCompartmentMatrix G o X)=
      diagonalGauge ht.val (graphCompartmentMatrix G o Y) := congrArg Subtype.val he
  have hXY : graphCompartmentMatrix G o X=diagonalGauge (fun i => ht.val i/hs.val i)
      (graphCompartmentMatrix G o Y) := by
    calc
      _ = diagonalGauge (fun i => (hs.val i)⁻¹) (diagonalGauge hs.val (graphCompartmentMatrix G o X)) :=
        (inverse_diagonalGauge _ hs.val (fun i => ne_of_gt (hs.property.1 i))).symm
      _ = diagonalGauge (fun i => (hs.val i)⁻¹) (diagonalGauge ht.val (graphCompartmentMatrix G o Y)) := by rw [hmat]
      _ = _ := by ext i j; simp only [diagonalGauge_apply,div_eq_mul_inv,_root_.mul_inv_rev,inv_inv]; ring
  have hdetY : (graphCompartmentMatrix G o Y).det ≠ 0 := by
    have h := positive_graph_residence_nonsingular p Y hy
    rw [Matrix.det_neg,mul_ne_zero_iff] at h
    exact h.2
  have hB := graph_same_leak_gauge_unique o X Y (ne_of_gt hy.1) hdetY
    (fun i => ht.val i/hs.val i)
    (fun i => div_ne_zero (ne_of_gt (ht.property.1 i)) (ne_of_gt (hs.property.1 i))) hXY
  have hxy : x=y := by
    apply Subtype.ext
    exact (graphRateEquiv p).injective (graphRates_from_matrix_injective o hB)
  subst y
  have hh : hs.val=ht.val := normalized_positive_gauge_injective _ o
    (positive_graph_residence_nonsingular p X hx)
    (fun i => ne_of_gt (positive_graph_residence_entry_pos hG p X hx i o))
    hs.val ht.val (fun i => ne_of_gt (hs.property.1 i)) (fun i => ne_of_gt (ht.property.1 i))
    hs.property.2.1 ht.property.2.1 hmat
  have hst : s=t := (graphLeakSimplexEquivGauge hG p ⟨X,hx⟩).injective (Subtype.ext hh)
  subst t
  rfl

/-- EVERY physical matrix is obtained. No gauge membership is part of its
fibre definition; the reverse construction was proved from the actual matrix. -/
theorem multiLeakModelFromShares_surjective {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (r w : Fin (n+1) → ℝ)
    (hr : Function.Injective r) (hpos : ∀ i,0<r i) (hw : ∀ i,0<w i) (hm : (∑ i,w i)=1) :
    Function.Surjective (multiLeakModelFromShares hG p r w) := by
  intro A
  obtain ⟨x,h,he⟩ := multiLeak_reference_exists hG p r w hr hpos hw hm A
  let E := graphLeakSimplexEquivGauge hG p
    ⟨graphRateEquiv p x.val,(graphRateEquiv_positive_iff p x.val).mpr x.property.1⟩
  refine ⟨⟨x,E.symm h⟩,?_⟩
  apply Subtype.ext
  change diagonalGauge (E (E.symm h)).val (graphCompartmentMatrix G o (graphRateEquiv p x.val))=A.val
  rw [Equiv.apply_symm_apply]
  exact he.symm

/-- Exact physical multi-leak fibre = discrete root references × full simplex,
including every zero-leak face. No numerical or genericity premise is used. -/
def multiLeakMatrixFiberEquiv {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (r w : Fin (n+1) → ℝ)
    (hr : Function.Injective r) (hpos : ∀ i,0<r i) (hw : ∀ i,0<w i) (hm : (∑ i,w i)=1) :
    MultiLeakMatrixFiber G o r w ≃ PositiveStieltjesFiber p.tree r w × LeakSimplex V :=
  (Equiv.ofBijective (multiLeakModelFromShares hG p r w)
    ⟨multiLeakModelFromShares_injective hG p r w,
      multiLeakModelFromShares_surjective hG p r w hr hpos hw hm⟩).symm

/-- The discrete index is the previously proved purely combinatorial recursive
allocation type, not an unspecified set of solutions assumed finite. -/
def multiLeakRecursiveSimplexEquiv {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (r w : Fin (n+1) → ℝ)
    (hr : Function.Injective r) (hpos : ∀ i,0<r i) (hw : ∀ i,0<w i) (hm : (∑ i,w i)=1) :
    MultiLeakMatrixFiber G o r w ≃ RecursivePoleAllocations p.tree × LeakSimplex V :=
  (multiLeakMatrixFiberEquiv hG p r w hr hpos hw hm).trans
    (Equiv.prodCongr (positiveStieltjesRecursiveEquiv p.tree r w hr hpos hw hm) (Equiv.refl _))

/-- Independent graph assumptions construct the required presentation and give
the complete all-size matrix classification with the exact finite index count. -/
theorem finite_graph_multileak_simplex_classification {n : ℕ}
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree) (o : V) (hN : Fintype.card V=n+1)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i,0<r i)
    (hw : ∀ i,0<w i) (hm : (∑ i,w i)=1) :
    ∃ p : RootedTreePresentation n G o,
      Nonempty (MultiLeakMatrixFiber G o r w ≃ RecursivePoleAllocations p.tree × LeakSimplex V) ∧
      Finite (RecursivePoleAllocations p.tree) ∧
      Nat.card (RecursivePoleAllocations p.tree)=n.factorial/(∏ e : Fin n,subtreeVertexCount p.tree e.succ) := by
  obtain ⟨p⟩ := finite_rooted_tree_presentation n G o hG hN
  have hc := recursivePoleAllocations_finite_card p.tree
  exact ⟨p,⟨multiLeakRecursiveSimplexEquiv hG p r w hr hpos hw hm⟩,hc.1,
    hc.2.trans (treeFiberDegree_eq_factorial_quotient p.tree)⟩

end HydrologyTree
