import HydrologyTree.SupportedPositiveGauge
import HydrologyTree.ConservationGaugeRigidity
import HydrologyTree.LeakRelocationWalk
import HydrologyTree.GraphModelInjectivity

/-! Automatic positivity for ANY real single-leak realization on an independent
finite tree, even when leakage is not at the inlet/observer. No sign assumption
is placed on the competing rates, leak, or intermediate diagonal scales. -/
open Matrix Polynomial
noncomputable section
namespace HydrologyTree
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma graphCompartment_nonedge (ell : V) (y : GraphRates G) (u v : V)
    (huv : u ≠ v) (hn : ¬G.Adj u v) : graphCompartmentMatrix G ell y u v=0 := by
  have hz (i : V) : (Matrix.single i i (1 : ℝ)) u v=0 := by
    apply Matrix.single_apply_of_ne
    rintro ⟨h1,h2⟩
    exact huv (h1.symm.trans h2)
  simp only [graphCompartmentMatrix,graphTransfer,Matrix.sub_apply,Matrix.sum_apply,
    Matrix.smul_apply,smul_eq_mul,hz,sub_zero,mul_zero]
  apply Finset.sum_eq_zero
  intro d _
  have he : ¬(d.snd=u ∧ d.fst=v) := by
    rintro ⟨h1,h2⟩
    have h := d.adj
    rw [h1,h2] at h
    exact hn h.symm
  simp [Matrix.single_apply,he]

lemma graphCompartment_tree_support {n : ℕ} {o : V} (p : RootedTreePresentation n G o)
    (ell : V) (y : GraphRates G) :
    HasTreeMatrixSupport p.tree ((graphCompartmentMatrix G ell y).submatrix p.vertices p.vertices) := by
  intro i j hij hn
  exact graphCompartment_nonedge ell y _ _ (fun h => hij (p.vertices.injective h))
    (fun h => hn ((p.adj_iff i j).mpr h))

/-- A full positive target pair forces strict positivity of EVERY real graph
rate and the unique leakage magnitude at ANY specified leakage vertex. The
competing real model is not assumed nonzero, stable, or Jacobian-regular. -/
theorem real_located_pair_forces_positive {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (ell : V) (y : GraphRates G)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i,0<r i)
    (hw : ∀ i,0<w i) (hm : (∑ i,w i)=1)
    (hP : (graphCompartmentMatrix G ell y).charpoly=stieltjesDenominator r)
    (hF : diagonalCofactor (graphCompartmentMatrix G ell y) o=stieltjesNumerator r w) :
    PositiveGraphRates y := by
  let A := graphCompartmentMatrix G ell y
  let M := A.submatrix p.vertices p.vertices
  have hMP : M.charpoly=stieltjesDenominator r :=
    (charpoly_submatrix_equiv A p.vertices).trans hP
  have hMF : diagonalCofactor M 0=stieltjesNumerator r w := by
    rw [diagonalCofactor_submatrix_equiv,p.root_eq]
    exact hF
  obtain ⟨x,h,hh,_,hMx⟩ := supported_positive_diagonal_realization p.tree M
    (graphCompartment_tree_support p ell y) r w hr hpos hw hm hMP hMF
  let y0 : PositiveGraphRateSpace G := ⟨graphRateEquiv p x.val,
    (graphRateEquiv_positive_iff p x.val).mpr x.property.1⟩
  let H : V → ℝ := fun v => h (p.vertices.symm v)
  have hH : ∀ v,H v ≠ 0 := fun v => hh _
  have hA : A=diagonalGauge H (graphCompartmentMatrix G o y0.val) := by
    rw [← graphCompartmentMatrix_transport p x.val] at hMx
    ext i j
    have he := congrArg (fun N : TreeMatrix n => N (p.vertices.symm i) (p.vertices.symm j)) hMx
    simpa only [M,Matrix.submatrix_apply,Equiv.apply_symm_apply,diagonalGauge_apply,H,y0] using he
  let z := relocatePositiveLeak hG o ell y0
  let B := graphCompartmentMatrix G ell z.val
  obtain ⟨k,hk,hB⟩ := relocatePositiveLeak_similarity hG o ell y0
  change B=diagonalGauge k (graphCompartmentMatrix G o y0.val) at hB
  have hkn : ∀ v,k v ≠ 0 := fun v => ne_of_gt (hk v)
  have hAB : A=diagonalGauge (fun v => H v/k v) B := by
    rw [hA,hB]
    ext i j
    simp only [diagonalGauge_apply]
    field_simp [hkn i,hkn j,hH j]
    <;> ring
  have hchar : B.charpoly=stieltjesDenominator r :=
    (relocatePositiveLeak_response hG o ell y0).1.trans
      ((graphCharacteristic_transport p x.val).trans x.property.2.1)
  have hdet : B.det ≠ 0 := by
    intro hz
    have heval : B.charpoly.eval 0 ≠ 0 := by
      rw [hchar]
      exact ne_of_gt (stieltjesDenominator_eval_zero_pos r hpos)
    apply heval
    rw [Matrix.eval_charpoly]
    simp [Matrix.scalar_apply,Matrix.det_neg,hz]
  have heq : A=B := graph_same_leak_gauge_unique ell y z.val (ne_of_gt z.property.1) hdet
    (fun v => H v/k v) (fun v => div_ne_zero (hH v) (hkn v)) hAB
  have hyr : y=z.val := graphRates_from_matrix_injective ell heq
  exact hyr ▸ z.property

end HydrologyTree
