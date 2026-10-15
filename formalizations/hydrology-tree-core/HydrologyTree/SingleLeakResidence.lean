import HydrologyTree.ResidenceGauge
import HydrologyTree.LeakRelocationWalk
import HydrologyTree.GraphLeakCofactor
import HydrologyTree.PositiveSpectrum
import HydrologyTree.GraphMassBalance

/-! Strict entrywise positivity of the ACTUAL residence inverse for every
positive finite single-leak tree. No inverse-positivity axiom is assumed. -/
open Matrix Polynomial
noncomputable section
namespace HydrologyTree
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma single_leak_inverse_row (B : Matrix V V ℝ) (o : V) (l : ℝ)
    (hB : (-B).det ≠ 0) (hl : l ≠ 0)
    (hc : ∀ j, (∑ i,B i j)=if j=o then -l else 0) (j : V) :
    residenceMatrix B o j=l⁻¹ := by
  have he : (fun _ : V => (1 : ℝ)) ᵥ* (-B)=Pi.single o l := by
    funext k
    simp only [Matrix.vecMul,dotProduct,Matrix.neg_apply,one_mul,Finset.sum_neg_distrib,hc,Pi.single_apply]
    by_cases hk : k=o <;> simp [hk,eq_comm]
  have hr := congrArg (fun v : V → ℝ => (v ᵥ* residenceMatrix B) j) he
  rw [leakGauge_inverse_recovery B hB,Matrix.single_vecMul] at hr
  change 1=l*residenceMatrix B o j at hr
  apply mul_left_cancel₀ hl
  rw [mul_inv_cancel₀ hl]
  exact hr.symm

variable {G : SimpleGraph V} [DecidableRel G.Adj]

lemma positive_graph_residence_nonsingular {n : ℕ} {o : V}
    (p : RootedTreePresentation n G o) (y : GraphRates G) (hy : PositiveGraphRates y) :
    (-(graphCompartmentMatrix G o y)).det ≠ 0 := by
  obtain ⟨x,rfl⟩ := (graphRateEquiv p).surjective y
  have hx := (graphRateEquiv_positive_iff p x).mp hy
  have hP := physical_characteristic_pos_on_nonnegative p.tree x (hx.1 0)
    (fun e => hx.1 e.succ) hx.2 0 (le_refl 0)
  have hg : 0 < (graphCompartmentMatrix G o (graphRateEquiv p x)).charpoly.eval 0 := by
    change 0 < (graphCharacteristic o (graphRateEquiv p x)).eval 0
    rwa [graphCharacteristic_transport]
  rw [Matrix.eval_charpoly] at hg
  simpa [Matrix.scalar_apply] using ne_of_gt hg

/-- Relocating the single leak to each row proves strict positivity of every
inverse entry. This applies also to positive spectral-collision models. -/
theorem positive_graph_residence_entry_pos {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (y : GraphRates G) (hy : PositiveGraphRates y)
    (i j : V) : 0 < residenceMatrix (graphCompartmentMatrix G o y) i j := by
  let z := relocatePositiveLeak hG o i ⟨y,hy⟩
  obtain ⟨h,hh,hM⟩ := relocatePositiveLeak_similarity hG o i ⟨y,hy⟩
  have hB := positive_graph_residence_nonsingular p y hy
  have hZ := positive_graph_residence_nonsingular (leakRootPresentation hG p i) z.val z.property
  have hr := single_leak_inverse_row (graphCompartmentMatrix G i z.val) i z.val.1 hZ
    (ne_of_gt z.property.1) (graphCompartment_column_sum i z.val) j
  change residenceMatrix (graphCompartmentMatrix G i (relocatePositiveLeak hG o i ⟨y,hy⟩).val) i j=_ at hr
  rw [hM,residenceMatrix_gauge _ hB h (fun v => ne_of_gt (hh v)),diagonalGauge_apply] at hr
  have hp : 0 < h i * residenceMatrix (graphCompartmentMatrix G o y) i j * (h j)⁻¹ := by
    rw [hr]
    exact inv_pos.mpr z.property.1
  exact (mul_pos_iff_of_pos_left (hh i)).mp
    ((mul_pos_iff_of_pos_right (inv_pos.mpr (hh j))).mp hp)

/-- Unconditional finite-tree specialization of the generic simplex theorem:
all inverse and positivity hypotheses are proved from actual positive rates. -/
def graphLeakSimplexEquivGauge {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (y : PositiveGraphRateSpace G) :
    LeakSimplex V ≃ NonnegativeLeakGauge (graphCompartmentMatrix G o y.val) o :=
  leakSimplexEquivGauge _ o (positive_graph_residence_nonsingular p y.val y.property)
    (positive_graph_residence_entry_pos hG p y.val y.property)

end HydrologyTree
