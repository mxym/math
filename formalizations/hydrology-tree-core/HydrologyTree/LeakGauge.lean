import HydrologyTree.DiagonalGauge
import HydrologyTree.GraphLeakCut
import HydrologyTree.GraphLeakMatrix

/-! The positive edge relocation is an ACTUAL diagonal similarity. The required
cut is constructed for every independent finite tree; no spectral input is used. -/
open Matrix Polynomial
noncomputable section
namespace HydrologyTree
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def leakCutWeight {d : G.Dart} (c : GraphLeakCut d) (y : GraphRates G) (v : V) : ℝ :=
  if c.side v then (y.2 d+y.1)/y.2 d else 1

lemma leakCutWeight_pos {d : G.Dart} (c : GraphLeakCut d) (y : GraphRates G)
    (hy : PositiveGraphRates y) (v : V) : 0<leakCutWeight c y v := by
  unfold leakCutWeight
  split
  · exact div_pos (add_pos (hy.2 d) hy.1) (hy.2 d)
  · norm_num

lemma leakCutWeight_scaled_rate {d : G.Dart} (c : GraphLeakCut d) (y : GraphRates G)
    (hy : PositiveGraphRates y) (e : G.Dart) :
    leakCutWeight c y e.snd*y.2 e*(leakCutWeight c y e.fst)⁻¹=(slideLeakRates d y).2 e := by
  have hf := ne_of_gt (hy.2 d)
  have ht := ne_of_gt (add_pos (hy.2 d) hy.1)
  by_cases he : e=d
  · subst e
    simp only [slideLeak_forward,leakCutWeight,c.source,c.target,Bool.false_eq_true,
      if_false,if_true,inv_one,mul_one]
    field_simp
  · by_cases hr : e=d.symm
    · subst e
      simp only [slideLeak_reverse,leakCutWeight,leakDart_symm_fst,
        leakDart_symm_snd,c.source,c.target,Bool.false_eq_true,if_false,if_true,one_mul]
      field_simp
    · rw [slideLeak_other d e y he hr]
      have hw : leakCutWeight c y e.fst=leakCutWeight c y e.snd := by
        simp only [leakCutWeight,c.same_side e he hr]
      rw [hw]
      field_simp [ne_of_gt (leakCutWeight_pos c y hy e.snd)]

lemma graphTransfer_eq_singles (y : GraphRates G) (e : G.Dart) :
    graphTransfer y e=Matrix.single e.snd e.fst (y.2 e)-Matrix.single e.fst e.fst (y.2 e) := by
  simp only [graphTransfer,smul_sub,Matrix.smul_single,smul_eq_mul,mul_one]

lemma matrix_single_sub (i j : V) (a b : ℝ) :
    Matrix.single i j (a-b)=Matrix.single i j a-Matrix.single i j b := by
  simp only [sub_eq_add_neg,Matrix.single_add,← Matrix.single_neg]

lemma leakGauge_transfer {d : G.Dart} (c : GraphLeakCut d) (y : GraphRates G)
    (hy : PositiveGraphRates y) (e : G.Dart) :
    diagonalGauge (leakCutWeight c y) (graphTransfer y e)=graphTransfer y e+
      (if e=d then Matrix.single d.snd d.fst y.1 else 0)-
      (if e=d.symm then Matrix.single d.fst d.snd (slideLeakRates d y).1 else 0) := by
  have hh : ∀ v, leakCutWeight c y v ≠ 0 := fun v => ne_of_gt (leakCutWeight_pos c y hy v)
  rw [graphTransfer_eq_singles,diagonalGauge_sub,diagonalGauge_single,
    diagonalGauge_diagonal_single _ hh,leakCutWeight_scaled_rate c y hy e]
  by_cases he : e=d
  · subst e
    simp only [slideLeak_forward,if_true,Ne.symm d.symm_ne,if_false,sub_zero,Matrix.single_add]
    abel
  · by_cases hr : e=d.symm
    · subst e
      rw [slideLeak_reverse_difference d y (ne_of_gt (add_pos (hy.2 d) hy.1)),matrix_single_sub]
      simp only [d.symm_ne,if_false,if_true,add_zero,leakDart_symm_fst,leakDart_symm_snd]
      abel
    · rw [slideLeak_other d e y he hr]
      simp [he,hr]

/-- Exact equality of independently constructed physical matrices with different
leak vertices. All original graph coordinates and diagonals are retained. -/
theorem graph_leak_slide_similarity {d : G.Dart} (c : GraphLeakCut d) (y : GraphRates G)
    (hy : PositiveGraphRates y) :
    graphCompartmentMatrix G d.snd (slideLeakRates d y)=
      diagonalGauge (leakCutWeight c y) (graphCompartmentMatrix G d.fst y) := by
  have hh : ∀ v, leakCutWeight c y v ≠ 0 := fun v => ne_of_gt (leakCutWeight_pos c y hy v)
  have hsum : diagonalGauge (leakCutWeight c y) (∑ e : G.Dart, graphTransfer y e)=
      (∑ e : G.Dart, graphTransfer y e)+Matrix.single d.snd d.fst y.1-
        Matrix.single d.fst d.snd (slideLeakRates d y).1 := by
    rw [diagonalGauge_sum]
    simp only [leakGauge_transfer c y hy,Finset.sum_sub_distrib,Finset.sum_add_distrib]
    simp
  rw [graphCompartment_slide_update d y (ne_of_gt (add_pos (hy.2 d) hy.1))]
  simp only [graphCompartmentMatrix,diagonalGauge_sub,diagonalGauge_smul,
    diagonalGauge_diagonal_single _ hh,Matrix.smul_single,smul_eq_mul,mul_one]
  rw [hsum]
  abel

/-- Every finite tree edge supplies the cut: no separation or similarity premise
is left to the user. The new positive model moves the actual sole leak one step. -/
theorem finite_tree_leak_slide (hG : G.IsTree) (d : G.Dart) (y : GraphRates G)
    (hy : PositiveGraphRates y) :
    ∃ h : V → ℝ, (∀ v, 0<h v) ∧
      graphCompartmentMatrix G d.snd (slideLeakRates d y)=diagonalGauge h (graphCompartmentMatrix G d.fst y) := by
  let c := finiteTreeLeakCut hG d
  exact ⟨leakCutWeight c y,leakCutWeight_pos c y hy,graph_leak_slide_similarity c y hy⟩

end HydrologyTree
