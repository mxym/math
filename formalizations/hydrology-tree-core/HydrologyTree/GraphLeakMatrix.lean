import HydrologyTree.GraphMatrixTransport
import HydrologyTree.LeakRelocationRates

/-! Actual matrix formula for moving the unique leak across an edge. All
unchanged diagonals and unchanged rates are proved from the graph construction. -/
open Matrix
noncomputable section
namespace HydrologyTree
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def dartTransferMatrix (d : G.Dart) : Matrix V V ℝ :=
  Matrix.single d.snd d.fst 1-Matrix.single d.fst d.fst 1

lemma graphTransfer_eq_smul (y : GraphRates G) (d : G.Dart) :
    graphTransfer y d=y.2 d • dartTransferMatrix d := rfl

lemma slideLeak_reverse_difference (d : G.Dart) (y : GraphRates G) (ht : y.2 d+y.1 ≠ 0) :
    (slideLeakRates d y).2 d.symm=y.2 d.symm-(slideLeakRates d y).1 := by
  have he := slideLeak_reverse_plus_leak d y ht
  linarith

lemma graphTransfer_slide_difference (d e : G.Dart) (y : GraphRates G) (ht : y.2 d+y.1 ≠ 0) :
    graphTransfer (slideLeakRates d y) e=graphTransfer y e+
      (if e=d then y.1 • dartTransferMatrix d else 0)-
      (if e=d.symm then (slideLeakRates d y).1 • dartTransferMatrix d.symm else 0) := by
  by_cases he : e=d
  · subst e
    simp [graphTransfer_eq_smul,slideLeak_forward,Ne.symm d.symm_ne,add_smul]
  · by_cases hr : e=d.symm
    · subst e
      rw [graphTransfer_eq_smul,slideLeak_reverse_difference d y ht]
      simp [graphTransfer_eq_smul,d.symm_ne,sub_smul]
    · rw [graphTransfer_eq_smul,slideLeak_other d e y he hr]
      simp [graphTransfer_eq_smul,he,hr]

/-- Moving the leak changes only two off-diagonal entries; every diagonal
remains exactly unchanged. This statement is about the independent graph matrix. -/
theorem graphCompartment_slide_update (d : G.Dart) (y : GraphRates G) (ht : y.2 d+y.1 ≠ 0) :
    graphCompartmentMatrix G d.snd (slideLeakRates d y) =
      graphCompartmentMatrix G d.fst y+y.1 • Matrix.single d.snd d.fst 1-
        (slideLeakRates d y).1 • Matrix.single d.fst d.snd 1 := by
  have he : (∑ e : G.Dart, graphTransfer (slideLeakRates d y) e)=
      (∑ e : G.Dart, graphTransfer y e)+y.1 • dartTransferMatrix d-
        (slideLeakRates d y).1 • dartTransferMatrix d.symm := by
    simp only [graphTransfer_slide_difference d _ y ht,Finset.sum_sub_distrib,Finset.sum_add_distrib]
    simp
  simp only [graphCompartmentMatrix]
  rw [he]
  simp only [dartTransferMatrix,leakDart_symm_fst,leakDart_symm_snd,smul_sub]
  abel

end HydrologyTree
