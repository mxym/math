import Entry005.PaperWitnessCombinatorics

noncomputable section
open MeasureTheory
open scoped BigOperators Matrix

namespace Entry005

theorem paper_iid_anchor_split_symm {α : Type*} [MeasurableSpace α] (d : ℕ)
    (w : Fin (d + 1) → α) (x : α) :
    (iidAnchorTestSplit d).symm (w, x) = Fin.cases x w := by
  ext k
  induction k using Fin.cases <;>
    simp [iidAnchorTestSplit, iidSplit, MeasurableEquiv.piFinSuccAbove_symm_apply,
      Fin.insertNthEquiv, MeasurableEquiv.prodComm]

theorem paper_iid_base_pair_split {α : Type*} [MeasurableSpace α] (d : ℕ)
    (g : Fin (d + 2) → α) :
    iidBasePairSplit d g = ((fun k => g k.succ.succ), (g 0, g 1)) := by
  ext k <;> simp [iidBasePairSplit, iidAnchorTestSplit, iidSplit,
    MeasurableEquiv.prodComm, MeasurableEquiv.prodAssoc, MeasurableEquiv.prodCongr,
    MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv, Fin.tail]

theorem paper_iid_transport {α : Type*} [MeasurableSpace α] (d : ℕ)
    (p : Equiv.Perm (Fin (d + 2))) (w : Fin (d + 1) → α) (x : α) :
    iidWitnessTransport d p (w, x) =
      ((fun k => Fin.cases x w (p.symm k.succ.succ)),
        (Fin.cases x w (p.symm 0), Fin.cases x w (p.symm 1))) := by
  simp only [iidWitnessTransport, MeasurableEquiv.trans_apply,
    paper_iid_anchor_split_symm, paper_iid_base_pair_split]
  simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply]

def paperFirstPermutation (d : ℕ) (i : Fin (d + 1)) : Equiv.Perm (Fin (d + 2)) :=
  Equiv.swap 1 i.succ

def paperPairPermutation (d : ℕ) (i j : Fin (d + 1)) : Equiv.Perm (Fin (d + 2)) :=
  (Equiv.swap 0 j.succ).trans (Equiv.swap 1 i.succ)

theorem paper_swap_succ {d : ℕ} (i k : Fin (d + 1)) :
    Equiv.swap 1 i.succ k.succ = (Equiv.swap 0 i k).succ := by
  have hinj : Function.Injective (Fin.succ : Fin (d + 1) → Fin (d + 2)) :=
    fun _ _ h => Fin.succ_inj.mp h
  simpa using hinj.swap_apply (0 : Fin (d + 1)) i k

theorem paper_first_transport {α : Type*} [MeasurableSpace α] (d : ℕ)
    (i : Fin (d + 1)) (w : Fin (d + 1) → α) (x : α) :
    iidWitnessTransport d (paperFirstPermutation d i) (w, x) =
      ((fun k => w (Equiv.swap 0 i k.succ)), (x, w i)) := by
  rw [paper_iid_transport]
  simp [paperFirstPermutation, paper_swap_succ]
  have h0 : Equiv.swap 1 i.succ (0 : Fin (d + 2)) = 0 :=
    Equiv.swap_apply_of_ne_of_ne (by simp) (Fin.succ_ne_zero i).symm
  simp [h0]

theorem paper_first_matrices {d : ℕ} (i : Fin (d + 1))
    (w : Fin (d + 1) → Fin d → ℝ) (x : Fin d → ℝ) :
    witnessMatrix (fun k => w (Equiv.swap 0 i k.succ)) (w i) =
      (anchorMatrix w).submatrix id (Equiv.swap 0 i) ∧
    witnessMatrix (fun k => w (Equiv.swap 0 i k.succ)) x =
      ((anchorMatrix w).updateCol i (liftedCoordinates id x)).submatrix id
        (Equiv.swap 0 i) := by
  constructor
  · ext r c
    induction c using Fin.cases <;>
      simp [witnessMatrix, Matrix.submatrix, anchor_matrix_entry]
  · ext r c
    induction c using Fin.cases with
    | zero => simp [witnessMatrix, Matrix.submatrix, Matrix.updateCol_apply, liftedCoordinates]
    | succ c =>
      have hi : Equiv.swap 0 i c.succ ≠ i := by
        intro h
        have h' := (Equiv.swap 0 i).injective (h.trans (Equiv.swap_apply_left 0 i).symm)
        exact Fin.succ_ne_zero c h'
      simp [witnessMatrix, Matrix.submatrix, Matrix.updateCol_apply, hi, anchor_matrix_entry]

theorem paper_sign_abs {n : ℕ} (p : Equiv.Perm (Fin n)) :
    |((p.sign : ℤ) : ℝ)| = 1 := by
  exact_mod_cast Equiv.Perm.sign_abs p

theorem paper_opposite_symm (a b : ℝ) : oppositeWitness a b = oppositeWitness b a := by
  simp [oppositeWitness, min_comm, add_comm]

theorem paper_first_witness {d : ℕ} (i : Fin (d + 1))
    (w : Fin (d + 1) → Fin d → ℝ) (x : Fin d → ℝ) :
    let z := iidWitnessTransport d (paperFirstPermutation d i) (w, x)
    oppositeWitness (liftedDeterminant z.1 z.2.1) (liftedDeterminant z.1 z.2.2) =
      oppositeWitness (anchorMatrix w).det (replacementDeterminant w x i) := by
  dsimp only
  rw [paper_first_transport]
  dsimp only
  unfold liftedDeterminant
  rw [(paper_first_matrices i w x).1, (paper_first_matrices i w x).2,
    Matrix.det_permute', Matrix.det_permute']
  rw [opposite_witness_mul, paper_sign_abs, one_mul]
  exact paper_opposite_symm _ _

theorem paper_cases_swap_zero {α : Type*} {d : ℕ}
    (j k : Fin (d + 1)) (w : Fin (d + 1) → α) (x : α) :
    Fin.cases x w (Equiv.swap 0 j.succ k.succ) = Function.update w j x k := by
  by_cases h : k = j
  · subst k
    simp
  · have h' : k.succ ≠ j.succ := fun heq => h (Fin.succ_inj.mp heq)
    simp [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero k) h', h]

theorem paper_pair_transport {α : Type*} [MeasurableSpace α] (d : ℕ)
    (i j : Fin (d + 1)) (hij : i < j) (w : Fin (d + 1) → α) (x : α) :
    iidWitnessTransport d (paperPairPermutation d i j) (w, x) =
      ((fun k => Function.update w j x (Equiv.swap 0 i k.succ)), (w j, w i)) := by
  rw [paper_iid_transport]
  have h0 : Equiv.swap 1 i.succ (0 : Fin (d + 2)) = 0 :=
    Equiv.swap_apply_of_ne_of_ne (by simp) (Fin.succ_ne_zero i).symm
  simp only [paperPairPermutation, Equiv.symm_trans_apply, Equiv.symm_swap,
    paper_swap_succ, paper_cases_swap_zero, h0, Equiv.swap_apply_left,
    Fin.cases_succ]
  simp [Function.update_of_ne (ne_of_lt hij)]

theorem paper_anchor_update {d : ℕ} (w : Fin (d + 1) → Fin d → ℝ)
    (x : Fin d → ℝ) (j : Fin (d + 1)) :
    anchorMatrix (Function.update w j x) =
      (anchorMatrix w).updateCol j (liftedCoordinates id x) := by
  ext r c
  by_cases h : c = j
  · subst c
    simp [anchor_matrix_entry, liftedCoordinates]
  · simp [anchor_matrix_entry, h]

theorem paper_pair_second_matrix {d : ℕ} (i j : Fin (d + 1)) (hij : i < j)
    (w : Fin (d + 1) → Fin d → ℝ) (x : Fin d → ℝ) :
    witnessMatrix (fun k => Function.update w j x (Equiv.swap 0 i k.succ)) (w i) =
      ((anchorMatrix w).updateCol j (liftedCoordinates id x)).submatrix id
        (Equiv.swap 0 i) := by
  simpa only [paper_anchor_update, Function.update_of_ne (ne_of_lt hij)] using
    (paper_first_matrices i (Function.update w j x) x).1

theorem paper_pair_first_matrix {d : ℕ} (i j : Fin (d + 1)) (hij : i < j)
    (w : Fin (d + 1) → Fin d → ℝ) (x : Fin d → ℝ) :
    witnessMatrix (fun k => Function.update w j x (Equiv.swap 0 i k.succ)) (w j) =
      ((anchorMatrix w).updateCol i (liftedCoordinates id x)).submatrix id
        ((Equiv.swap 0 j).trans (Equiv.swap 0 i)) := by
  have hj0 : j ≠ 0 := by intro h; subst j; exact (not_lt_of_ge (Fin.zero_le i)) hij
  have hji : j ≠ i := (ne_of_lt hij).symm
  have hqj : Equiv.swap 0 i j = j := Equiv.swap_apply_of_ne_of_ne hj0 hji
  ext r c
  induction c using Fin.cases with
  | zero =>
    simp [witnessMatrix, Matrix.submatrix, Matrix.updateCol_apply,
      Equiv.trans_apply, hqj, hji, anchor_matrix_entry]
  | succ c =>
    by_cases hc : c.succ = j
    · have heq : Equiv.swap 0 i c.succ = j := hc ▸ hqj
      simp only [witnessMatrix, Fin.cases_succ]
      simp [hqj, Matrix.submatrix, Matrix.updateCol_apply,
        Equiv.trans_apply, hc, liftedCoordinates]
    · have hqne : Equiv.swap 0 i c.succ ≠ j := by
        intro h
        exact hc ((Equiv.swap 0 i).injective (h.trans hqj.symm))
      have hqni : Equiv.swap 0 i c.succ ≠ i := by
        intro h
        exact Fin.succ_ne_zero c
          ((Equiv.swap 0 i).injective (h.trans (Equiv.swap_apply_left 0 i).symm))
      simp [witnessMatrix, Matrix.submatrix, Matrix.updateCol_apply,
        Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero c) hc,
        Function.update_of_ne hqne, hqni, anchor_matrix_entry]

theorem paper_pair_sign {d : ℕ} (i j : Fin (d + 1)) (hij : i < j) :
    (((Equiv.Perm.sign ((Equiv.swap 0 j).trans (Equiv.swap 0 i)) : ℤ) : ℝ)) =
      -((((Equiv.swap 0 i).sign : ℤ) : ℝ)) := by
  have hj0 : (0 : Fin (d + 1)) ≠ j := by
    intro h
    exact (not_lt_of_ge (Fin.zero_le i)) (h ▸ hij)
  simp [Equiv.Perm.sign_trans, Equiv.Perm.sign_swap hj0]

theorem paper_pair_witness {d : ℕ} (i j : Fin (d + 1)) (hij : i < j)
    (w : Fin (d + 1) → Fin d → ℝ) (x : Fin d → ℝ) :
    let z := iidWitnessTransport d (paperPairPermutation d i j) (w, x)
    oppositeWitness (liftedDeterminant z.1 z.2.1) (liftedDeterminant z.1 z.2.2) =
      oppositeWitness (replacementDeterminant w x i) (-replacementDeterminant w x j) := by
  dsimp only
  rw [paper_pair_transport d i j hij]
  dsimp only
  unfold liftedDeterminant
  rw [paper_pair_first_matrix i j hij, paper_pair_second_matrix i j hij,
    Matrix.det_permute', Matrix.det_permute', paper_pair_sign i j hij]
  rw [neg_mul, ← mul_neg, opposite_witness_mul, paper_sign_abs, one_mul]
  simpa only [neg_neg, replacementDeterminant] using
    opposite_witness_neg_neg (replacementDeterminant w x i) (-replacementDeterminant w x j)

def paperWitnessPermutation (d : ℕ) : PaperWitnessIndex d → Equiv.Perm (Fin (d + 2))
  | Sum.inl i => paperFirstPermutation d i
  | Sum.inr ij => paperPairPermutation d ij.val.1 ij.val.2

theorem paper_witness_index_nonempty (d : ℕ) : Nonempty (PaperWitnessIndex d) :=
  ⟨Sum.inl 0⟩

theorem paper_witness_transport_preserving {d : ℕ}
    (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν] (i : PaperWitnessIndex d) :
    MeasurePreserving (iidWitnessTransport d (paperWitnessPermutation d i))
      ((iidLaw ν (d + 1)).prod ν) ((iidLaw ν d).prod (ν.prod ν)) :=
  iid_witness_transport_preserving ν d (paperWitnessPermutation d i)

theorem paper_pair_replacement_symm {d : ℕ}
    (w : Fin (d + 1) → Fin d → ℝ) (x : Fin d → ℝ) (i j : Fin (d + 1)) :
    oppositeWitness (replacementDeterminant w x i) (-replacementDeterminant w x j) =
      oppositeWitness (replacementDeterminant w x j) (-replacementDeterminant w x i) := by
  unfold oppositeWitness
  simp [min_comm]

theorem determinant_assignment_witness_eq_paper_sum {d : ℕ}
    (w : Fin (d + 1) → Fin d → ℝ) (x : Fin d → ℝ) :
    determinantAssignmentWitness w x =
      ∑ i : PaperWitnessIndex d,
        let z := iidWitnessTransport d (paperWitnessPermutation d i) (w, x)
        oppositeWitness (liftedDeterminant z.1 z.2.1) (liftedDeterminant z.1 z.2.2) := by
  unfold determinantAssignmentWitness
  rw [symmetric_half_off_diagonal_sum _ (paper_pair_replacement_symm w x)]
  change _ = ∑ i : Sum (Fin (d + 1)) {ij : Fin (d + 1) × Fin (d + 1) // ij.1 < ij.2}, _
  rw [Fintype.sum_sum_type]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    exact (paper_first_witness i w x).symm
  · apply Finset.sum_congr rfl
    intro ij _
    exact (paper_pair_witness ij.val.1 ij.val.2 ij.property w x).symm

theorem integral_determinant_assignment_witness_eq_transportedWitnessSum {d : ℕ}
    (ν : Measure (Fin d → ℝ)) (w : Fin (d + 1) → Fin d → ℝ) :
    (∫ x, determinantAssignmentWitness w x ∂ν) =
      transportedWitnessSum ν (fun base x => liftedDeterminant base x)
        (fun i => iidWitnessTransport d (paperWitnessPermutation d i)) w := by
  unfold transportedWitnessSum
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (determinant_assignment_witness_eq_paper_sum w)

end Entry005
