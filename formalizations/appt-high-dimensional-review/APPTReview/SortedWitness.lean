import APPTReview.EntropyHead
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Analysis.Matrix.PosDef

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

noncomputable def spectralLabel (ι : Type*) [Fintype ι] :
    Fin (Fintype.card ι) ≃ ι :=
  Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))

@[simp] theorem eigenvalues_spectralLabel {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (i : Fin (Fintype.card ι)) :
    hA.eigenvalues (spectralLabel ι i) = hA.eigenvalues₀ i := by
  simp [IsHermitian.eigenvalues, spectralLabel]

/-- Canonical placement: least, next-to-least, largest, third-to-least. -/
def rankTwoLabels {D : ℕ} (hD : 4 ≤ D) (p : Fin 2 × Fin 2) : Fin D :=
  if p.1 = 0 then
    if p.2 = 0 then ⟨D-1, by omega⟩ else ⟨D-2, by omega⟩
  else if p.2 = 0 then ⟨0, by omega⟩ else ⟨D-3, by omega⟩

theorem rankTwoLabels_injective {D : ℕ} (hD : 4 ≤ D) :
    Function.Injective (rankTwoLabels hD) := by
  intro ⟨i,j⟩ ⟨k,l⟩ h
  have hv := congrArg Fin.val h
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [rankTwoLabels] at hv ⊢ <;> omega

/-- The sorted rank-two witness for an actual APPT matrix, with the eigenvalue
permutation constructed in the proof rather than supplied as a hypothesis. -/
theorem appt_sorted_rankTwo_witness {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n)
    {A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ}
    (hA : A.IsHermitian) (h : APPT.Quantum.AbsolutelyPPT A) :
    (witnessMatrix (fun p : Fin 2 × Fin 2 =>
      hA.eigenvalues₀ (rankTwoLabels
        (show 4 ≤ Fintype.card (Fin m × Fin n) by
          simp only [Fintype.card_prod, Fintype.card_fin]; nlinarith) p))).PosSemidef := by
  classical
  have hD : 4 ≤ Fintype.card (Fin m × Fin n) := by
    simp only [Fintype.card_prod, Fintype.card_fin]; nlinarith
  let i : Fin 2 → Fin m := Fin.castLE hm
  let e : Fin m → Fin n := Fin.castLE hmn
  have hi : Function.Injective i := by
    intro a b hab
    exact Fin.ext (congrArg (fun z : Fin m => z.val) hab)
  have he : Function.Injective e := by
    intro a b hab
    exact Fin.ext (congrArg (fun z : Fin n => z.val) hab)
  let f : Fin 2 × Fin 2 → Fin m × Fin n := fun p => (i p.1,e (i p.2))
  have hf : Function.Injective f := by
    intro a b hab
    exact Prod.ext (hi (congrArg Prod.fst hab))
      (hi (he (congrArg Prod.snd hab)))
  let g : Fin 2 × Fin 2 → Fin m × Fin n :=
    fun p => spectralLabel _ (rankTwoLabels hD p)
  have hg : Function.Injective g :=
    (spectralLabel _).injective.comp (rankTwoLabels_injective hD)
  obtain ⟨σ,hσ⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  have hM := (appt_eigenvalue_witness_posSemidef hA h σ e he).submatrix i
  have hw (a b : Fin 2) : hA.eigenvalues (σ (i a,e (i b))) =
      hA.eigenvalues₀ (rankTwoLabels hD (a,b)) := by
    change hA.eigenvalues (σ (f (a,b))) = _
    rw [hσ]
    exact eigenvalues_spectralLabel hA _
  convert hM using 1
  ext a b
  have heq : i a = i b ↔ a = b := hi.eq_iff
  have hlt : i a < i b ↔ a < b := Iff.rfl
  simp only [Matrix.submatrix, Matrix.of_apply, witnessMatrix, heq, hlt, hw]

/-- The genuine sorted eigenvalue determinant condition; all placement
obligations have been discharged by the preceding theorem. -/
theorem appt_sorted_rankTwo_determinant {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n)
    {A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ}
    (hA : A.IsHermitian) (h : APPT.Quantum.AbsolutelyPPT A)
    (hD : 4 ≤ Fintype.card (Fin m × Fin n)) :
    (hA.eigenvalues₀ (rankTwoLabels hD (1,0)) -
      hA.eigenvalues₀ (rankTwoLabels hD (0,1)))^2 ≤
    4*hA.eigenvalues₀ (rankTwoLabels hD (0,0))*
      hA.eigenvalues₀ (rankTwoLabels hD (1,1)) := by
  have hM := appt_sorted_rankTwo_witness hm hmn hA h
  have hd := hM.det_nonneg
  simp only [Matrix.det_fin_two, witnessMatrix] at hd
  norm_num at hd
  nlinarith

end APPTReview
