import SchurCompletion.CodimensionOneAsymptotic
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Order.PiLex

open scoped BigOperators Topology
open Matrix MeasureTheory Filter Asymptotics

namespace ExtractionSchur
open SymmetricSupport ExtractionSpectrum ExtractionRankSupport
noncomputable section

abbrev AvoidPattern (D k : ℕ) (pat : List (Fin D)) :=
  {w : Word D k // ¬ pat.Sublist (List.ofFn w)}

def avoidPatternCount (D k : ℕ) (pat : List (Fin D)) : ℕ :=
  Nat.card (AvoidPattern D k pat)

def avoidConsEquiv (D k : ℕ) (a : Fin D) (pat : List (Fin D)) :
    AvoidPattern D (k+1) (a::pat) ≃
      (AvoidPattern D k pat ⊕ ({b : Fin D // b ≠ a} × AvoidPattern D k (a::pat))) := by
  classical
  refine {
    toFun := fun w => if h : w.val 0 = a then
      Sum.inl ⟨fun i => w.val i.succ, ?_⟩ else
      Sum.inr (⟨w.val 0,h⟩, ⟨fun i => w.val i.succ, ?_⟩)
    invFun := fun x => match x with
      | Sum.inl w => ⟨Fin.cons a w.val, ?_⟩
      | Sum.inr x => ⟨Fin.cons x.1.val x.2.val, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro hh
    apply w.property
    rw [List.ofFn_succ, h]
    exact List.cons_sublist_cons.mpr hh
  · intro hh
    apply w.property
    rw [List.ofFn_succ]
    exact hh.cons _
  · simpa only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ,
      List.cons_sublist_cons] using w.property
  · simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ,
      List.cons_sublist_cons', Ne.symm x.1.property, false_and, or_false]
    exact x.2.property
  · intro w
    dsimp only
    split_ifs with h
    all_goals
      apply Subtype.ext
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [h]
      · simp
  · intro x
    cases x with
    | inl w =>
      simp only [Fin.cons_zero, ↓reduceDIte]
      congr 1
    | inr x =>
      simp only [Fin.cons_zero, x.1.property, ↓reduceDIte]
      congr 1

theorem avoidPatternCount_cons (D k : ℕ) (a : Fin D) (pat : List (Fin D)) :
    avoidPatternCount D (k+1) (a::pat) =
      avoidPatternCount D k pat + (D-1) * avoidPatternCount D k (a::pat) := by
  classical
  have hc : Nat.card {b : Fin D // b ≠ a} = D-1 := by
    rw [Nat.card_eq_fintype_card]
    simpa only [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype_eq]
  rw [avoidPatternCount, Nat.card_congr (avoidConsEquiv D k a pat), Nat.card_sum,
    Nat.card_prod, hc]
  rfl

theorem avoidPatternCount_nil (D k : ℕ) : avoidPatternCount D k [] = 0 := by
  classical
  unfold avoidPatternCount
  have h : IsEmpty (AvoidPattern D k []) := ⟨fun w => w.property (List.nil_sublist _)⟩
  letI := h
  simp

theorem avoidPatternCount_zero_cons (D : ℕ) (a : Fin D) (pat : List (Fin D)) :
    avoidPatternCount D 0 (a::pat) = 1 := by
  classical
  unfold avoidPatternCount
  have h (w : Word D 0) : ¬ (a::pat).Sublist (List.ofFn w) := by simp
  let e : AvoidPattern D 0 (a::pat) ≃ Word D 0 :=
    Equiv.subtypeUnivEquiv (fun w => h w)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  simp [Word]


def patternPolynomial (s k l : ℕ) : ℕ :=
  ∑ j ∈ Finset.range l, k.choose j * s^(k-j)

theorem patternPolynomial_succ (s k l : ℕ) :
    patternPolynomial s (k+1) (l+1) =
      patternPolynomial s k l + s * patternPolynomial s k (l+1) := by
  have he (j : ℕ) : k.choose (j+1) * s^(k-j) =
      s * (k.choose (j+1) * s^(k-(j+1))) := by
    by_cases hj : j < k
    · rw [show k-j = (k-(j+1))+1 by omega, pow_succ]
      ring
    · simp [Nat.choose_eq_zero_of_lt (by omega : k < j+1)]
  simp only [patternPolynomial, Finset.sum_range_succ', Nat.choose_zero_right,
    one_mul, Nat.sub_zero, Nat.choose_succ_succ, Nat.add_sub_add_right, Nat.add_mul]
  rw [Finset.sum_add_distrib]
  simp_rw [he]
  rw [← Finset.mul_sum, pow_succ]
  ring

theorem patternPolynomial_zero_succ (s l : ℕ) : patternPolynomial s 0 (l+1) = 1 := by
  simp [patternPolynomial, Finset.sum_range_succ']

/-- The number of words avoiding any one fixed subsequence pattern depends
only on its length, and has a finite binomial formula. -/
theorem avoidPatternCount_eq_patternPolynomial (D k : ℕ) (pat : List (Fin D)) :
    avoidPatternCount D k pat = patternPolynomial (D-1) k pat.length := by
  induction k generalizing pat with
  | zero =>
    cases pat with
    | nil => simp [avoidPatternCount_nil, patternPolynomial]
    | cons a pat => rw [avoidPatternCount_zero_cons, List.length_cons,
        patternPolynomial_zero_succ]
  | succ k ih =>
    cases pat with
    | nil => simp [avoidPatternCount_nil, patternPolynomial]
    | cons a pat =>
      rw [avoidPatternCount_cons, ih, ih, List.length_cons, patternPolynomial_succ]

end
end ExtractionSchur
