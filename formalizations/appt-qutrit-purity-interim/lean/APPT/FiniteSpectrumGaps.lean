import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Basic.Real.Basic

open scoped BigOperators

namespace APPT.FiniteSpectrum

/-- Adjacent differences of a finite spectrum, with the last value as the last gap. -/
noncomputable def gaps {d : ℕ} (y : Fin (d + 1) → ℝ) : Fin (d + 1) → ℝ :=
  Fin.lastCases (y (Fin.last d)) (fun i : Fin d => y i.castSucc - y i.succ)

/-- Recover a spectrum entry as the sum of the gaps at and after that index. -/
noncomputable def tailSum {D : ℕ} (g : Fin D → ℝ) (i : Fin D) : ℝ :=
  ∑ j : Fin D, if i ≤ j then g j else 0

theorem gaps_nonneg {d : ℕ} (y : Fin (d + 1) → ℝ)
    (horder : Antitone y) (hpos : ∀ i, 0 ≤ y i) : ∀ i, 0 ≤ gaps y i := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa [gaps] using hpos (Fin.last d)
  · have hj : j.castSucc ≤ j.succ := by
      change j.val ≤ j.val + 1
      omega
    simpa [gaps] using sub_nonneg.mpr (horder hj)

theorem tailSum_last {d : ℕ} (g : Fin (d + 1) → ℝ) :
    tailSum g (Fin.last d) = g (Fin.last d) := by
  classical
  unfold tailSum
  rw [Finset.sum_eq_single (Fin.last d)]
  · simp
  · intro j _ hne
    have hnot : ¬ Fin.last d ≤ j := by
      intro h
      exact hne (le_antisymm j.le_last h)
    simp [hnot]
  · simp

theorem tailSum_castSucc {d : ℕ} (g : Fin (d + 1) → ℝ) (i : Fin d) :
    tailSum g i.castSucc = g i.castSucc + tailSum g i.succ := by
  classical
  calc
    tailSum g i.castSucc =
        ∑ j : Fin (d + 1),
          ((if j = i.castSucc then g j else 0) + (if i.succ ≤ j then g j else 0)) := by
      unfold tailSum
      apply Finset.sum_congr rfl
      intro j _
      by_cases he : j = i.castSucc
      · subst j
        have hs : ¬ i.succ ≤ i.castSucc := by
          change ¬ i.val + 1 ≤ i.val
          omega
        simp [hs]
      · by_cases hi : i.castSucc ≤ j
        · have hv : j.val ≠ i.val := by
            intro hv
            apply he
            exact Fin.ext hv
          have hs : i.succ ≤ j := by
            change i.val + 1 ≤ j.val
            change i.val ≤ j.val at hi
            omega
          simp [he, hi, hs]
        · have hs : ¬ i.succ ≤ j := by
            change ¬ i.val + 1 ≤ j.val
            change ¬ i.val ≤ j.val at hi
            omega
          simp [he, hi, hs]
    _ = g i.castSucc + tailSum g i.succ := by
      simp [Finset.sum_add_distrib, tailSum]

/-- The inverse gap transform is exact, without any order or positivity hypothesis. -/
theorem tailSum_gaps {d : ℕ} (y : Fin (d + 1) → ℝ) (i : Fin (d + 1)) :
    tailSum (gaps y) i = y i := by
  induction i using Fin.reverseInduction with
  | last => simp [tailSum_last, gaps]
  | cast i ih =>
    rw [tailSum_castSucc, ih]
    simp [gaps]

end APPT.FiniteSpectrum
