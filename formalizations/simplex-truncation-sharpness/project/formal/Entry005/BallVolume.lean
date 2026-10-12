import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section

open Metric MeasureTheory MeasureTheory.Measure
open scoped BigOperators

namespace Entry005

/-- The very coarse cube bound used in the written proof.  Both sides are
actual Euclidean volumes; the cube is proved to lie in the unit ball. -/
theorem euclidean_unit_ball_cube (m : ℕ) (hm : 1 ≤ m) :
    ENNReal.ofReal ((2 / (m : ℝ)) ^ m) ≤
      volume (closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hmone : (1 : ℝ) ≤ m := by exact_mod_cast hm
  let a : ℝ := 1 / (m : ℝ)
  let C : Set (Fin m → ℝ) := Set.Icc (fun _ => -a) (fun _ => a)
  have hsubset : C ⊆ (WithLp.toLp 2) ⁻¹' closedBall (0 : EuclideanSpace ℝ (Fin m)) 1 := by
    intro x hx
    have hxabs (i : Fin m) : |x i| ≤ a := abs_le.mpr ⟨hx.1 i, hx.2 i⟩
    have hxsq (i : Fin m) : x i ^ 2 ≤ a ^ 2 := by
      have h := mul_self_le_mul_self (abs_nonneg (x i)) (hxabs i)
      simpa [sq_abs, pow_two] using h
    have hsum : ∑ i : Fin m, x i ^ 2 ≤ (m : ℝ) * a ^ 2 := by
      calc
        ∑ i : Fin m, x i ^ 2 ≤ ∑ _i : Fin m, a ^ 2 := Finset.sum_le_sum (fun i _ => hxsq i)
        _ = (m : ℝ) * a ^ 2 := by simp
    have hbound : (m : ℝ) * a ^ 2 ≤ 1 := by
      dsimp [a]
      have hinv : 1 / (m : ℝ) ≤ 1 := (div_le_one hmpos).mpr hmone
      convert hinv using 1
      field_simp
    have hnorm : ‖WithLp.toLp 2 x‖ ≤ (1 : ℝ) := by
      have hnormsq : ‖WithLp.toLp 2 x‖ ^ 2 ≤ (1 : ℝ) := by
        rw [EuclideanSpace.real_norm_sq_eq]
        exact hsum.trans hbound
      nlinarith [norm_nonneg (WithLp.toLp 2 x)]
    simpa [mem_closedBall, dist_zero_right] using hnorm
  have hvol : volume C = ENNReal.ofReal ((2 / (m : ℝ)) ^ m) := by
    rw [Real.volume_Icc_pi]
    simp only [sub_neg_eq_add, ← two_mul, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    rw [← ENNReal.ofReal_pow (by dsimp [a]; positivity)]
    congr 2
    dsimp [a]
    ring
  calc
    ENNReal.ofReal ((2 / (m : ℝ)) ^ m) = volume C := hvol.symm
    _ ≤ volume ((WithLp.toLp 2) ⁻¹' closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) :=
      measure_mono hsubset
    _ = volume (closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) :=
      (PiLp.volume_preserving_toLp (Fin m)).measure_preimage measurableSet_closedBall.nullMeasurableSet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The same bound on any finite-dimensional real inner product space,
with the canonical volume normalization. -/
theorem unit_ball_cube (hm : 1 ≤ Module.finrank ℝ E) :
    ENNReal.ofReal ((2 / (Module.finrank ℝ E : ℝ)) ^ Module.finrank ℝ E) ≤
      volume (closedBall (0 : E) 1) := by
  let b := stdOrthonormalBasis ℝ E
  have hpre : b.repr ⁻¹' closedBall (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 1 =
      closedBall (0 : E) 1 := by
    ext x
    simp [mem_closedBall, dist_zero_right]
  have heq := b.measurePreserving_repr.measure_preimage
    (s := closedBall (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 1)
    measurableSet_closedBall.nullMeasurableSet
  rw [hpre] at heq
  rw [heq]
  exact euclidean_unit_ball_cube (Module.finrank ℝ E) hm

end Entry005
