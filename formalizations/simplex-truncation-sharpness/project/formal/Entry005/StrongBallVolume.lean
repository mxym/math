import Entry005.BallVolume

noncomputable section

open Metric MeasureTheory MeasureTheory.Measure
open scoped BigOperators

namespace Entry005

/-- The actual coordinate cube of half-side `1 / √m` lies in the Euclidean
unit ball, giving a sharper canonical-volume bound. -/
theorem euclidean_unit_ball_sqrt_cube (m : ℕ) (hm : 1 ≤ m) :
    ENNReal.ofReal ((2 / Real.sqrt (m : ℝ)) ^ m) ≤
      volume (closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hsqrt : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hmpos
  let a : ℝ := 1 / Real.sqrt (m : ℝ)
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
    have hbound : (m : ℝ) * a ^ 2 = 1 := by
      dsimp [a]
      rw [div_pow, one_pow, Real.sq_sqrt hmpos.le]
      field_simp
    have hnorm : ‖WithLp.toLp 2 x‖ ≤ (1 : ℝ) := by
      have hnormsq : ‖WithLp.toLp 2 x‖ ^ 2 ≤ (1 : ℝ) := by
        rw [EuclideanSpace.real_norm_sq_eq]
        exact hsum.trans_eq hbound
      nlinarith [norm_nonneg (WithLp.toLp 2 x)]
    simpa [mem_closedBall, dist_zero_right] using hnorm
  have hvol : volume C = ENNReal.ofReal ((2 / Real.sqrt (m : ℝ)) ^ m) := by
    rw [Real.volume_Icc_pi]
    simp only [sub_neg_eq_add, ← two_mul, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    rw [← ENNReal.ofReal_pow (by dsimp [a]; positivity)]
    congr 2
    dsimp [a]
    ring
  calc
    ENNReal.ofReal ((2 / Real.sqrt (m : ℝ)) ^ m) = volume C := hvol.symm
    _ ≤ volume ((WithLp.toLp 2) ⁻¹' closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) :=
      measure_mono hsubset
    _ = volume (closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) :=
      (PiLp.volume_preserving_toLp (Fin m)).measure_preimage measurableSet_closedBall.nullMeasurableSet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The sharp coordinate-cube lower bound on any finite-dimensional real
inner product space, transported through an actual orthonormal basis. -/
theorem unit_ball_sqrt_cube (hm : 1 ≤ Module.finrank ℝ E) :
    ENNReal.ofReal ((2 / Real.sqrt (Module.finrank ℝ E : ℝ)) ^ Module.finrank ℝ E) ≤
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
  exact euclidean_unit_ball_sqrt_cube (Module.finrank ℝ E) hm

end Entry005
