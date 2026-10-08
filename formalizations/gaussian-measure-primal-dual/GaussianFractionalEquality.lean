import GaussianPrimalDual

/-! Equality in the actual Gaussian price dual forces deterministic winning
labels almost everywhere, for distinct score vectors. -/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace GaussianMeasureBridge

variable {d k : ℕ} [NeZero k]

theorem fractional_dual_equality_ae_winning (v : Fin k → Space d) (b : Fin k → ℝ)
    (hv : Function.Injective v) (G : FractionalPartition d k)
    (hEq : partitionValue v G = priceObjective v (fun i => G.mass i) b) :
    ∀ᵐ x ∂gaussian d, ∀ i, G.labels i x = (winningPartition v b hv).labels i x := by
  classical
  let weighted : Space d → ℝ := fun x => ∑ i, G.labels i x * (⟪v i, x⟫ - b i)
  let gap : Space d → ℝ := fun x => scoreMax v b x - weighted x
  have hintW : Integrable weighted (gaussian d) :=
    integrable_finsetSum _ (fun i _ => G.integrable_weighted_score i (v i) (b i))
  have hint : Integrable gap (gaussian d) := (integrable_scoreMax v b).sub hintW
  have hn : ∀ᵐ x ∂gaussian d, ∀ i, 0 ≤ G.labels i x := ae_all_iff.mpr G.nonneg
  have hnonneg : 0 ≤ᵐ[gaussian d] gap := by
    filter_upwards [hn, G.sum_one] with x hx hsum
    apply sub_nonneg.mpr
    change (∑ i, G.labels i x * (⟪v i, x⟫ - b i)) ≤ scoreMax v b x
    calc
      _ ≤ ∑ i, G.labels i x * scoreMax v b x := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (le_scoreMax v b x i) (hx i)
      _ = (∑ i, G.labels i x) * scoreMax v b x := (Finset.sum_mul ..).symm
      _ = scoreMax v b x := by rw [hsum, one_mul]
  have hevalW : (∫ x, weighted x ∂gaussian d) =
      partitionValue v G - ∑ i, G.mass i * b i := by
    dsimp [weighted]
    rw [integral_finsetSum Finset.univ
      (fun i _ => G.integrable_weighted_score i (v i) (b i))]
    simp_rw [G.integral_weighted_score]
    rw [Finset.sum_sub_distrib]
    rfl
  have hzero : (∫ x, gap x ∂gaussian d) = 0 := by
    dsimp [gap]
    rw [integral_sub (integrable_scoreMax v b) hintW, hevalW, hEq]
    unfold priceObjective expectedScore
    ring
  have hgapAE := (integral_eq_zero_iff_of_nonneg_ae hnonneg hint).mp hzero
  filter_upwards [hn, G.sum_one, hgapAE, ae_unique_winner v b hv] with x hx hsum hgap hw
  obtain ⟨r, hr⟩ := hw
  have hsgap : (∑ j, G.labels j x * (scoreMax v b x - (⟪v j, x⟫ - b j))) = 0 := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul]
    simpa only [gap, weighted, mul_sub, Pi.zero_apply] using hgap
  have hlabelzero : ∀ j, j ≠ r → G.labels j x = 0 := by
    intro j hj
    have hpos : 0 < scoreMax v b x - (⟪v j, x⟫ - b j) := by
      rw [scoreMax_eq_winning_score v b x r hr]
      exact sub_pos.mpr (hr j hj)
    have hle := Finset.single_le_sum
      (fun s _ => mul_nonneg (hx s) (sub_nonneg.mpr (le_scoreMax v b x s)))
      (Finset.mem_univ j)
    rw [hsgap] at hle
    have hnj : G.labels j x ≤ 0 := le_of_mul_le_mul_right (by simpa using hle) hpos
    exact le_antisymm hnj (hx j)
  have hrone : G.labels r x = 1 := by
    rw [Finset.sum_eq_single r (fun j _ hj => hlabelzero j hj) (by simp)] at hsum
    exact hsum
  intro i
  by_cases hi : i = r
  · subst i
    simp [winningPartition, hr, hrone]
  · have hnot : x ∉ winningCell v b i := by
      intro hxi
      have h1 := hr i hi
      have h2 := hxi r (Ne.symm hi)
      linarith
    simp [winningPartition, hnot, hlabelzero i hi]

end GaussianMeasureBridge
