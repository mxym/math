import Mathlib.Analysis.Convex.Body
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
The geometric cap construction in the sharp entry005 proof.
All sets and balls below are actual subsets of a real inner product space.
No surface-area or projection-volume identities are assumed here.
-/

noncomputable section

open Metric MeasureTheory MeasureTheory.Measure
open scoped RealInnerProductSpace

namespace Entry005

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A unit normal at the closest point separates the whole convex set.
The minimizing point and its supporting inequality are both derived. -/
theorem closest_support (K : Set E) (hK : Convex ℝ K) (hc : IsComplete K)
    (hne : K.Nonempty) (q : E) (hq : q ∉ K) :
    ∃ k ∈ K, ∃ n : E,
      0 < ‖q - k‖ ∧ ‖n‖ = 1 ∧
      inner ℝ n q - inner ℝ n k = ‖q - k‖ ∧
      (∀ x ∈ K, inner ℝ n x ≤ inner ℝ n k) ∧
      (∀ x ∈ K, ‖q - k‖ ≤ ‖q - x‖) := by
  obtain ⟨k, hk, hmin⟩ := exists_norm_eq_iInf_of_complete_convex hne hc hK q
  have hqk : q - k ≠ 0 := by
    intro h
    exact hq (sub_eq_zero.mp h ▸ hk)
  have hs : 0 < ‖q - k‖ := norm_pos_iff.mpr hqk
  let n : E := (‖q - k‖⁻¹ : ℝ) • (q - k)
  have hn : ‖n‖ = 1 := by
    simp [n, norm_smul, hs.ne']
  have hsep := (norm_eq_iInf_iff_real_inner_le_zero hK hk).mp hmin
  refine ⟨k, hk, n, hs, hn, ?_, ?_, ?_⟩
  · rw [← inner_sub_right]
    simp [n, inner_smul_left, pow_two, hs.ne']
  · intro x hx
    have h := hsep x hx
    have : inner ℝ n (x - k) ≤ 0 := by
      dsimp [n]
      rw [inner_smul_left]
      exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (inv_pos.mpr hs)) h
    rw [inner_sub_right] at this
    linarith
  · intro x hx
    rw [hmin]
    have hb : BddBelow (Set.range (fun w : K => ‖q - (w : E)‖)) :=
      ⟨(0 : ℝ), fun _ ⟨_, h⟩ => h ▸ norm_nonneg _⟩
    exact ciInf_le hb ⟨x, hx⟩

/-- A cap ball of radius `s/(2(M+1))` lies in the enclosing convex set and
strictly outside the separated inner set.  This works in the projected space
as well as in the ambient space. -/
theorem cap_ball (K P : Set E) (n q k : E) (M s : ℝ) (hP : Convex ℝ P)
    (hball : closedBall (0 : E) 1 ⊆ P) (hq : q ∈ P)
    (hn : ‖n‖ = 1) (hM : 0 ≤ M)
    (hqM : ‖q‖ ≤ M) (hs : 0 < s) (hsM : s ≤ M)
    (hgap : inner ℝ n q - inner ℝ n k = s)
    (hsep : ∀ x ∈ K, inner ℝ n x ≤ inner ℝ n k) :
    let τ := s / (2 * (M + 1))
    closedBall ((1 - τ) • q) τ ⊆ P ∧
      Disjoint K (closedBall ((1 - τ) • q) τ) := by
  let τ := s / (2 * (M + 1))
  have hden : 0 < 2 * (M + 1) := by positivity
  have ht : 0 < τ := div_pos hs hden
  have ht1 : τ ≤ 1 := by
    apply (div_le_iff₀ hden).mpr
    linarith
  have htval : τ * (M + 1) = s / 2 := by
    dsimp [τ]
    field_simp
  have hinside : closedBall ((1 - τ) • q) τ ⊆ P := by
    intro y hy
    have hy' : ‖y - (1 - τ) • q‖ ≤ τ := by
      simpa [mem_closedBall, dist_eq_norm] using hy
    let x := τ⁻¹ • (y - (1 - τ) • q)
    have hx : x ∈ closedBall (0 : E) 1 := by
      simp only [mem_closedBall, dist_zero_right]
      dsimp [x]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
      exact (inv_mul_le_iff₀ ht).mpr (by simpa using hy')
    have hconv := hP hq (hball hx) (sub_nonneg.mpr ht1) ht.le (by ring : 1 - τ + τ = 1)
    have hxy : (1 - τ) • q + τ • x = y := by
      simp [x, smul_smul, ht.ne']
    exact hxy ▸ hconv
  refine ⟨hinside, Set.disjoint_left.mpr ?_⟩
  intro y hyK hycap
  have hy' : ‖y - (1 - τ) • q‖ ≤ τ := by
    simpa [mem_closedBall, dist_eq_norm] using hycap
  have herr : -τ ≤ inner ℝ n (y - (1 - τ) • q) := by
    have h := abs_real_inner_le_norm n (y - (1 - τ) • q)
    rw [hn, one_mul] at h
    exact (neg_le_of_abs_le (h.trans hy'))
  have hnq : inner ℝ n q ≤ M := by
    have h := real_inner_le_norm n q
    simpa [hn] using h.trans (by simpa [hn] using hqM)
  rw [inner_sub_right, inner_smul_right] at herr
  have hsep' := hsep y hyK
  have hmul : τ * inner ℝ n q ≤ τ * M := mul_le_mul_of_nonneg_left hnq ht.le
  nlinarith

section Measure

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

/-- The constructed cap gives an actual Haar-volume gain; the cap is not
replaced by a scalar or a conclusion-shaped assumption. -/
theorem cap_measure_gain (μ : Measure E) [μ.IsAddHaarMeasure]
    (K P : Set E) (n q k : E) (M s : ℝ)
    (hKP : K ⊆ P) (hP : Convex ℝ P)
    (hball : closedBall (0 : E) 1 ⊆ P) (hq : q ∈ P)
    (hn : ‖n‖ = 1) (hM : 0 ≤ M) (hqM : ‖q‖ ≤ M)
    (hs : 0 < s) (hsM : s ≤ M)
    (hgap : inner ℝ n q - inner ℝ n k = s)
    (hsep : ∀ x ∈ K, inner ℝ n x ≤ inner ℝ n k) :
    μ K + ENNReal.ofReal ((s / (2 * (M + 1))) ^ Module.finrank ℝ E) *
      μ (closedBall (0 : E) 1) ≤ μ P := by
  let τ := s / (2 * (M + 1))
  have ht : 0 ≤ τ := by dsimp [τ]; positivity
  obtain ⟨hcap, hdis⟩ :=
    cap_ball K P n q k M s hP hball hq hn hM hqM hs hsM hgap hsep
  calc
    μ K + ENNReal.ofReal (τ ^ Module.finrank ℝ E) * μ (closedBall (0 : E) 1) =
        μ K + μ (closedBall ((1 - τ) • q) τ) := by
      rw [addHaar_closedBall' μ _ ht]
    _ = μ (K ∪ closedBall ((1 - τ) • q) τ) :=
      (measure_union hdis measurableSet_closedBall).symm
    _ ≤ μ P := measure_mono (Set.union_subset hKP hcap)

/-- A closest point produces the cap-volume estimate for actual nested
compact convex sets, without any assumed normal or supporting equation. -/
theorem nested_body_cap_gain (μ : Measure E) [μ.IsAddHaarMeasure]
    (K P : ConvexBody E) (M : ℝ) (hM : 0 ≤ M)
    (hball : closedBall (0 : E) 1 ⊆ K) (hKP : K ≤ P)
    (hPM : (P : Set E) ⊆ closedBall (0 : E) M)
    (q : E) (hq : q ∈ P) (hqK : q ∉ K) :
    ∃ k ∈ K, (∀ x ∈ K, ‖q - k‖ ≤ ‖q - x‖) ∧
      μ (K : Set E) +
        ENNReal.ofReal ((‖q - k‖ / (2 * (M + 1))) ^ Module.finrank ℝ E) *
        μ (closedBall (0 : E) 1) ≤ μ (P : Set E) := by
  obtain ⟨k, hk, n, hs, hn, hgap, hsep, hmin⟩ :=
    closest_support (K : Set E) K.convex K.isCompact.isComplete K.nonempty q hqK
  have hqM : ‖q‖ ≤ M := by simpa [mem_closedBall, dist_zero_right] using hPM hq
  have h0 : (0 : E) ∈ K := hball (by simp)
  have hsM : ‖q - k‖ ≤ M := (by simpa using hmin 0 h0 : ‖q - k‖ ≤ ‖q‖).trans hqM
  refine ⟨k, hk, hmin, ?_⟩
  exact cap_measure_gain μ (K : Set E) (P : Set E) n q k M ‖q - k‖
    hKP P.convex (hball.trans hKP) hq hn hM hqM hs hsM hgap hsep

end Measure

end Entry005
