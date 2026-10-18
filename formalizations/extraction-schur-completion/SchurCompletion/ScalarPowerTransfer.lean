import SchurCompletion.MinorMomentAsymptotic
import SchurCompletion.DeterminantTrace

open scoped BigOperators Topology
open Matrix MeasureTheory Filter Asymptotics

namespace ExtractionSchur
noncomputable section

def affineStep (s : ℕ) (x : ℝ) : ℝ := ((s : ℝ)-1+x)/(s : ℝ)

def powerCutoff (N : ℕ) : ℝ := 1 - 1/(2*((N : ℝ)+1)^2)

theorem one_sub_nat_mul_one_sub_le_pow (b : ℕ) (y : ℝ) (hy0 : 0 ≤ y) :
    1-(b : ℝ)*(1-y) ≤ y^b := by
  induction b with
  | zero => simp
  | succ b ih =>
    have h := mul_le_mul_of_nonneg_right ih hy0
    rw [pow_succ, Nat.cast_add, Nat.cast_one]
    nlinarith [mul_nonneg (Nat.cast_nonneg b) (sq_nonneg (1-y))]

theorem powerCutoff_bounds (N : ℕ) : 0 < powerCutoff N ∧ powerCutoff N < 1 := by
  have hm : (1 : ℝ) ≤ (N : ℝ)+1 := by exact le_add_of_nonneg_left (Nat.cast_nonneg N)
  have hd : (0 : ℝ) < 2*((N : ℝ)+1)^2 := by positivity
  constructor
  · unfold powerCutoff
    have he : 1/(2*((N : ℝ)+1)^2) ≤ 1/2 := by
      apply one_div_le_one_div_of_le (by norm_num)
      nlinarith
    linarith
  · unfold powerCutoff
    have hp : 0 < 1/(2*((N : ℝ)+1)^2) := by positivity
    linarith

theorem affineStep_bounds (s : ℕ) (hs : 0 < s) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ affineStep s x ∧ affineStep s x ≤ 1 := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast (by omega : 1 ≤ s)
  unfold affineStep
  constructor
  · exact div_nonneg (by linarith) hsR.le
  · exact (div_le_one hsR).mpr (by linarith)

/-- A deterministic integer-power comparison near one. Its exponent ratio
approaches 1/s as N grows, avoiding any assumed concentration theorem. -/
theorem affineStep_power_near_one (s N : ℕ) (hs : 0 < s) (Npos : 0 < N)
    (x : ℝ) (hx : powerCutoff N ≤ x) (hx1 : x ≤ 1) :
    affineStep s x ^ (s*(N+1)) ≤ x^N := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hx0 : 0 ≤ x := (powerCutoff_bounds N).1.le.trans hx
  let y := affineStep s x
  have hy := affineStep_bounds s hs x hx0 hx1
  have hsy : (s : ℝ)*(1-y) = 1-x := by dsimp [y, affineStep]; field_simp; ring
  have hb := one_sub_nat_mul_one_sub_le_pow (s*(N+1)) y hy.1
  have hb' : 1-((N : ℝ)+1)*(1-x) ≤ y^(s*(N+1)) := by
    have he : ((s*(N+1) : ℕ) : ℝ)*(1-y) = ((N : ℝ)+1)*(1-x) := by
      push_cast
      nlinarith [congrArg (fun z : ℝ => z*((N : ℝ)+1)) hsy]
    rwa [he] at hb
  have hsmall : 2*((N : ℝ)+1)^2*(1-x) ≤ 1 := by
    have hd : 0 < 2*((N : ℝ)+1)^2 := by positivity
    rw [mul_comm (2*((N : ℝ)+1)^2) (1-x)]
    apply (le_div_iff₀ hd).mp
    dsimp [powerCutoff] at hx
    linarith
  have hmul : (N : ℝ) ≤ ((N : ℝ)+1)*y^(s*(N+1)) := by
    have h := mul_le_mul_of_nonneg_left hb' (by positivity : 0 ≤ (N : ℝ)+1)
    nlinarith
  have hsum : (s : ℝ)*(N : ℝ) ≤ ∑ j ∈ Finset.range (s*(N+1)), y^j := by
    calc
      _ ≤ (s : ℝ)*(((N : ℝ)+1)*y^(s*(N+1))) := mul_le_mul_of_nonneg_left hmul hsR.le
      _ = ∑ j ∈ Finset.range (s*(N+1)), y^(s*(N+1)) := by simp; ring
      _ ≤ _ := Finset.sum_le_sum (fun j hj =>
        pow_le_pow_of_le_one hy.1 hy.2 (Nat.le_of_lt (Finset.mem_range.mp hj)))
  have hxsum : (∑ j ∈ Finset.range N, x^j) ≤ (N : ℝ) := by
    calc
      _ ≤ ∑ j ∈ Finset.range N, (1 : ℝ) :=
        Finset.sum_le_sum (fun j hj => pow_le_one₀ hx0 hx1)
      _ = _ := by simp
  have hY := geom_sum_mul_neg y (s*(N+1))
  have hX := geom_sum_mul_neg x N
  have hlow := mul_le_mul_of_nonneg_right hsum (sub_nonneg.mpr hy.2)
  have hhigh := mul_le_mul_of_nonneg_right hxsum (sub_nonneg.mpr hx1)
  have hsN := congrArg (fun z : ℝ => z*(N : ℝ)) hsy
  change y^(s*(N+1)) ≤ x^N
  nlinarith

theorem affineStep_power_global (s N k : ℕ) (hs : 0 < s) (Npos : 0 < N)
    (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    affineStep s x ^ k ≤ x^(N*(k/(s*(N+1)))) +
      affineStep s (powerCutoff N) ^ ((s*(N+1))*(k/(s*(N+1)))) := by
  have hy := affineStep_bounds s hs x hx0 hx1
  have hr := affineStep_bounds s hs (powerCutoff N) (powerCutoff_bounds N).1.le
    (powerCutoff_bounds N).2.le
  have hfirst : affineStep s x ^ k ≤ affineStep s x ^ ((s*(N+1))*(k/(s*(N+1)))) :=
    pow_le_pow_of_le_one hy.1 hy.2 (Nat.mul_div_le k (s*(N+1)))
  apply hfirst.trans
  by_cases hnear : powerCutoff N ≤ x
  · have h := affineStep_power_near_one s N hs Npos x hnear hx1
    have hp : affineStep s x ^ ((s*(N+1))*(k/(s*(N+1)))) ≤
        x^(N*(k/(s*(N+1)))) := by
      have hp := pow_le_pow_left₀ (pow_nonneg hy.1 _) h (k/(s*(N+1)))
      simpa only [← pow_mul] using hp
    exact hp.trans (le_add_of_nonneg_right (pow_nonneg hr.1 _))
  · have hle : affineStep s x ≤ affineStep s (powerCutoff N) := by
      apply div_le_div_of_nonneg_right _ (by exact_mod_cast (Nat.zero_le s))
      linarith
    have hp : affineStep s x ^ ((s*(N+1))*(k/(s*(N+1)))) ≤
        affineStep s (powerCutoff N) ^ ((s*(N+1))*(k/(s*(N+1)))) :=
      pow_le_pow_left₀ hy.1 hle _
    exact hp.trans (le_add_of_nonneg_left (pow_nonneg hx0 _))

end
end ExtractionSchur
