import ErdosSimilarityGrowingGaps.AnnulusSequence
import ErdosSimilarityGrowingGaps.PowerCore
import ErdosSimilarityGrowingGaps.GridGeometry
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Thickening

namespace ErdosSimilarityGrowingGaps

open Set

/-- A filled annulus supplies an actual input whose logarithmic coordinate lies
in the requested interval.  The two-sided input bounds retain the full
half-open endpoint convention of `FillsAnnulus`. -/
theorem FillsAnnulus.sample_input_bounds
    {Z : LogScale} {U R D v : ℝ}
    (h : FillsAnnulus Z U R D)
    (hv : U / R ≤ v) (hvD : v + D ≤ R * U) :
    ∃ n : ℕ,
      (2 : ℝ) ^ (-(v + D)) ≤ input Z n ∧
      input Z n ≤ (2 : ℝ) ^ (-v) := by
  obtain ⟨n, hnlo, hnhi⟩ := h.sample_mem hv hvD
  refine ⟨n, ?_, ?_⟩
  · unfold input
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  · unfold input
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith

/-- Raising the sampled input to a positive exponent preserves the annular
sandwich.  This is the quantitative bridge used by the finite-window route. -/
theorem FillsAnnulus.sample_power_bounds
    {Z : LogScale} {U R D v s : ℝ}
    (h : FillsAnnulus Z U R D)
    (hv : U / R ≤ v) (hvD : v + D ≤ R * U) (hs : 0 < s) :
    ∃ n : ℕ,
      (2 : ℝ) ^ (-(v + D) * s) ≤ (input Z n) ^ s ∧
      (input Z n) ^ s ≤ (2 : ℝ) ^ (-v * s) := by
  obtain ⟨n, hlow, hupp⟩ := h.sample_input_bounds hv hvD
  refine ⟨n, ?_, ?_⟩
  · calc
      (2 : ℝ) ^ (-(v + D) * s) = ((2 : ℝ) ^ (-(v + D))) ^ s :=
        Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) _ _
      _ ≤ (input Z n) ^ s := Real.rpow_le_rpow (by positivity) hlow hs.le
  · calc
      (input Z n) ^ s ≤ ((2 : ℝ) ^ (-v)) ^ s :=
        Real.rpow_le_rpow (input_pos Z n).le hupp hs.le
      _ = (2 : ℝ) ^ (-v * s) := (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) _ _).symm

/-- A sampled power differs from the left endpoint power by at most the full
annular power width.  The statement is sign-robust and is the exact error
buffer needed before enlarging an open grid blocker. -/
theorem FillsAnnulus.sample_power_error
    {Z : LogScale} {U R D v s c : ℝ}
    (h : FillsAnnulus Z U R D)
    (hv : U / R ≤ v) (hvD : v + D ≤ R * U) (hs : 0 < s) :
    ∃ n : ℕ,
      |c * (input Z n) ^ s - c * (2 : ℝ) ^ (-v * s)| ≤
        |c| * ((2 : ℝ) ^ (-v * s) - (2 : ℝ) ^ (-(v + D) * s)) := by
  obtain ⟨n, hlow, hupp⟩ := h.sample_power_bounds hv hvD hs
  refine ⟨n, ?_⟩
  have hwidth : 0 ≤ (2 : ℝ) ^ (-v * s) - (2 : ℝ) ^ (-(v + D) * s) := by
    apply sub_nonneg.mpr
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hD : 0 ≤ D := le_trans (by norm_num) (h.2.2.1)
    nlinarith [mul_nonneg hs.le hD]
  have habs : |(input Z n) ^ s - (2 : ℝ) ^ (-v * s)| ≤
      (2 : ℝ) ^ (-v * s) - (2 : ℝ) ^ (-(v + D) * s) := by
    rw [abs_le]
    constructor <;> linarith
  rw [show c * (input Z n) ^ s - c * (2 : ℝ) ^ (-v * s) =
      c * ((input Z n) ^ s - (2 : ℝ) ^ (-v * s)) by ring, abs_mul]
  exact (mul_le_mul_of_nonneg_left habs (abs_nonneg c))


/-- The deterministic perturbation estimate turns an ideal power hit into an
actual sampled hit after the annular width and tail remainder fit inside an
open buffer.  This is the local interface between the logarithmic sampler and
an individual finite blocker. -/
theorem sampled_output_mem_thickening
    {Z : LogScale} {f : ℝ → ℝ} {B : Set ℝ} {n : ℕ}
    {s α y c M v D r : ℝ}
    (hs : 0 < s) (hα : 0 < α) (hM : 0 ≤ M)
    (happrox : |f (input Z n) - y - c * (input Z n) ^ s| ≤
      M * (input Z n) ^ (s + α))
    (hideal : y + c * (2 : ℝ) ^ (-v * s) ∈ B)
    (hpower : |c * (input Z n) ^ s - c * (2 : ℝ) ^ (-v * s)| ≤
      |c| * ((2 : ℝ) ^ (-v * s) - (2 : ℝ) ^ (-(v + D) * s)))
    (hwidth : |c| * ((2 : ℝ) ^ (-v * s) - (2 : ℝ) ^ (-(v + D) * s)) +
        M * (input Z n) ^ (s + α) < r) :
    f (input Z n) ∈ Metric.thickening r B := by
  apply Metric.mem_thickening_iff.2
  refine ⟨y + c * (2 : ℝ) ^ (-v * s), hideal, ?_⟩
  have hpow : 0 ≤ (input Z n) ^ s := Real.rpow_nonneg (input_pos Z n).le _
  have hαpow : 0 ≤ (input Z n) ^ (s + α) :=
    Real.rpow_nonneg (input_pos Z n).le _
  have htri := abs_add_le
    (f (input Z n) - y - c * (input Z n) ^ s)
    (c * (input Z n) ^ s - c * (2 : ℝ) ^ (-v * s))
  have hsample := hpower
  have habs : |f (input Z n) - (y + c * (2 : ℝ) ^ (-v * s))| ≤
      M * (input Z n) ^ (s + α) +
        |c| * ((2 : ℝ) ^ (-v * s) - (2 : ℝ) ^ (-(v + D) * s)) := by
    calc
      _ = |(f (input Z n) - y - c * (input Z n) ^ s) +
          (c * (input Z n) ^ s - c * (2 : ℝ) ^ (-v * s))| := by congr 1 <;> ring
      _ ≤ _ := htri.trans (add_le_add happrox hsample)
      _ = _ := by ring
  rw [Real.dist_eq]
  exact habs.trans_lt (by simpa [add_comm] using hwidth)

/-!  The preceding estimate in the coordinates used by the routing tree. -/
theorem FillsAnnulus.sample_powerPoint_error
    {Z : LogScale} {K : ℕ} {x : ℝ} {p : PowerParams (1 / (K : ℝ)) K}
    {U R D v C : ℝ}
    (hK : 2 ≤ K)
    (h : FillsAnnulus Z U R D)
    (hv : U / R ≤ v) (hvD : v + D ≤ R * U)
    (hC : 0 ≤ C) :
    ∃ n : ℕ,
      |powerPoint (input Z n) C (x, p) -
        powerPoint ((2 : ℝ) ^ (-v)) C (x, p)| ≤
        |p.2.1 * C| * ((2 : ℝ) ^ (-v * p.1.1) -
          (2 : ℝ) ^ (-(v + D) * p.1.1)) := by
  have hs : 0 < p.1.1 := lt_of_lt_of_le (by
    have hKr : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
    positivity) p.1.2.1
  obtain ⟨n, hn⟩ := h.sample_power_error (c := p.2.1 * C) hv hvD hs
  refine ⟨n, ?_⟩
  have hpow : (2 : ℝ) ^ (-v * p.1.1) =
      ((2 : ℝ) ^ (-v)) ^ p.1.1 :=
    Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) _ _
  calc
    |powerPoint (input Z n) C (x, p) -
        powerPoint ((2 : ℝ) ^ (-v)) C (x, p)| =
      |p.2.1 * C * (input Z n) ^ p.1.1 -
        p.2.1 * C * ((2 : ℝ) ^ (-v)) ^ p.1.1| := by
          simp only [powerPoint]
          ring_nf
    _ = |p.2.1 * C * (input Z n) ^ p.1.1 -
        p.2.1 * C * (2 : ℝ) ^ (-v * p.1.1)| := by rw [hpow]
    _ ≤ _ := hn

theorem gridAddress_eq_of_common_stable_interval
    (b : ℕ) (x R z z' : ℝ) (hstable :
      NoGridBoundary (2 ^ (b + 3)) x R)
    (hz : x ≤ z ∧ z ≤ x + R) (hz' : x ≤ z' ∧ z' ≤ x + R) :
    gridAddress b z = gridAddress b z' := by
  apply (gridAddress_eq_iff b z z').2
  rw [periodicGridKey_eq_of_no_boundary _ (pow_pos (by decide) _) x R z hz hstable,
    periodicGridKey_eq_of_no_boundary _ (pow_pos (by decide) _) x R z' hz' hstable]

theorem FillsAnnulus.sample_powerPoint_stable_key
    {Z : LogScale} {K : ℕ} {x : ℝ} {p : PowerParams (1 / (K : ℝ)) K}
    {U R D v C : ℝ} {b : ℕ}
    (hK : 2 ≤ K)
    (h : FillsAnnulus Z U R D)
    (hv : U / R ≤ v) (hvD : v + D ≤ R * U)
    (hC : 0 ≤ C)
    (hstable : NoGridBoundary (2 ^ (b + 3)) x R)
    (hideal : x ≤ powerPoint ((2 : ℝ) ^ (-v)) C (x, p) ∧
      powerPoint ((2 : ℝ) ^ (-v)) C (x, p) ≤ x + R) :
    ∃ n : ℕ,
      gridAddress b (powerPoint (input Z n) C (x, p)) =
        gridAddress b (powerPoint ((2 : ℝ) ^ (-v)) C (x, p)) := by
  have hs : 0 < p.1.1 := lt_of_lt_of_le (by
    have hKr : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
    positivity) p.1.2.1
  obtain ⟨n, hlo, hhi⟩ := h.sample_power_bounds hv hvD hs
  have hinput : 0 < input Z n := input_pos Z n
  have hcoef : 0 ≤ p.2.1 * C :=
    mul_nonneg (by linarith [p.2.2.1]) hC
  have hactual : x ≤ powerPoint (input Z n) C (x, p) := by
    simp only [powerPoint]
    have hpow : 0 ≤ (input Z n) ^ p.1.1 := Real.rpow_nonneg hinput.le _
    nlinarith
  have hupper : powerPoint (input Z n) C (x, p) ≤
      powerPoint ((2 : ℝ) ^ (-v)) C (x, p) := by
    have hpow' : (2 : ℝ) ^ (-v * p.1.1) =
        ((2 : ℝ) ^ (-v)) ^ p.1.1 :=
      Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) _ _
    calc
      powerPoint (input Z n) C (x, p) =
          x + (p.2.1 * C) * (input Z n) ^ p.1.1 := by simp [powerPoint]
      _ ≤ x + (p.2.1 * C) * ((2 : ℝ) ^ (-v)) ^ p.1.1 :=
        by rw [← hpow']; simpa [add_comm] using
          (add_le_add_left (mul_le_mul_of_nonneg_left hhi hcoef) x)
      _ = powerPoint ((2 : ℝ) ^ (-v)) C (x, p) := by
        simp [powerPoint, hpow']
  exact ⟨n, gridAddress_eq_of_common_stable_interval b x R _ _ hstable
    ⟨hactual, hupper.trans hideal.2⟩ hideal⟩

theorem FillsAnnulus.sample_powerPoint_mem_thickening
    {Z : LogScale} {K : ℕ} {x : ℝ} {p : PowerParams (1 / (K : ℝ)) K}
    {U R D v C r : ℝ} (hK : 2 ≤ K)
    (h : FillsAnnulus Z U R D)
    (hv : U / R ≤ v) (hvD : v + D ≤ R * U) (hC : 0 ≤ C)
    {G : Set ℝ}
    (hideal : powerPoint ((2 : ℝ) ^ (-v)) C (x, p) ∈ G)
    (hwidth : |p.2.1 * C| * ((2 : ℝ) ^ (-v * p.1.1) -
      (2 : ℝ) ^ (-(v + D) * p.1.1)) < r) :
    ∃ n : ℕ,
      powerPoint (input Z n) C (x, p) ∈ Metric.thickening r G := by
  obtain ⟨n, hn⟩ := h.sample_powerPoint_error hK hv hvD hC
  refine ⟨n, Metric.mem_thickening_iff.2 ⟨
    powerPoint ((2 : ℝ) ^ (-v)) C (x, p), hideal, ?_⟩⟩
  rw [Real.dist_eq]
  exact hn.trans_lt hwidth

end ErdosSimilarityGrowingGaps
