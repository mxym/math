import SymmetricSupport.RankAsymptotic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace ExtractionRankSupport

open SymmetricSupport

/-- A direct explicit polynomial bound for the actual symmetric support. This
new child module leaves all sources and roots of the parent pure audit fixed. -/
theorem symmetricProjector_rank_le_explicit_polynomial (E k : ℕ) (hE : 0 < E) :
    (symmetricProjector E k).rank ≤ E ^ (E-1) * (k+1) ^ (E-1) := by
  rw [symmetricProjector_rank_choose_complement E k hE]
  have hkle : k ≤ E*k := by nlinarith
  have hbase : k+E-1 ≤ E*(k+1) := by
    calc
      k+E-1 ≤ k+E := Nat.sub_le _ _
      _ ≤ E*k+E := Nat.add_le_add_right hkle _
      _ = _ := by ring
  calc
    _ ≤ (k+E-1) ^ (E-1) := Nat.choose_le_pow _ _
    _ ≤ (E*(k+1)) ^ (E-1) := Nat.pow_le_pow_left hbase _
    _ = _ := Nat.mul_pow _ _ _

theorem shifted_choose_le_explicit_polynomial (E k : ℕ) (hE : 0 < E) :
    (E+k-1).choose k ≤ E ^ (E-1) * (k+1) ^ (E-1) := by
  rw [← symmetricProjector_rank_choose E k]
  exact symmetricProjector_rank_le_explicit_polynomial E k hE

theorem symmetricProjector_log_rank_le_explicit (E k : ℕ) (hE : 0 < E) :
    Real.log ((symmetricProjector E k).rank : ℝ) ≤
      ((E-1 : ℕ) : ℝ) * Real.log (E : ℝ) +
        ((E-1 : ℕ) : ℝ) * Real.log (k+1 : ℝ) := by
  have hE0 : (0 : ℝ) < E := by exact_mod_cast hE
  have hkp : (0 : ℝ) < (k : ℝ)+1 := by positivity
  have hr : (0 : ℝ) < (symmetricProjector E k).rank := by
    exact_mod_cast symmetricProjector_rank_pos E k hE
  have hu : ((symmetricProjector E k).rank : ℝ) ≤
      (E : ℝ) ^ (E-1) * ((k : ℝ)+1) ^ (E-1) := by
    exact_mod_cast symmetricProjector_rank_le_explicit_polynomial E k hE
  have h := Real.log_le_log hr hu
  rwa [Real.log_mul (pow_ne_zero _ hE0.ne') (pow_ne_zero _ hkp.ne'),
    Real.log_pow, Real.log_pow] at h

end ExtractionRankSupport
