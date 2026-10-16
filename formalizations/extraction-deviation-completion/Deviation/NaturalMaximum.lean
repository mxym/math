import Deviation.RoundedTarget
import Mathlib.Order.Lattice.Nat

open scoped Topology
open Set Filter

namespace ExtractionDeviation
noncomputable section

theorem natTargets_bddAbove (S : Set ℕ) (hpos : ∀ K ∈ S, 0 < K)
    (k : ℕ) (hk : 0 < k) (C z : ℝ)
    (hu : ∀ K ∈ S, (Real.log K-k*C)/Real.sqrt k < z) : BddAbove S := by
  refine ⟨roundedTarget C z k,?_⟩
  intro K hK
  have hKR : (0:ℝ) < K := by exact_mod_cast hpos K hK
  have hsqrt : 0 < Real.sqrt (k:ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hk)
  have hlog : Real.log K < k*C+z*Real.sqrt k := by
    have h := (div_lt_iff₀ hsqrt).mp (hu K hK)
    linarith
  have hexp : (K:ℝ) ≤ Real.exp (k*C+z*Real.sqrt k) := by
    simpa only [Real.exp_log hKR] using (Real.exp_le_exp.mpr hlog.le)
  exact_mod_cast hexp.trans (Nat.le_ceil _)

/-- Inverting a genuine family of finite natural target sets requires no
monotonicity of a chosen protocol. Exclusion applies to every larger target. -/
theorem maximalTarget_gaussian_of_brackets (S : ℕ → Set ℕ) (C q : ℝ)
    (hpos : ∀ k K, K ∈ S k → 0 < K)
    (hu : ∀ z, q < z → ∀ᶠ k : ℕ in atTop,
      ∀ K ∈ S k, (Real.log K-k*C)/Real.sqrt k < z)
    (hl : ∀ z, z < q → ∃ K : ℕ → ℕ,
      (∀ᶠ k : ℕ in atTop, K k ∈ S k) ∧
      Tendsto (fun k : ℕ => (Real.log (K k)-k*C)/Real.sqrt k) atTop (𝓝 z)) :
    (∀ᶠ k : ℕ in atTop, (S k).Nonempty ∧ BddAbove (S k) ∧
      sSup (S k) ∈ S k) ∧
    Tendsto (fun k : ℕ => (Real.log ((sSup (S k):ℕ):ℝ)-k*C)/Real.sqrt k)
      atTop (𝓝 q) := by
  obtain ⟨K,hKmem,hKlimit⟩ := hl (q-1) (by linarith)
  have hmax : ∀ᶠ k : ℕ in atTop, (S k).Nonempty ∧ BddAbove (S k) ∧
      sSup (S k) ∈ S k := by
    filter_upwards [hKmem,hu (q+1) (by linarith),eventually_gt_atTop 0] with k hk hu hkpos
    have hne : (S k).Nonempty := ⟨K k,hk⟩
    have hb := natTargets_bddAbove (S k) (hpos k) k hkpos C (q+1) hu
    exact ⟨hne,hb,Nat.sSup_mem hne hb⟩
  refine ⟨hmax,?_⟩
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  obtain ⟨L,hLmem,hLlim⟩ := hl (q-δ/2) (by linarith)
  have hL := hLlim.eventually (Ioi_mem_nhds (show q-δ < q-δ/2 by linarith))
  filter_upwards [hmax,hu (q+δ) (by linarith),hLmem,hL,eventually_gt_atTop 0]
    with k hmaxk hUk hLk hLow hk
  have hle : L k ≤ sSup (S k) := le_csSup hmaxk.2.1 hLk
  have hLpos : (0:ℝ) < L k := by exact_mod_cast hpos k _ hLk
  have hlog := Real.log_le_log hLpos (show (L k:ℝ) ≤ ((sSup (S k):ℕ):ℝ) by exact_mod_cast hle)
  have hcenter : (Real.log (L k)-k*C)/Real.sqrt k ≤
      (Real.log ((sSup (S k):ℕ):ℝ)-k*C)/Real.sqrt k :=
    div_le_div_of_nonneg_right (sub_le_sub_right hlog _) (Real.sqrt_nonneg _)
  have hUpper := hUk _ hmaxk.2.2
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end
end ExtractionDeviation
