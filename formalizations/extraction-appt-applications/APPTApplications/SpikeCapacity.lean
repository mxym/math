import APPTApplications.SpikeEntropy

open scoped BigOperators ComplexOrder Topology
open Matrix
namespace ExtractionAPPT
noncomputable section

/-- Exact faithful capacity of the explicit physical APPT state, for every unit
vector in every nontrivial dimension pair. The local cap is proved inactive. -/
theorem spikeState_capacity {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n)
    (v : Fin m × Fin n → ℂ) (hv : (∑ p, star (v p)*v p)=1) :
    physicalCapacity m n (spikeState m n v) =
      (Real.log (((m:ℝ)*n)/((m:ℝ)*n+2)) + 3*Real.log 3/((m:ℝ)*n+2))/2 := by
  have hmR : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
  have hD : 0 < (m:ℝ)*n := by positivity
  have hZ : 0 < (m:ℝ)*n+2 := by positivity
  have hlog : Real.log ((m:ℝ)*n) ≤ Real.log ((m:ℝ)*n+2) :=
    Real.log_le_log hD (by linarith)
  have hl3 : 0 ≤ Real.log (3:ℝ) := Real.log_nonneg (by norm_num)
  have hthree : Real.log (3:ℝ) ≤ 2*Real.log m := by
    have hh := Real.log_le_log (by norm_num : (0:ℝ)<3)
      (show (3:ℝ) ≤ (m:ℝ)*m by nlinarith)
    rw [Real.log_mul (by positivity : (m:ℝ)≠0) (by positivity : (m:ℝ)≠0)] at hh
    linarith
  have hfrac : 3*Real.log 3/((m:ℝ)*n+2) ≤ Real.log 3 := by
    rw [div_le_iff₀ hZ]
    have hDlow : (1:ℝ) ≤ (m:ℝ)*n := by nlinarith
    nlinarith
  rw [physicalCapacity_eq (by omega) (by omega) hmn _ (spikeState_density m n v hv),
    spikeState_entropy m n v hv]
  rw [min_eq_right (show (Real.log ((m:ℝ)*n) -
      (Real.log ((m:ℝ)*n+2)-3*Real.log 3/((m:ℝ)*n+2)))/2 ≤ Real.log m by linarith)]
  rw [Real.log_div hD.ne' hZ.ne']
  ring

/-- The explicit lower example is a member of the actual physical optimization
set, so it yields a bound on its genuine attained capacity supremum. -/
theorem spike_capacity_le_apptMax {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n)
    (v : Fin m × Fin n → ℂ) (hv : (∑ p, star (v p)*v p)=1) :
    (Real.log (((m:ℝ)*n)/((m:ℝ)*n+2)) + 3*Real.log 3/((m:ℝ)*n+2))/2 ≤
      apptMaxCapacity m n := by
  obtain ⟨A,hA,_,hg⟩ := exists_appt_capacity_isGreatest hm hmn
  have hval : physicalCapacity m n (spikeState m n v) ∈ apptCapacityValues m n :=
    ⟨spikeState m n v,spikeState_mem_appt m n v hv,rfl⟩
  have hle := hg.2 hval
  rw [spikeState_capacity hm hmn v hv] at hle
  exact hle.trans_eq hg.csSup_eq.symm

end
end ExtractionAPPT
