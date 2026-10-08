import ContinuumRemainder.SampleSchedule

set_option autoImplicit false

#print axioms ContinuumRemainder.LogSyndetic.exists_spaced_bins
#print axioms ContinuumRemainder.LogSyndetic.exists_sampledLogConfiguration
#print axioms ContinuumRemainder.SampledLogConfiguration.a_tendsto
#print axioms ContinuumRemainder.open_window_count_bounds
#print axioms ContinuumRemainder.SampledLogConfiguration.activeLabels_count_bounds
#print axioms ContinuumRemainder.SampledLogConfiguration.potentialPairs_active_count
#print axioms ContinuumRemainder.exists_sample_routing_schedule_late
#print axioms ContinuumRemainder.sampleSchedule_node_entropy_lt

/-- In (1,9), both endpoint labels are inactive. This leaves precisely one
test, attaining the lower density bound for D=4 and ell=8. -/
example :
    (8 : ℝ) / 4 - 1 ≤ (({1} : Finset ℕ).card : ℝ) ∧
      (({1} : Finset ℕ).card : ℝ) ≤ 1 + (8 : ℝ) / 3 := by
  have ht : Filter.Tendsto (fun n : ℕ => 4 * (n : ℝ) + 1)
      Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right Filter.atTop 1
      (Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 4)
        tendsto_natCast_atTop_atTop)
  have hmono : Monotone (fun n : ℕ => 4 * (n : ℝ) + 1) := by
    intro i j hij
    have hc : (i : ℝ) ≤ j := by exact_mod_cast hij
    linarith
  apply ContinuumRemainder.open_window_count_bounds
    (fun n : ℕ => 4 * (n : ℝ) + 1) ht hmono 4 (by norm_num)
    (fun n => by push_cast; linarith)
    (fun n => by push_cast; linarith) 1 8 (by norm_num) (by norm_num) {1}
  intro n
  simp only [Finset.mem_singleton]
  constructor
  · rintro rfl
    norm_num
  · rintro ⟨hl, hu⟩
    have hn0 : 0 < n := by exact_mod_cast (by linarith : (0 : ℝ) < n)
    have hn2 : n < 2 := by exact_mod_cast (by linarith : (n : ℝ) < 2)
    omega
