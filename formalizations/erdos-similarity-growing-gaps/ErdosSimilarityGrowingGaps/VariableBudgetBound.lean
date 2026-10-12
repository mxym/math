import ErdosSimilarityGrowingGaps.VariableSigmaCertificate
namespace ErdosSimilarityGrowingGaps
open Filter Topology Asymptotics
lemma base_budget_le_large_power
    {K : ℕ} (hK : 2 ≤ K) (p σ D : ℝ)
    (hp : 0 < p) (hp1 : p ≤ 1) (hσ : 0 < σ) (hD : 0 ≤ D) :
    ((Nat.ceil (2 * ((K : ℝ) * (σ + D))) + 1 : ℕ) : ℝ) ≤
      (((8 * lateBranching K p σ D) ^ (lateDepth K p σ D + 1) : ℕ) : ℝ) := by
  have hKpos : (0:ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hKD : 0 ≤ σ + D := by linarith
  have hM : 2 ≤ lateBranching K p σ D := lateBranching_ge_two K p σ D
  have hMreal : (2:ℝ) ≤ lateBranching K p σ D := by exact_mod_cast hM
  have hMlower : 24 * ((K:ℝ) * (σ + D)) ≤
      (lateBranching K p σ D : ℝ) := by
    unfold lateBranching variableBranching
    have hc := Nat.le_ceil (24 * (σ + D) / (p / (K:ℝ)))
    have hceil : (24 * (σ + D) / (p / (K:ℝ)) : ℝ) ≤
        Nat.ceil (24 * (σ + D) / (p / (K:ℝ))) := by exact_mod_cast hc
    have hpk : 0 < p / (K:ℝ) := by positivity
    have hden : p / (K : ℝ) ≤ 1 := by
      apply (div_le_iff₀ hKpos).2
      have hKreal : (1 : ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K by omega)
      nlinarith [hp1]
    have hdiv : 24 * ((K:ℝ) * (σ + D)) ≤
        24 * (σ + D) / (p / (K:ℝ)) := by
      apply (le_div_iff₀ hpk).2
      have hKnonneg : 0 ≤ (K:ℝ) * (σ + D) := by positivity
      have heq : (24 * ((K:ℝ) * (σ + D))) * (p / (K:ℝ)) =
          24 * p * (σ + D) := by field_simp
      rw [heq]
      nlinarith
    norm_num [Nat.cast_add]
    exact hdiv.trans (by linarith [hceil])
  have hP : ((Nat.ceil (2 * ((K : ℝ) * (σ + D))) : ℕ) : ℝ) ≤
      2 * ((K:ℝ) * (σ + D)) + 1 := by
    have hc := Nat.ceil_lt_add_one (show 0 ≤ 2 * ((K:ℝ) * (σ + D)) by positivity)
    exact_mod_cast (le_of_lt hc)
  have hceil_le_M :
      (2 * ((K:ℝ) * (σ + D)) + 1) ≤ (lateBranching K p σ D : ℝ) := by
    nlinarith [hMlower]
  have hP' : ((Nat.ceil (2 * ((K : ℝ) * (σ + D))) + 1 : ℕ) : ℝ) ≤
      (lateBranching K p σ D : ℝ) + 1 := by
    push_cast
    linarith
  have hbase : (1:ℝ) ≤ 8 * (lateBranching K p σ D : ℝ) := by nlinarith
  have hpow : (lateBranching K p σ D : ℝ) + 1 ≤
      ((8 * lateBranching K p σ D) ^ (lateDepth K p σ D + 1) : ℕ) := by
    have hd : 0 < lateDepth K p σ D := lateDepth_pos K hK p σ D hp hp1 hσ hD
    have hn : 1 ≤ lateDepth K p σ D + 1 := by omega
    have hnat : lateBranching K p σ D + 1 ≤
        (8 * lateBranching K p σ D) ^ (lateDepth K p σ D + 1) := by
      have hpow0 := pow_two_ge_add_one (8 * lateBranching K p σ D)
      have hpowmon : (8 * lateBranching K p σ D : ℕ) ≤
          (8 * lateBranching K p σ D) ^ (lateDepth K p σ D + 1) := by
        exact Nat.le_pow (by omega)
      exact (by omega)
    exact_mod_cast hnat
  exact hP'.trans (hpow)
end ErdosSimilarityGrowingGaps
