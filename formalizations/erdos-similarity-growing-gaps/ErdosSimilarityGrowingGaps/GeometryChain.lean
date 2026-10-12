import ErdosSimilarityGrowingGaps.Activation
import Mathlib.Tactic


namespace ErdosSimilarityGrowingGaps

theorem exists_compact_exponent_range (s : ℝ) (hs : 0 < s) :
    ∃ K : ℕ, 2 ≤ K ∧ s ∈ Set.Icc (1 / (K : ℝ)) (K : ℝ) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max s (1 / s))
  refine ⟨n + 2, by omega, ?_, ?_⟩
  · have hK : (0 : ℝ) < (n + 2 : ℕ) := by positivity
    apply (div_le_iff₀ hK).2
    have hinv : 1 / s < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
    have := (div_lt_iff₀ hs).1 hinv
    push_cast
    nlinarith
  · have hsn : s < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
    push_cast
    linarith

theorem exists_spaced_sampling (s₀ : ℝ) (hs₀ : 0 < s₀) :
    ∃ m : ℕ, 0 < m ∧ 3 ≤ (m : ℝ) * s₀ := by
  obtain ⟨m, hm⟩ := exists_nat_gt (3 / s₀)
  have hprod : 3 < (m : ℝ) * s₀ := (div_lt_iff₀ hs₀).1 hm
  refine ⟨m, ?_, hprod.le⟩
  have hmreal : (0 : ℝ) < m := by nlinarith
  exact_mod_cast hmreal

/-- Three-unit log separation for every exponent in the compact range. -/
theorem sampled_output_gap (s₀ s : ℝ) (m i j : ℕ) (hm : 0 < m)
    (hspace : 3 ≤ (m : ℝ) * s₀) (hs : s₀ ≤ s) (hij : i < j) :
    3 ≤ (m : ℝ) * s * j - (m : ℝ) * s * i := by
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  have hδ : 3 ≤ (m : ℝ) * s := hspace.trans (mul_le_mul_of_nonneg_left hs hmreal.le)
  have hstep : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hij
  nlinarith

/-- First complete dependency chain.

Every ratio has an exact positive power parameter in a countable compact
range, a uniformly separated dyadic subsequence, and finite endpoint-complete
test sets in every sufficiently long/late output window, with explicit count
and original progression tail indices. Avoiding-set existence is still open;
the routing and probability layers remain separate open obligations.
-/
theorem complete_geometric_activation_chain (q : ℝ) (hq₀ : 0 < q) (hq₁ : q < 1) :
    ∃ (s : ℝ) (K m : ℕ),
      0 < s ∧ 2 ≤ K ∧ 0 < m ∧
      s ∈ Set.Icc (1 / (K : ℝ)) (K : ℝ) ∧
      3 ≤ (m : ℝ) * (1 / (K : ℝ)) ∧
      (∀ n : ℕ, q ^ n = (dyadic n) ^ s) ∧
      ∀ (N : ℕ) (u ℓ : ℝ),
        ((m : ℝ) * K) * N ≤ u → 2 * ((m : ℝ) * K) ≤ ℓ →
        ∃ tests : Finset ℕ,
          ℓ / (2 * ((m : ℝ) * K)) ≤ (tests.card : ℝ) ∧
          ∀ n ∈ tests,
            N ≤ m * n ∧
            u < (m : ℝ) * s * n ∧ (m : ℝ) * s * n < u + ℓ ∧
            q ^ (m * n) = (dyadic (m * n)) ^ s := by
  obtain ⟨s, hs, heq⟩ := geometric_parameter q hq₀ hq₁
  obtain ⟨K, hK, hsK⟩ := exists_compact_exponent_range s hs
  have hKreal : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hs₀ : (0 : ℝ) < 1 / K := one_div_pos.2 hKreal
  obtain ⟨m, hm, hspace⟩ := exists_spaced_sampling (1 / (K : ℝ)) hs₀
  refine ⟨s, K, m, hs, hK, hm, hsK, hspace, heq, ?_⟩
  intro N u ℓ hu hℓ
  have htests := compact_power_activation (1 / (K : ℝ)) (K : ℝ) u ℓ m N
    hs₀ hm hℓ hu s hsK
  refine ⟨activeNaturals u ℓ ((m : ℝ) * s), htests.1, ?_⟩
  intro n hn
  obtain ⟨htail, hlo, hhi⟩ := htests.2 n hn
  refine ⟨?_, hlo, hhi, heq (m * n)⟩
  calc
    N ≤ n := htail
    _ ≤ m * n := by nlinarith [hm]

end ErdosSimilarityGrowingGaps
