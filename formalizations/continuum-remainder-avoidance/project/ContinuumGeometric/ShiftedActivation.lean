import ContinuumGeometric.Activation

/-!
The coefficient shift is explicit: output logs s*n-k in (u,u+ell) correspond
to unshifted logs in (u+k,u+k+ell). Natural-index counting requires u+k>=0;
the stronger tail guard is retained. Finite test cardinality is proved for
the ORIGINAL progression indices m*n, with multiplicative injectivity.
-/
namespace ContinuumGeometric

theorem compact_shifted_original_activation (s₀ s₁ u ℓ : ℝ) (m N : ℕ) (k : ℤ)
    (hs₀ : 0 < s₀) (hm : 0 < m) (hℓ : 2 * ((m : ℝ) * s₁) ≤ ℓ)
    (hshift : 0 ≤ u + (k : ℝ)) (htail : ((m : ℝ) * s₁) * N ≤ u + (k : ℝ)) :
    ∀ s ∈ Set.Icc s₀ s₁,
      ∃ tests : Finset ℕ,
        ℓ / (2 * ((m : ℝ) * s₁)) ≤ (tests.card : ℝ) ∧
        ∀ n ∈ tests,
          N ≤ n ∧ u < s * n - k ∧ s * n - k < u + ℓ := by
  intro s hs
  have hactive := compact_power_activation s₀ s₁ (u + (k : ℝ)) ℓ m N
    hs₀ hm hℓ htail s hs
  let labels := activeNaturals (u + (k : ℝ)) ℓ ((m : ℝ) * s)
  have hinj : Function.Injective (fun n : ℕ => m * n) := fun _ _ h => Nat.mul_left_cancel hm h
  have hcard : (labels.image (fun n => m * n)).card = labels.card :=
    Finset.card_image_of_injective labels hinj
  refine ⟨labels.image (fun n => m * n), ?_, ?_⟩
  · rw [hcard]
    exact hactive.1
  · intro n hn
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hn
    have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
    have hspos : 0 < s := lt_of_lt_of_le hs₀ hs.1
    have hδ : 0 < (m : ℝ) * s := mul_pos hmreal hspos
    have hbounds := (mem_activeNaturals_iff (u + (k : ℝ)) ℓ _ hδ hshift i).1 hi
    have hNi : N ≤ i := (hactive.2 i hi).1
    have hid : s * (m * i : ℕ) = (m : ℝ) * s * i := by push_cast; ring
    refine ⟨?_, ?_, ?_⟩
    · calc
        N ≤ i := hNi
        _ ≤ m * i := by nlinarith [hm]
    · rw [hid]
      linarith [hbounds.1]
    · rw [hid]
      linarith [hbounds.2]

end ContinuumGeometric
