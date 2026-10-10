import ErdosSimilarityGrowingGaps.PowerCore
import Mathlib.Tactic


/-!
Exact open-window activation, including exponent values at either boundary.
This proves actual finite counts. No uniform blocker is assumed.
-/
namespace ErdosSimilarityGrowingGaps

noncomputable def activeIntegers (u ℓ δ : ℝ) : Finset ℤ :=
  Finset.Ioo ⌊u / δ⌋ ⌈(u + ℓ) / δ⌉

theorem mem_activeIntegers_iff (u ℓ δ : ℝ) (hδ : 0 < δ) (n : ℤ) :
    n ∈ activeIntegers u ℓ δ ↔ u < δ * n ∧ δ * n < u + ℓ := by
  simp only [activeIntegers, Finset.mem_Ioo, Int.floor_lt, Int.lt_ceil]
  constructor
  · rintro ⟨hlo, hhi⟩
    exact ⟨by simpa [mul_comm] using (div_lt_iff₀ hδ).1 hlo,
      by simpa [mul_comm] using (lt_div_iff₀ hδ).1 hhi⟩
  · rintro ⟨hlo, hhi⟩
    exact ⟨(div_lt_iff₀ hδ).2 (by simpa [mul_comm] using hlo),
      (lt_div_iff₀ hδ).2 (by simpa [mul_comm] using hhi)⟩

theorem activation_card_exact (u ℓ δ : ℝ) (hδ : 0 < δ) (hℓ : 0 < ℓ) :
    ((activeIntegers u ℓ δ).card : ℝ) =
      (⌈(u + ℓ) / δ⌉ : ℝ) - (⌊u / δ⌋ : ℝ) - 1 := by
  have hfloor := Int.floor_le (u / δ)
  have hceil := Int.le_ceil ((u + ℓ) / δ)
  have hlt : u / δ < (u + ℓ) / δ := (div_lt_div_iff_of_pos_right hδ).2 (by linarith)
  have hbounds : ⌊u / δ⌋ < ⌈(u + ℓ) / δ⌉ := by
    exact_mod_cast lt_of_le_of_lt hfloor (lt_of_lt_of_le hlt hceil)
  have hcard := Int.card_Ioo_of_lt _ _ hbounds
  exact_mod_cast hcard

theorem activation_card_lower (u ℓ δ : ℝ) (hδ : 0 < δ) (hℓ : 0 < ℓ) :
    ℓ / δ - 1 ≤ ((activeIntegers u ℓ δ).card : ℝ) := by
  rw [activation_card_exact u ℓ δ hδ hℓ]
  have hfloor := Int.floor_le (u / δ)
  have hceil := Int.le_ceil ((u + ℓ) / δ)
  rw [add_div] at hceil ⊢
  linarith

theorem activation_card_uniform (u ℓ δ D : ℝ) (hδ : 0 < δ)
    (hδD : δ ≤ D) (hℓ : 2 * D ≤ ℓ) :
    ℓ / (2 * D) ≤ ((activeIntegers u ℓ δ).card : ℝ) := by
  have hD : 0 < D := lt_of_lt_of_le hδ hδD
  have hℓpos : 0 < ℓ := lt_of_lt_of_le (by positivity : 0 < 2 * D) hℓ
  have hdiv : ℓ / D ≤ ℓ / δ := div_le_div_of_nonneg_left hℓpos.le hδ hδD
  have hone : 1 ≤ ℓ / (2 * D) := (le_div_iff₀ (by positivity : 0 < 2 * D)).2 (by simpa using hℓ)
  have hhalf : ℓ / D = 2 * (ℓ / (2 * D)) := by field_simp
  have hcount := activation_card_lower u ℓ δ hδ hℓpos
  linarith

/-- Every active integer is a natural tail index at sufficiently late output position. -/
theorem activation_tail (u ℓ δ : ℝ) (hδ : 0 < δ) (N : ℕ)
    (hu : δ * N ≤ u) (n : ℤ) (hn : n ∈ activeIntegers u ℓ δ) :
    (N : ℤ) < n := by
  have hlo := (mem_activeIntegers_iff u ℓ δ hδ n).1 hn |>.1
  have hreal : (N : ℝ) < (n : ℝ) := by nlinarith
  exact_mod_cast hreal

noncomputable def activeNaturals (u ℓ δ : ℝ) : Finset ℕ :=
  (activeIntegers u ℓ δ).image Int.toNat

theorem activeNaturals_card (u ℓ δ : ℝ) (hδ : 0 < δ) (hu : 0 ≤ u) :
    (activeNaturals u ℓ δ).card = (activeIntegers u ℓ δ).card := by
  apply Finset.card_image_of_injOn
  intro a ha b hb hab
  have ha₀ : 0 ≤ a := (activation_tail u ℓ δ hδ 0 (by simpa using hu) a ha).le
  have hb₀ : 0 ≤ b := (activation_tail u ℓ δ hδ 0 (by simpa using hu) b hb).le
  calc
    a = (a.toNat : ℤ) := (Int.toNat_of_nonneg ha₀).symm
    _ = (b.toNat : ℤ) := by rw [hab]
    _ = b := Int.toNat_of_nonneg hb₀

theorem mem_activeNaturals_iff (u ℓ δ : ℝ) (hδ : 0 < δ) (hu : 0 ≤ u) (n : ℕ) :
    n ∈ activeNaturals u ℓ δ ↔ u < δ * n ∧ δ * n < u + ℓ := by
  constructor
  · intro hn
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hn
    have hz₀ : 0 ≤ z := (activation_tail u ℓ δ hδ 0 (by simpa using hu) z hz).le
    have hcast : (z.toNat : ℝ) = (z : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hz₀
    rw [hcast]
    exact (mem_activeIntegers_iff u ℓ δ hδ z).1 hz
  · intro hn
    apply Finset.mem_image.2
    refine ⟨(n : ℤ), ?_, by simp⟩
    apply (mem_activeIntegers_iff u ℓ δ hδ (n : ℤ)).2
    simpa using hn

/-- A uniform count and explicit natural tail indices for a compact continuum of exponents. -/
theorem compact_power_activation (s₀ s₁ u ℓ : ℝ) (m N : ℕ)
    (hs₀ : 0 < s₀) (hm : 0 < m) (hℓ : 2 * ((m : ℝ) * s₁) ≤ ℓ)
    (hu : ((m : ℝ) * s₁) * N ≤ u) :
    ∀ s ∈ Set.Icc s₀ s₁,
      ℓ / (2 * ((m : ℝ) * s₁)) ≤
        ((activeNaturals u ℓ ((m : ℝ) * s)).card : ℝ) ∧
      ∀ n ∈ activeNaturals u ℓ ((m : ℝ) * s),
        N ≤ n ∧ u < (m : ℝ) * s * n ∧ (m : ℝ) * s * n < u + ℓ := by
  intro s hs
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  have hspos : 0 < s := lt_of_lt_of_le hs₀ hs.1
  have hδ : 0 < (m : ℝ) * s := mul_pos hmreal hspos
  have hδD : (m : ℝ) * s ≤ (m : ℝ) * s₁ := mul_le_mul_of_nonneg_left hs.2 hmreal.le
  have huδ : ((m : ℝ) * s) * N ≤ u :=
    (mul_le_mul_of_nonneg_right hδD (Nat.cast_nonneg N)).trans hu
  have hu₀ : 0 ≤ u := (by positivity : 0 ≤ ((m : ℝ) * s) * N).trans huδ
  constructor
  · rw [activeNaturals_card u ℓ _ hδ hu₀]
    exact activation_card_uniform u ℓ _ _ hδ hδD hℓ
  · intro n hn
    have hmem := (mem_activeNaturals_iff u ℓ _ hδ hu₀ n).1 hn
    have htail : (N : ℝ) < (n : ℝ) := by nlinarith [hmem.1]
    exact ⟨(by exact_mod_cast htail.le), hmem⟩

end ErdosSimilarityGrowingGaps
