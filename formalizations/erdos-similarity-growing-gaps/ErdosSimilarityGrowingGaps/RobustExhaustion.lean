import ErdosSimilarityGrowingGaps.TailAnalysis
import ErdosSimilarityGrowingGaps.CoefficientCover
import ErdosSimilarityGrowingGaps.WindowRepair
import ErdosSimilarityGrowingGaps.CountableExhaustion

namespace ErdosSimilarityGrowingGaps

open Filter Set Topology MeasureTheory
open scoped BigOperators ENNReal

/-! A compact robust blocker is the finite positive-coefficient object that is
    produced by the routing construction.  This file performs the countable
    sign/scale/tail exhaustion after that finite object has been supplied. -/

def CompactRobustSpec (Z : LogScale) : Prop :=
  ∀ K : ℕ, 2 ≤ K → ∀ k : ℤ, ∀ N : ℕ, ∀ α q : ℝ,
    0 < α → 0 ≤ q → ∀ δ : ℝ, 0 < δ → δ < 1 →
      ∃ H : Set ℝ, IsOpen H ∧ OnePeriodic H ∧
        unitDensity H < ENNReal.ofReal δ ∧
        CompactRobustHits Z H K k N α q

def CompactRobustFamilySpec {ι : Type*} [Countable ι]
    (F : ι → LogScale) : Prop :=
  ∀ i, CompactRobustSpec (F i)

theorem robustExhaustion_of_compactRobustSpec
    {ι : Type*} [Countable ι] [Nonempty ι]
    {F : ι → LogScale} (hC : CompactRobustFamilySpec F) :
    WindowBlockerSpec F := by
  intro ε hε hε₁
  let Outer := ι × (ℕ × ℕ)
  let Inner := {K : ℕ // 2 ≤ K} × (ℤ × (ℕ × Bool))
  let Index := Outer × Inner
  obtain ⟨b, hbpos, hbsum⟩ := exists_budget_allocation (ι := Index) hε
  let w : Outer → ℝ≥0∞ := fun o => ∑' r : Inner, b (o, r)
  have hw : ∑' o : Outer, w o < ENNReal.ofReal ε := by
    rw [show (∑' o : Outer, w o) = ∑' q : Index, b q by
      simpa only [w] using (ENNReal.tsum_prod' (f := b)).symm]
    exact hbsum
  apply blockerFamily_of_grid_blockers w hw
  intro i j q
  let o : Outer := (i, (j, q))
  have hwt : w o ≠ ∞ := by
    have hle : w o ≤ ∑' o : Outer, w o := ENNReal.le_tsum o
    exact ne_top_of_lt (hle.trans_lt hw)
  have hwt_nonneg : 0 ≤ (w o).toReal := ENNReal.toReal_nonneg
  have hwt_pos : 0 < (w o).toReal := by
    have hle : b (o, (⟨2, by omega⟩, (0, (0, true)))) ≤ w o := by
      exact ENNReal.le_tsum (f := fun r : Inner => b (o, r)) _
    exact ENNReal.toReal_pos
      (ne_of_gt (lt_of_lt_of_le (hbpos _) hle)) hwt
  have hwt_one : (w o).toReal < 1 := by
    have hle : w o ≤ ∑' o : Outer, w o := ENNReal.le_tsum o
    have hlt : w o < ENNReal.ofReal ε := hle.trans_lt hw
    have hreal : (w o).toReal < (ENNReal.ofReal ε).toReal :=
      (ENNReal.toReal_lt_toReal hwt ENNReal.ofReal_ne_top).2 hlt
    rw [ENNReal.toReal_ofReal hε.le] at hreal
    exact hreal.trans (by linarith [hε₁])
  have hdata : ∀ r : Inner, ∃ H : Set ℝ, IsOpen H ∧ OnePeriodic H ∧
      unitDensity H < ENNReal.ofReal (b (o, r)).toReal ∧
      CompactRobustHits (F i) H r.1.1 r.2.1 r.2.2.1
        (1 / (j + 1 : ℝ)) q := by
    intro r
    have hbr_top : b (o, r) ≠ ∞ := by
      have hle : b (o, r) ≤ ∑' q : Index, b q := ENNReal.le_tsum _
      exact ne_top_of_lt (hle.trans_lt hbsum)
    have hbr_pos : 0 < (b (o, r)).toReal :=
      ENNReal.toReal_pos (ne_of_gt (hbpos _)) hbr_top
    have hbr_one : (b (o, r)).toReal < 1 := by
      have hle : b (o, r) ≤ ∑' q : Index, b q := ENNReal.le_tsum _
      have hlt : b (o, r) < ENNReal.ofReal ε := hle.trans_lt hbsum
      have hreal : (b (o, r)).toReal < (ENNReal.ofReal ε).toReal :=
        (ENNReal.toReal_lt_toReal hbr_top ENNReal.ofReal_ne_top).2 hlt
      rw [ENNReal.toReal_ofReal hε.le] at hreal
      exact hreal.trans (by linarith [hε₁])
    exact hC i r.1.1 r.1.2 r.2.1 r.2.2.1 (1 / (j + 1 : ℝ)) q
      (by positivity) (by positivity) _ hbr_pos hbr_one
  choose H hHo hHp hHμ hHhit using hdata
  let S : Set ℝ := ⋃ r : Inner, if r.2.2.2 then H r else reflectedSet (H r)
  have hSo : IsOpen S := by
    apply isOpen_iUnion
    intro r
    by_cases hs : r.2.2.2
    · simpa [hs] using hHo r
    · simpa [hs, reflectedSet] using (hHo r).preimage continuous_neg
  have hSp : OnePeriodic S := by
    intro x
    simp only [S, mem_iUnion]
    exact exists_congr fun r => by
      by_cases hs : r.2.2.2
      · simpa [hs] using hHp r x
      · simpa [hs] using onePeriodic_reflectedSet (hHp r) x
  have hSd : unitDensity S ≤ w o := by
    calc
      unitDensity S ≤ ∑' r : Inner,
          unitDensity (if r.2.2.2 then H r else reflectedSet (H r)) :=
        unitDensity_iUnion_le (fun r : Inner => if r.2.2.2 then H r else reflectedSet (H r))
      _ ≤ ∑' r : Inner, b (o, r) := by
        apply ENNReal.tsum_le_tsum
        intro r
        by_cases hs : r.2.2.2
        · have hbr_top : b (o, r) ≠ ∞ := by
            have hle : b (o, r) ≤ ∑' q : Index, b q := ENNReal.le_tsum _
            exact ne_top_of_lt (hle.trans_lt hbsum)
          simpa [hs, ENNReal.ofReal_toReal hbr_top] using (hHμ r).le
        · have hbr_top : b (o, r) ≠ ∞ := by
            have hle : b (o, r) ≤ ∑' q : Index, b q := ENNReal.le_tsum _
            exact ne_top_of_lt (hle.trans_lt hbsum)
          have hs' : r.2.2.2 = false := Bool.eq_false_of_not_eq_true hs
          simp only [hs', Bool.false_eq_true, ↓reduceIte]
          rw [unitDensity_reflectedSet (H r) (hHp r)]
          simpa [ENNReal.ofReal_toReal hbr_top] using (hHμ r).le
      _ = w o := rfl
  refine ⟨S, hSo, hSp, hSd, ?_⟩
  intro s y c hs hc f hf ρ hρ
  obtain ⟨k, t, ht₁, ht₂, hceq⟩ := positive_dyadic_coefficient_cover |c|
    (abs_pos.mpr hc)
  obtain ⟨K, hK, hsK⟩ := exists_compact_exponent_range s hs
  obtain ⟨N₀, hfN⟩ := hf
  have hev : ∀ᶠ n : ℕ in atTop, input (F i) n < ρ :=
    (input_tendsto_zero (F i)).eventually (Iio_mem_nhds hρ)
  obtain ⟨Nρ, hNρ⟩ := eventually_atTop.1 hev
  let N := max N₀ Nρ
  let ppar : PowerParams (1 / (K : ℝ)) K :=
    (⟨s, hsK⟩, ⟨t, ht₁, ht₂.le⟩)
  have hN₀ : N₀ ≤ N := le_max_left _ _
  have hNρ' : Nρ ≤ N := le_max_right _ _
  by_cases hcpos : 0 < c
  · let r : Inner := (⟨K, hK⟩, (k, (N, true)))
    obtain ⟨n, hn, hhit⟩ := hHhit r y ppar f (by
      intro n hnN
      have hfn := hfN n (hN₀.trans hnN)
      have hpow : ppar.1.1 = s := rfl
      have hcoef : ppar.2.1 * (2 : ℝ) ^ k = c := by
        dsimp [ppar]
        rw [abs_of_pos hcpos] at hceq
        linarith
      simpa [ppar, r, hpow, hcoef] using hfn)
    refine ⟨n, hNρ n (hNρ'.trans hn), ?_⟩
    apply mem_iUnion.2
    refine ⟨r, ?_⟩
    simpa [r] using hhit
  · have hcneg : c < 0 := lt_of_le_of_ne (le_of_not_gt hcpos) hc
    let r : Inner := (⟨K, hK⟩, (k, (N, false)))
    obtain ⟨n, hn, hhit⟩ := hHhit r (-y) ppar (fun a => -f a) (by
      intro n hnN
      have hfn := hfN n (hN₀.trans hnN)
      have hcoef : ppar.2.1 * (2 : ℝ) ^ k = -c := by
        dsimp [ppar]
        rw [abs_of_neg hcneg] at hceq
        linarith
      have heq : (-f (input (F i) n)) - -y -
          ppar.2.1 * (2 : ℝ) ^ k * (input (F i) n) ^ ppar.1.1 =
          -(f (input (F i) n) - y - c * (input (F i) n) ^ s) := by
        rw [hcoef]
        congr 1
        ring
      rw [heq, abs_neg]
      simpa [ppar] using hfn)
    refine ⟨n, hNρ n (hNρ'.trans hn), ?_⟩
    apply mem_iUnion.2
    refine ⟨r, ?_⟩
    have : -f (input (F i) n) ∈ H r := hhit
    simpa [r, reflectedSet] using this

end ErdosSimilarityGrowingGaps
