import CholletCycleTraceBound

/-! The actual nonnegative permanent upper bound from simple cycles,
finite closed-walk traces, and the proved row-sum contraction estimate. -/
set_option autoImplicit false
open scoped BigOperators
namespace Chollet
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable section

theorem cycle_weight_sum_by_length (C : Matrix V V ℝ) :
    (∑ σ ∈ allCycles,cycleWeight C σ) =
      ∑ k ∈ Finset.range (Fintype.card V),
        ∑ σ ∈ cyclesOfLength (V := V) (k+2),cycleWeight C σ := by
  classical
  have hm : ∀ σ ∈ allCycles (V := V),σ.support.card - 2 ∈ Finset.range (Fintype.card V) := by
    intro σ hσ
    have hc : σ.IsCycle := (Finset.mem_filter.mp hσ).2
    have hl := hc.two_le_card_support
    have hu := Finset.card_le_univ σ.support
    apply Finset.mem_range.mpr
    omega
  have he (k : ℕ) :
      (allCycles (V := V)).filter (fun σ => σ.support.card - 2 = k) =
        cyclesOfLength (V := V) (k+2) := by
    ext σ
    simp only [cyclesOfLength,Finset.mem_filter]
    constructor
    · intro ⟨hσ,hk⟩
      have hc : σ.IsCycle := (Finset.mem_filter.mp hσ).2
      have := hc.two_le_card_support
      exact ⟨hσ,by omega⟩
    · intro ⟨hσ,hk⟩
      exact ⟨hσ,by omega⟩
  have h := Finset.sum_fiberwise_of_maps_to hm (cycleWeight C)
  simpa only [he] using h.symm

theorem cycle_weight_sum_le_trace_series (C : Matrix V V ℝ)
    (hc : ∀ i j,0 ≤ C i j) (hs : ∀ i j,C i j = C j i) :
    (∑ σ ∈ allCycles,cycleWeight C σ) ≤
      ∑ k ∈ Finset.range (Fintype.card V),(C^(k+2)).trace / (k+2 : ℕ) := by
  rw [cycle_weight_sum_by_length]
  exact Finset.sum_le_sum fun k _ => cyclesOfLength_weight_le_trace C hc hs k

theorem cycleWeight_one_add (C : Matrix V V ℝ) (σ : Equiv.Perm V) :
    cycleWeight (1+C) σ = cycleWeight C σ := by
  unfold cycleWeight
  apply Finset.prod_congr rfl
  intro i hi
  have hne := Equiv.Perm.mem_support.mp hi
  simp [Matrix.add_apply,Matrix.one_apply,hne]

theorem log_permanent_one_add_upper (C : Matrix V V ℝ)
    (hc : ∀ i j,0 ≤ C i j) (hs : ∀ i j,C i j = C j i)
    (hd : ∀ i,C i i = 0) (hrow : ∀ i,(∑ j,C i j) ≤ 1 / 2) :
    Real.log (1+C).permanent ≤ (19 / 24 : ℝ) * (C^2).trace := by
  have hunit : ∀ i,(1+C) i i = 1 := by intro i; simp [hd,Matrix.add_apply]
  have hnonneg : ∀ i j,0 ≤ (1+C) i j := by
    intro i j
    simp only [Matrix.add_apply,Matrix.one_apply]
    split_ifs <;> linarith [hc i j]
  calc
    _ ≤ ∑ σ ∈ allCycles,cycleWeight (1+C) σ :=
      log_permanent_le_cycle_sum (1+C) hunit hnonneg
    _ = ∑ σ ∈ allCycles,cycleWeight C σ := by simp only [cycleWeight_one_add]
    _ ≤ ∑ k ∈ Finset.range (Fintype.card V),(C^(k+2)).trace / (k+2 : ℕ) :=
      cycle_weight_sum_le_trace_series C hc hs
    _ ≤ _ := finite_trace_series_upper C hc hs hrow _

end
end Chollet
