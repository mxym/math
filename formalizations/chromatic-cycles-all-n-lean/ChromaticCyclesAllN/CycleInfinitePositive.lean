import ChromaticCyclesAllN.CycleSequenceAlgebra
import Mathlib.Tactic.FinCases

namespace ChromaticCycleAll

/-- A robust 3-factor log-concavity invariant for nonnegative sequences. -/
def TripleConcave (a : ℕ → ℚ) : Prop :=
  (∀ k, 0 ≤ a k) ∧
  (∀ k, 3 * a (k-1) * a (k+1) ≤ (a k)^2)

theorem triple_preserved (a : ℕ → ℚ) (h : TripleConcave a) :
    TripleConcave (LC a) := by
  obtain ⟨hpos, htriple⟩ := h
  have hLpos : ∀ k, 0 ≤ LC a k := by
    intro k
    have hprod : 0 ≤ a (k-1) * a (k+1) :=
      mul_nonneg (hpos _) (hpos _)
    have hh := htriple k
    dsimp [LC]
    nlinarith
  constructor
  · exact hLpos
  · intro k
    let p := a (k-1) * a (k+1)
    let q := (a k)^2
    let b := LC a k
    have hp : 0 ≤ p := mul_nonneg (hpos _) (hpos _)
    have hq : 0 ≤ q := sq_nonneg _
    have hb : 0 ≤ b := hLpos k
    have h3pq : 3*p ≤ q := by
      dsimp [p,q]
      simpa only [mul_assoc] using htriple k
    have h2qb : 2*q ≤ 3*b := by
      dsimp [q,b,LC]
      nlinarith [h3pq]
    have hsq1 : (3*p)^2 ≤ q^2 := by
      have hsub : 0 ≤ q - 3*p := by linarith
      have hadd : 0 ≤ q + 3*p := by positivity
      nlinarith [mul_nonneg hsub hadd]
    have hsq2 : (2*q)^2 ≤ (3*b)^2 := by
      have hsub : 0 ≤ 3*b - 2*q := by linarith
      have hadd : 0 ≤ 3*b + 2*q := by positivity
      nlinarith [mul_nonneg hsub hadd]
    have hquad : 3*p^2 ≤ b^2 := by nlinarith [hsq1,hsq2, sq_nonneg p]
    have hleft : LC a (k-1) ≤ (a (k-1))^2 := by
      dsimp [LC]
      simp only [pow_two]
      exact sub_le_self _ (mul_nonneg (hpos _) (hpos _))
    have hright : LC a (k+1) ≤ (a (k+1))^2 := by
      dsimp [LC]
      simp only [pow_two]
      exact sub_le_self _ (mul_nonneg (hpos _) (hpos _))
    have hmult :
        LC a (k-1) * LC a (k+1) ≤
          (a (k-1))^2 * (a (k+1))^2 :=
      mul_le_mul hleft hright (hLpos _) (sq_nonneg _)
    change 3 * LC a (k-1) * LC a (k+1) ≤ (LC a k)^2
    dsimp [p,b] at hquad
    nlinarith [hmult, hquad]


def iterLC (a : ℕ → ℚ) : ℕ → (ℕ → ℚ)
  | 0 => a
  | j + 1 => LC (iterLC a j)

theorem binomialBase_zero_tail (n k : ℕ) (hk : n < k) (hn : 2 ≤ n) :
    binomialBase n k = 0 := by
  have h0 : k ≠ 0 := by omega
  have h1 : k ≠ 1 := by omega
  simp [binomialBase, h0, h1, Nat.choose_eq_zero_of_lt hk]

theorem iterLC_zero_tail (n j k : ℕ) (hn : 2 ≤ n) (hk : n < k) :
    iterLC (binomialBase n) j k = 0 := by
  induction j generalizing k with
  | zero => exact binomialBase_zero_tail n k hk hn
  | succ j ih =>
      change LC (iterLC (binomialBase n) j) k = 0
      have hk1 : n < k+1 := by omega
      rw [LC, ih k hk, ih (k+1) hk1]
      ring

theorem triple_iterate_after (a : ℕ → ℚ) (j : ℕ)
    (h : TripleConcave (iterLC a j)) (t : ℕ) :
    TripleConcave (iterLC a (j+t)) := by
  induction t with
  | zero => simpa using h
  | succ t ih =>
      change TripleConcave (LC (iterLC a (j+t)))
      exact triple_preserved _ ih

theorem finite_triple_certificate (n j : ℕ) (hn : 2 ≤ n)
    (hfinite : ∀ i : Fin (n+1),
      0 ≤ iterLC (binomialBase n) j i.val ∧
      3 * iterLC (binomialBase n) j (i.val-1) *
        iterLC (binomialBase n) j (i.val+1) ≤
        (iterLC (binomialBase n) j i.val)^2) :
    TripleConcave (iterLC (binomialBase n) j) := by
  constructor
  · intro k
    by_cases hk : k ≤ n
    · exact (hfinite ⟨k,by omega⟩).1
    · rw [iterLC_zero_tail n j k hn (by omega)]
  · intro k
    by_cases hk : k ≤ n
    · exact (hfinite ⟨k,by omega⟩).2
    · have hk1 : n < k+1 := by omega
      rw [iterLC_zero_tail n j k hn (by omega),
          iterLC_zero_tail n j (k+1) hn hk1]
      simp

theorem all_iterations_of_finite_cert (n j : ℕ) (hn : 2 ≤ n)
    (ht : TripleConcave (iterLC (binomialBase n) j))
    (hearly : ∀ r : Fin j, ∀ k : Fin (n+1),
       0 ≤ iterLC (binomialBase n) r.val k.val) :
    ∀ r k, 0 ≤ iterLC (binomialBase n) r k := by
  intro r k
  by_cases hr : r < j
  · by_cases hk : k ≤ n
    · exact hearly ⟨r,hr⟩ ⟨k,by omega⟩
    · rw [iterLC_zero_tail n r k hn (by omega)]
  · have hj : j ≤ r := by omega
    have hindex : j+(r-j)=r := Nat.add_sub_of_le hj
    rw [←hindex]
    exact (triple_iterate_after _ j ht (r-j)).1 k

private theorem finite_small_case (n j : ℕ) (hn : 2 ≤ n)
    (hf : ∀ i : Fin (n+1),
       0 ≤ iterLC (binomialBase n) j i.val ∧
       3 * iterLC (binomialBase n) j (i.val-1) *
         iterLC (binomialBase n) j (i.val+1) ≤
         (iterLC (binomialBase n) j i.val)^2)
    (he : ∀ r : Fin j, ∀ i : Fin (n+1),
       0 ≤ iterLC (binomialBase n) r.val i.val) :
    ∀ r k, 0 ≤ iterLC (binomialBase n) r k :=
  all_iterations_of_finite_cert n j hn
    (finite_triple_certificate n j hn hf) he

theorem cycle3_infinitely_log_concave :
    ∀ r k, 0 ≤ iterLC (binomialBase 3) r k := by
  apply finite_small_case 3 0 (by omega)
  · intro i
    fin_cases i <;> norm_num [iterLC, LC, binomialBase, Nat.choose]
  · intro r
    exact Fin.elim0 r

theorem cycle4_infinitely_log_concave :
    ∀ r k, 0 ≤ iterLC (binomialBase 4) r k := by
  apply finite_small_case 4 1 (by omega)
  · intro i
    fin_cases i <;> norm_num [iterLC, LC, binomialBase, Nat.choose]
  · intro r i
    fin_cases r <;> fin_cases i <;> norm_num [iterLC, LC, binomialBase, Nat.choose]

theorem cycle5_infinitely_log_concave :
    ∀ r k, 0 ≤ iterLC (binomialBase 5) r k := by
  apply finite_small_case 5 2 (by omega)
  · intro i
    fin_cases i <;> norm_num [iterLC, LC, binomialBase, Nat.choose]
  · intro r i
    fin_cases r <;> fin_cases i <;> norm_num [iterLC, LC, binomialBase, Nat.choose]

theorem cycle6_infinitely_log_concave :
    ∀ r k, 0 ≤ iterLC (binomialBase 6) r k := by
  apply finite_small_case 6 2 (by omega)
  · intro i
    fin_cases i <;> norm_num [iterLC, LC, binomialBase, Nat.choose]
  · intro r i
    fin_cases r <;> fin_cases i <;> norm_num [iterLC, LC, binomialBase, Nat.choose]

theorem cycle7_infinitely_log_concave :
    ∀ r k, 0 ≤ iterLC (binomialBase 7) r k := by
  apply finite_small_case 7 2 (by omega)
  · intro i
    fin_cases i <;> norm_num [iterLC, LC, binomialBase, Nat.choose]
  · intro r i
    fin_cases r <;> fin_cases i <;> norm_num [iterLC, LC, binomialBase, Nat.choose]

theorem cycle8_infinitely_log_concave :
    ∀ r k, 0 ≤ iterLC (binomialBase 8) r k := by
  apply finite_small_case 8 3 (by omega)
  · intro i
    fin_cases i <;> norm_num [iterLC, LC, binomialBase, Nat.choose]
  · intro r i
    fin_cases r <;> fin_cases i <;> norm_num [iterLC, LC, binomialBase, Nat.choose]

theorem cycle9_infinitely_log_concave :
    ∀ r k, 0 ≤ iterLC (binomialBase 9) r k := by
  apply finite_small_case 9 3 (by omega)
  · intro i
    fin_cases i <;> norm_num [iterLC, LC, binomialBase, Nat.choose]
  · intro r i
    fin_cases r <;> fin_cases i <;> norm_num [iterLC, LC, binomialBase, Nat.choose]

theorem cycle10_infinitely_log_concave :
    ∀ r k, 0 ≤ iterLC (binomialBase 10) r k := by
  apply finite_small_case 10 3 (by omega)
  · intro i
    fin_cases i <;> norm_num [iterLC, LC, binomialBase, Nat.choose]
  · intro r i
    fin_cases r <;> fin_cases i <;> norm_num [iterLC, LC, binomialBase, Nat.choose]

theorem cycle11_infinitely_log_concave :
    ∀ r k, 0 ≤ iterLC (binomialBase 11) r k := by
  apply finite_small_case 11 3 (by omega)
  · intro i
    fin_cases i <;> norm_num [iterLC, LC, binomialBase, Nat.choose]
  · intro r i
    fin_cases r <;> fin_cases i <;> norm_num [iterLC, LC, binomialBase, Nat.choose]

theorem all_small_cycle_sequences_infinitely_log_concave (n : ℕ)
    (hn : 3 ≤ n) (hm : n ≤ 11) :
    ∀ r k, 0 ≤ iterLC (binomialBase n) r k := by
  have h : n=3 ∨ n=4 ∨ n=5 ∨ n=6 ∨ n=7 ∨ n=8 ∨
      n=9 ∨ n=10 ∨ n=11 := by omega
  rcases h with h | h | h | h | h | h | h | h | h
  all_goals subst n
  all_goals first
    | exact cycle3_infinitely_log_concave
    | exact cycle4_infinitely_log_concave
    | exact cycle5_infinitely_log_concave
    | exact cycle6_infinitely_log_concave
    | exact cycle7_infinitely_log_concave
    | exact cycle8_infinitely_log_concave
    | exact cycle9_infinitely_log_concave
    | exact cycle10_infinitely_log_concave
    | exact cycle11_infinitely_log_concave


/-- The five remaining exceptional cycle lengths fail in a finite iteration. -/
theorem cycle12_negative : iterLC (binomialBase 12) 5 2 < 0 := by
  norm_num [iterLC, LC, binomialBase, Nat.choose]

theorem cycle13_negative : iterLC (binomialBase 13) 4 2 < 0 := by
  norm_num [iterLC, LC, binomialBase, Nat.choose]

theorem cycle14_negative : iterLC (binomialBase 14) 4 2 < 0 := by
  norm_num [iterLC, LC, binomialBase, Nat.choose]

theorem cycle15_negative : iterLC (binomialBase 15) 4 2 < 0 := by
  norm_num [iterLC, LC, binomialBase, Nat.choose]

theorem cycle16_negative : iterLC (binomialBase 16) 4 2 < 0 := by
  norm_num [iterLC, LC, binomialBase, Nat.choose]

def InfinitelyLogConcave (a : ℕ → ℚ) : Prop :=
  ∀ r k, 0 ≤ iterLC a r k

theorem all_other_cycle_binomial_sequences_fail (n : ℕ) (hn : 12 ≤ n) :
    ¬ InfinitelyLogConcave (binomialBase n) := by
  intro h
  have hcases : n=12 ∨ n=13 ∨ n=14 ∨ n=15 ∨ n=16 ∨ 17 ≤ n := by omega
  rcases hcases with h12 | h13 | h14 | h15 | h16 | h17
  · subst n
    have hpos := h 5 2
    exact (not_le_of_gt cycle12_negative) hpos
  · subst n
    have hpos := h 4 2
    exact (not_le_of_gt cycle13_negative) hpos
  · subst n
    have hpos := h 4 2
    exact (not_le_of_gt cycle14_negative) hpos
  · subst n
    have hpos := h 4 2
    exact (not_le_of_gt cycle15_negative) hpos
  · subst n
    have hpos := h 4 2
    exact (not_le_of_gt cycle16_negative) hpos
  · have hneg : iterLC (binomialBase n) 3 2 < 0 := by
      simpa only [iterLC] using all_large_cycle_binomial_sequences_fail n h17
    exact (not_le_of_gt hneg) (h 3 2)

theorem cycle_binomial_infinite_classification (n : ℕ) (hn : 3 ≤ n) :
    InfinitelyLogConcave (binomialBase n) ↔ n ≤ 11 := by
  constructor
  · intro h
    by_contra hnot
    have h12 : 12 ≤ n := by omega
    exact all_other_cycle_binomial_sequences_fail n h12 h
  · intro h11
    exact all_small_cycle_sequences_infinitely_log_concave n hn h11

end ChromaticCycleAll
