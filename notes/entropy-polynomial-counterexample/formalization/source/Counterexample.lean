import Signs
import FourRoots
import Mathlib.Algebra.Polynomial.Roots

set_option autoImplicit false
set_option maxHeartbeats 0

namespace EntropyCounterexample

/-- The polynomial-valued form of the original finite sum (1.3). -/
noncomputable def hPolynomial (k r : ℕ) : Polynomial ℝ :=
  ∑ j ∈ Finset.range k,
    Polynomial.C (∑ v ∈ Finset.range (j+1), (-1 : ℝ) ^ (j-v) / (v+1) *
      (Nat.choose (r*v+k) k : ℝ) * (Nat.choose k (j-v) : ℝ)) * Polynomial.X ^ (r*j)

/-- The polynomial in equation (1.4), without any coefficient-list substitution. -/
noncomputable def pPolynomial (k r : ℕ) (a : ℝ) : Polynomial ℝ :=
  Polynomial.C (a*k) * (1-Polynomial.X^r)^k * hPolynomial k k -
    Polynomial.C (r : ℝ) * (1-Polynomial.X^k)^k * hPolynomial k r

theorem eval_hPolynomial (k r : ℕ) (x : ℝ) :
    (hPolynomial k r).eval x = h k r x := by
  simp [hPolynomial, h, Polynomial.eval_finsetSum, mul_comm]

theorem eval_pPolynomial (k r : ℕ) (a x : ℝ) :
    (pPolynomial k r a).eval x = p k r a x := by
  simp [pPolynomial, p, eval_hPolynomial]

theorem p_continuous : Continuous (p 11 10 alpha) := by
  simp_rw [show p 11 10 alpha = fun x => alpha * A x - B x from funext (p_special alpha)]
  unfold A B P Q
  fun_prop

/-- Four zeros in four specific, pairwise disjoint open subintervals of `(0,1)`. -/
theorem counterexample_four_intervals :
    ∃ x1 x2 x3 x4 : ℝ,
      x1 ∈ Set.Ioo (1/5) (2/5) ∧ x2 ∈ Set.Ioo (2/5) (3/5) ∧
      x3 ∈ Set.Ioo (3/5) (2/3) ∧ x4 ∈ Set.Ioo (2/3) (4/5) ∧
      p 11 10 alpha x1 = 0 ∧ p 11 10 alpha x2 = 0 ∧
      p 11 10 alpha x3 = 0 ∧ p 11 10 alpha x4 = 0 :=
  four_roots_in_open_intervals p_continuous sample_one_fifth sample_two_fifths
    sample_three_fifths sample_two_thirds sample_four_fifths

/-- Four ordered zeros of the original function, with no sign hypotheses. -/
theorem counterexample_four_ordered_roots :
    ∃ x1 x2 x3 x4 : ℝ,
      0 < x1 ∧ x1 < x2 ∧ x2 < x3 ∧ x3 < x4 ∧ x4 < 1 ∧
      p 11 10 alpha x1 = 0 ∧ p 11 10 alpha x2 = 0 ∧
      p 11 10 alpha x3 = 0 ∧ p 11 10 alpha x4 = 0 :=
  four_ordered_roots p_continuous sample_one_fifth sample_two_fifths
    sample_three_fifths sample_two_thirds sample_four_fifths

/-- The polynomial is nonzero, witnessed by its strictly positive value at `1/5`. -/
theorem pPolynomial_ne_zero : pPolynomial 11 10 alpha ≠ 0 := by
  intro heq
  have hz : p 11 10 alpha (1/5) = 0 := by
    rw [← eval_pPolynomial, heq]
    simp
  linarith [sample_one_fifth]

/-- Roots strictly in `(0,1)`, counted with their polynomial multiplicities. -/
noncomputable def unitRootCount (q : Polynomial ℝ) : ℕ := by
  classical
  exact (q.roots.filter (fun x => x ∈ Set.Ioo (0 : ℝ) 1)).card

/-- Any four distinct roots in the interval give a multiplicity count of at least four. -/
theorem root_count_ge_four {q : Polynomial ℝ} (hq : q ≠ 0)
    {x1 x2 x3 x4 : ℝ}
    (hx1 : x1 ∈ Set.Ioo 0 1) (hx2 : x2 ∈ Set.Ioo 0 1)
    (hx3 : x3 ∈ Set.Ioo 0 1) (hx4 : x4 ∈ Set.Ioo 0 1)
    (h12 : x1 ≠ x2) (h13 : x1 ≠ x3) (h14 : x1 ≠ x4)
    (h23 : x2 ≠ x3) (h24 : x2 ≠ x4) (h34 : x3 ≠ x4)
    (hz1 : q.eval x1 = 0) (hz2 : q.eval x2 = 0)
    (hz3 : q.eval x3 = 0) (hz4 : q.eval x4 = 0) :
    4 ≤ unitRootCount q := by
  classical
  let s : Finset ℝ := {x1, x2, x3, x4}
  let m := q.roots.filter (fun x => x ∈ Set.Ioo (0 : ℝ) 1)
  have hc : s.card = 4 := by simp [s, h12, h13, h14, h23, h24, h34]
  have hs : s ⊆ m.toFinset := by
    intro x hx
    simp only [s, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · simpa [m, Polynomial.mem_roots hq, Polynomial.IsRoot] using And.intro hz1 hx1
    · simpa [m, Polynomial.mem_roots hq, Polynomial.IsRoot] using And.intro hz2 hx2
    · simpa [m, Polynomial.mem_roots hq, Polynomial.IsRoot] using And.intro hz3 hx3
    · simpa [m, Polynomial.mem_roots hq, Polynomial.IsRoot] using And.intro hz4 hx4
  calc
    4 = s.card := hc.symm
    _ ≤ m.toFinset.card := Finset.card_le_card hs
    _ ≤ m.card := Multiset.toFinset_card_le m

/-- The original polynomial has at least four roots in `(0,1)`, counting multiplicity. -/
theorem counterexample_root_count : 4 ≤ unitRootCount (pPolynomial 11 10 alpha) := by
  obtain ⟨x1, x2, x3, x4, hx1, hx2, hx3, hx4, h12, h13, h14, h23, h24, h34,
    hz1, hz2, hz3, hz4⟩ :=
    four_distinct_roots p_continuous sample_one_fifth sample_two_fifths
      sample_three_fifths sample_two_thirds sample_four_fifths
  apply root_count_ge_four pPolynomial_ne_zero hx1 hx2 hx3 hx4 h12 h13 h14 h23 h24 h34
  · simpa only [eval_pPolynomial] using hz1
  · simpa only [eval_pPolynomial] using hz2
  · simpa only [eval_pPolynomial] using hz3
  · simpa only [eval_pPolynomial] using hz4

/-- In particular, the claimed multiplicity count of two is false. -/
theorem counterexample_not_two : unitRootCount (pPolynomial 11 10 alpha) ≠ 2 := by
  have h := counterexample_root_count
  omega

/-- A counterexample satisfying positivity, strict order, coprimality, and the exact parameter equation. -/
theorem counterexample_to_conjecture_two :
    ∃ k r : ℕ, ∃ a : ℝ,
      0 < r ∧ r < k ∧ Nat.Coprime k r ∧ a ∈ Set.Ioo 0 1 ∧
      a^r * (1+a)^(k-r) = 1 ∧ 4 ≤ unitRootCount (pPolynomial k r a) := by
  refine ⟨11, 10, alpha, by norm_num, by norm_num, by decide,
    ⟨alpha_pos, alpha_lt_one⟩, ?_, counterexample_root_count⟩
  simpa using alpha_equation

/-- The result applies to the defining parameter, independently of how it is selected. -/
theorem counterexample_for_any_parameter {a : ℝ}
    (ha : a ∈ Set.Ioo 0 1) (heq : a^10 * (1+a) = 1) :
    4 ≤ unitRootCount (pPolynomial 11 10 a) := by
  have h := alpha_unique ha.1 heq
  simpa only [h] using counterexample_root_count

/-- The universal two-root assertion fails even on positive coprime pairs. -/
theorem wakhare_conjecture_two_false :
    ¬ (∀ k r : ℕ, 0 < r → r < k → Nat.Coprime k r →
      ∀ a : ℝ, a ∈ Set.Ioo 0 1 → a^r * (1+a)^(k-r) = 1 →
        unitRootCount (pPolynomial k r a) = 2) := by
  intro hc
  apply counterexample_not_two
  apply hc 11 10 (by norm_num) (by norm_num) (by decide) alpha
    ⟨alpha_pos, alpha_lt_one⟩
  simpa using alpha_equation

end EntropyCounterexample
