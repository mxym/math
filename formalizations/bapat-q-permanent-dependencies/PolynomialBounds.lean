import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Data.Fintype.BigOperators

open scoped BigOperators
open Set

namespace BapatBounds

def realPolynomial {ι : Type*} [Fintype ι] (e : ι → ℕ) (c : ι → ℝ)
    (q : ℝ) : ℝ := ∑ i, q ^ e i * c i

def realDerivative {ι : Type*} [Fintype ι] (e : ι → ℕ) (c : ι → ℝ)
    (q : ℝ) : ℝ := ∑ i, (e i : ℝ) * q ^ (e i - 1) * c i

theorem realPolynomial_hasDerivAt {ι : Type*} [Fintype ι]
    (e : ι → ℕ) (c : ι → ℝ) (q : ℝ) :
    HasDerivAt (realPolynomial e c) (realDerivative e c q) q := by
  unfold realPolynomial realDerivative
  apply HasDerivAt.fun_sum
  intro i hi
  simpa using ((hasDerivAt_id q).pow (e i)).mul_const (c i)

theorem realPolynomial_deriv {ι : Type*} [Fintype ι]
    (e : ι → ℕ) (c : ι → ℝ) (q : ℝ) :
    deriv (realPolynomial e c) q = realDerivative e c q :=
  (realPolynomial_hasDerivAt e c q).deriv

theorem abs_pow_sub_one_bound (q : ℝ) (m : ℕ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    |q ^ m - 1| ≤ (m : ℝ) * (1 - q) := by
  have hpow : ∀ m : ℕ, 1 - q ^ m ≤ (m : ℝ) * (1 - q) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
      have hd : 0 ≤ 1 - q := sub_nonneg.mpr hq1
      have hmul : q * (1 - q ^ m) ≤ q * ((m : ℝ) * (1 - q)) :=
        mul_le_mul_of_nonneg_left ih hq0
      have hle : q * ((m : ℝ) * (1 - q)) ≤ (m : ℝ) * (1 - q) :=
        mul_le_of_le_one_left (mul_nonneg hm hd) hq1
      rw [pow_succ, Nat.cast_succ]
      nlinarith
  rw [abs_of_nonpos (sub_nonpos.mpr (pow_le_one₀ hq0 hq1))]
  simpa only [neg_sub] using hpow m

/-- Uniform derivative variation for a finite polynomial, with natural exponents.
The bound includes exponents zero and one; truncated subtraction is intentional. -/
theorem realDerivative_difference_bound {ι : Type*} [Fintype ι]
    (e : ι → ℕ) (c : ι → ℝ) (N : ℕ) (M q : ℝ)
    (hM : 0 ≤ M) (he : ∀ i, e i ≤ N) (hc : ∀ i, |c i| ≤ M)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    |realDerivative e c q - realDerivative e c 1| ≤
      (Fintype.card ι : ℝ) * (N : ℝ) * ((N - 1 : ℕ) : ℝ) * M * (1 - q) := by
  classical
  have hdelta : 0 ≤ 1 - q := sub_nonneg.mpr hq1
  have hterm (i : ι) :
      |(e i : ℝ) * q ^ (e i - 1) * c i - (e i : ℝ) * 1 ^ (e i - 1) * c i| ≤
        (N : ℝ) * ((N - 1 : ℕ) : ℝ) * M * (1 - q) := by
    have he0 : 0 ≤ (e i : ℝ) := Nat.cast_nonneg _
    have heb : (e i : ℝ) * ((e i - 1 : ℕ) : ℝ) ≤
        (N : ℝ) * ((N - 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_le_mul (he i) (Nat.sub_le_sub_right (he i) 1)
    have hx : |q ^ (e i - 1) - 1| ≤ ((e i - 1 : ℕ) : ℝ) * (1 - q) :=
      abs_pow_sub_one_bound q _ hq0 hq1
    have heq : (e i : ℝ) * q ^ (e i - 1) * c i - (e i : ℝ) * 1 ^ (e i - 1) * c i =
        (e i : ℝ) * (q ^ (e i - 1) - 1) * c i := by simp; ring
    rw [heq, abs_mul, abs_mul, abs_of_nonneg he0]
    calc
      _ ≤ (e i : ℝ) * (((e i - 1 : ℕ) : ℝ) * (1 - q)) * M :=
        mul_le_mul (mul_le_mul_of_nonneg_left hx he0) (hc i) (abs_nonneg _)
          (mul_nonneg he0 (mul_nonneg (Nat.cast_nonneg _) hdelta))
      _ = ((e i : ℝ) * ((e i - 1 : ℕ) : ℝ)) * (M * (1 - q)) := by ring
      _ ≤ ((N : ℝ) * ((N - 1 : ℕ) : ℝ)) * (M * (1 - q)) :=
        mul_le_mul_of_nonneg_right heb (mul_nonneg hM hdelta)
      _ = _ := by ring
  unfold realDerivative
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |(e i : ℝ) * q ^ (e i - 1) * c i -
        (e i : ℝ) * 1 ^ (e i - 1) * c i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, (N : ℝ) * ((N - 1 : ℕ) : ℝ) * M * (1 - q) :=
      Finset.sum_le_sum (fun i _ => hterm i)
    _ = _ := by simp [mul_assoc]

/-- An explicit interval witnessing failure of monotonicity. The hypotheses
are derivative and variation bounds, not an assumed optimizer or conclusion. -/
theorem explicit_reverse_interval (f g : ℝ → ℝ) (K : ℝ) (hK : 1 ≤ K)
    (hd : ∀ q, HasDerivAt f (g q) q) (h1 : g 1 ≤ -(1 / 4 : ℝ))
    (hvariation : ∀ q ∈ Icc (0 : ℝ) 1, |g q - g 1| ≤ K * (1 - q)) :
    let h := 1 / (8 * K)
    let q₀ := 1 - h
    0 < q₀ ∧ q₀ < 1 ∧ h / 8 ≤ f q₀ - f 1 ∧ f 1 < f q₀ := by
  dsimp
  have hKp : 0 < K := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hK
  have hh : 0 < 1 / (8 * K) := by positivity
  have hh1 : 1 / (8 * K) ≤ (1 / 8 : ℝ) := by
    apply one_div_le_one_div_of_le
    · norm_num
    · linarith
  have hq0 : 0 < 1 - 1 / (8 * K) := by linarith
  have hq1 : 1 - 1 / (8 * K) < 1 := by linarith
  have hk : K * (1 / (8 * K)) = (1 / 8 : ℝ) := by field_simp
  have hder : ∀ q ∈ Icc (1 - 1 / (8 * K)) 1, deriv f q ≤ -(1 / 8 : ℝ) := by
    intro q hq
    rw [(hd q).deriv]
    have hnonneg : 0 ≤ q := hq0.le.trans hq.1
    have hv := hvariation q ⟨hnonneg, hq.2⟩
    have hup := (abs_le.mp hv).2
    have hbound : K * (1 - q) ≤ K * (1 / (8 * K)) := by
      apply mul_le_mul_of_nonneg_left _ hKp.le
      linarith [hq.1]
    linarith
  have hdiff : Differentiable ℝ f := fun q => (hd q).differentiableAt
  have hs := (convex_Icc (1 - 1 / (8 * K)) (1 : ℝ)).image_sub_le_mul_sub_of_deriv_le
    hdiff.continuous.continuousOn hdiff.differentiableOn
    (fun q hq => hder q (interior_subset hq))
    (1 - 1 / (8 * K)) ⟨le_rfl, hq1.le⟩ 1 ⟨hq1.le, le_rfl⟩ hq1.le
  refine ⟨hq0, hq1, ?_, ?_⟩
  · linarith
  · have hh8 : 0 < 1 / (8 * K) / 8 := by positivity
    linarith

end BapatBounds
