import Mathlib.Tactic

open Set Filter Topology

/-!
Discrete ascent core for a mountain-pass deformation.  The analytic input is
only the one-step monotonicity/gain estimate; no ODE or Gaussian statement is
used here.
-/

theorem iterate_gain_of_strip
    {b η c : ℝ} (hη : 0 < η) (hc : 0 < c)
    (x : ℕ → ℝ)
    (hmono : ∀ n, x n ≤ x (n + 1))
    (hgain : ∀ n, b - η ≤ x n → x n ≤ b + η → x n + c ≤ x (n + 1))
    (hstart : b - η / 2 < x 0)
    {N : ℕ} (hN : 2 * η / c ≤ N) :
    b + η / 2 ≤ x N := by
  by_contra hbad
  have hmono_le : ∀ {i j : ℕ}, i ≤ j → x i ≤ x j := by
    intro i j hij
    exact monotone_nat_of_le_succ hmono hij
  have hbelow : ∀ n ≤ N, x n < b + η / 2 := by
    intro n hn
    linarith [hmono_le hn]
  have hstrip : ∀ n ≤ N, b - η ≤ x n := by
    intro n hn
    exact le_trans (by linarith [hstart]) (hmono_le (Nat.zero_le n))
  have hstep : ∀ n ≤ N, x 0 + n * c ≤ x n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        intro hn
        have hnN : n ≤ N := Nat.le_trans (Nat.le_succ n) hn
        have hgn := hgain n (hstrip n hnN)
          (by linarith [hbelow n hnN])
        have hi := ih (Nat.le_trans (Nat.le_succ n) hn)
        norm_num [Nat.cast_succ, add_assoc] at *
        nlinarith
  have hNstep := hstep N (le_rfl)
  have hNreal : 2 * η ≤ (N : ℝ) * c := (div_le_iff₀ hc).mp hN
  nlinarith

theorem iterate_gain_of_strip_le
    {b η c : ℝ} (hη : 0 < η) (hc : 0 < c)
    (x : ℕ → ℝ)
    (hmono : ∀ n, x n ≤ x (n + 1))
    (hgain : ∀ n, b - η ≤ x n → x n ≤ b + η → x n + c ≤ x (n + 1))
    (hstart : b - η / 2 < x 0)
    {N : ℕ} (hN : 2 * η / c ≤ N) :
    b + η / 2 ≤ x N := by
  exact iterate_gain_of_strip hη hc x hmono hgain hstart hN

/- The same result in the form used by a discrete deformation: the only
analytic obligations are preservation of K, monotonicity, and the one-step
strip gain. -/
theorem iterate_map_gain_of_strip
    {X : Type*} (K : Set X) (f : X → ℝ) (T : X → X) {b η c : ℝ}
    (hη : 0 < η) (hc : 0 < c)
    (hTK : ∀ x, x ∈ K → T x ∈ K)
    (hmono : ∀ x, x ∈ K → f x ≤ f (T x))
    (hgain : ∀ x, x ∈ K → b - η ≤ f x → f x ≤ b + η →
      f x + c ≤ f (T x))
    (x₀ : X) (hx₀ : x₀ ∈ K) (hstart : b - η / 2 < f x₀)
    {N : ℕ} (hN : 2 * η / c ≤ N) :
    b + η / 2 ≤ f ((T^[N]) x₀) := by
  have hK : ∀ n : ℕ, (T^[n]) x₀ ∈ K := by
    intro n
    induction n with
    | zero => simpa using hx₀
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact hTK _ ih
  let x : ℕ → ℝ := fun n => f ((T^[n]) x₀)
  have hxm : ∀ n, x n ≤ x (n + 1) := by
    intro n
    change f ((T^[n]) x₀) ≤ f ((T^[n + 1]) x₀)
    rw [Function.iterate_succ_apply']
    exact hmono _ (hK n)
  have hxg : ∀ n, b - η ≤ x n → x n ≤ b + η → x n + c ≤ x (n + 1) := by
    intro n hlo hhi
    change b - η ≤ f ((T^[n]) x₀) at hlo
    change f ((T^[n]) x₀) ≤ b + η at hhi
    change f ((T^[n]) x₀) + c ≤ f ((T^[n + 1]) x₀)
    rw [Function.iterate_succ_apply']
    exact hgain _ (hK n) hlo hhi
  have h := iterate_gain_of_strip hη hc x hxm hxg hstart hN
  simpa [x] using h

