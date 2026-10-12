import CofactorFiniteLowerThreshold

/-! The actual integer ceiling recurrence, its geometric separation and prefix bounds. -/
set_option autoImplicit false
open scoped BigOperators
namespace CofactorSpectral
noncomputable section

def ringDegreeSequence (b : ℝ) (m : ℕ) : ℕ → ℕ :=
  Nat.rec m (fun _ d => Nat.ceil (b*(d : ℝ)))

theorem ringDegreeSequence_pos (b : ℝ) (hb : 1 < b) (m : ℕ) (hm : 0 < m) (k : ℕ) :
    0 < ringDegreeSequence b m k := by
  induction k with
  | zero => exact hm
  | succ k ih =>
    exact Nat.ceil_pos.mpr (mul_pos (by linarith) (by exact_mod_cast ih))

theorem ringDegreeSequence_step (b : ℝ) (m k : ℕ) :
    b*(ringDegreeSequence b m k : ℝ) ≤ (ringDegreeSequence b m (k+1) : ℝ) :=
  Nat.le_ceil _

theorem ringDegreeSequence_strictMono (b : ℝ) (hb : 1 < b) (m : ℕ) (hm : 0 < m) :
    StrictMono (ringDegreeSequence b m) := by
  apply strictMono_nat_of_lt_succ
  intro k
  have hp : (0 : ℝ) < ringDegreeSequence b m k := by
    exact_mod_cast ringDegreeSequence_pos b hb m hm k
  have hs := ringDegreeSequence_step b m k
  have ht : (ringDegreeSequence b m k : ℝ) < ringDegreeSequence b m (k+1) := by nlinarith
  exact_mod_cast ht

theorem ringDegreeSequence_min (b : ℝ) (hb : 1 < b) (m : ℕ) (hm : 0 < m) (k : ℕ) :
    m ≤ ringDegreeSequence b m k :=
  (ringDegreeSequence_strictMono b hb m hm).monotone (Nat.zero_le k)

theorem ringDegreeSequence_separation (b : ℝ) (hb : 1 < b) (m : ℕ) (hm : 0 < m)
    (i j : ℕ) (hij : i < j) :
    b*(ringDegreeSequence b m i : ℝ) ≤ (ringDegreeSequence b m j : ℝ) := by
  have hs : ringDegreeSequence b m (i+1) ≤ ringDegreeSequence b m j :=
    (ringDegreeSequence_strictMono b hb m hm).monotone (Nat.succ_le_of_lt hij)
  exact (ringDegreeSequence_step b m i).trans (by exact_mod_cast hs)

theorem ringDegreeSequence_upper_shift (b : ℝ) (hb : 1 < b) (m : ℕ) (hm : 0 < m)
    (k : ℕ) :
    (ringDegreeSequence b m k : ℝ)+1/(b-1) ≤ ((m : ℝ)+1/(b-1))*b^k := by
  have hb0 : 0 < b := by linarith
  have hc : b*(1/(b-1)) = 1+1/(b-1) := by
    field_simp [ne_of_gt (sub_pos.mpr hb)]
    <;> ring
  induction k with
  | zero =>
    change (m : ℝ)+1/(b-1) ≤ ((m : ℝ)+1/(b-1))*b^0
    simp
  | succ k ih =>
    have hp : (0 : ℝ) < ringDegreeSequence b m k := by
      exact_mod_cast ringDegreeSequence_pos b hb m hm k
    have hceil : (ringDegreeSequence b m (k+1) : ℝ) ≤ b*(ringDegreeSequence b m k : ℝ)+1 :=
      (Nat.ceil_lt_add_one (mul_pos hb0 hp).le).le
    calc
      _ ≤ b*(ringDegreeSequence b m k : ℝ)+1+1/(b-1) := by linarith
      _ = b*((ringDegreeSequence b m k : ℝ)+1/(b-1)) := by rw [mul_add,hc]; ring
      _ ≤ b*(((m : ℝ)+1/(b-1))*b^k) := mul_le_mul_of_nonneg_left ih hb0.le
      _ = _ := by rw [pow_succ]; ring

theorem geometric_prefix_upper (b : ℝ) (hb : 1 < b) (K : ℕ) :
    (∑ k ∈ Finset.range K, b^k) ≤ b^K/(b-1) := by
  have he : (b-1)*(∑ k ∈ Finset.range K, b^k) = b^K-1 := by
    induction K with
    | zero => simp
    | succ K ih => rw [Finset.sum_range_succ,pow_succ]; nlinarith only [ih]
  apply (le_div_iff₀ (sub_pos.mpr hb)).2
  nlinarith only [he]

theorem ringDegreeSequence_prefix_upper (b : ℝ) (hb : 1 < b) (m : ℕ) (hm : 0 < m)
    (K : ℕ) :
    ((∑ k ∈ Finset.range K, ringDegreeSequence b m k : ℕ) : ℝ) ≤
      (((m : ℝ)+1/(b-1))/(b-1))*b^K := by
  have hb1 : 0 < b-1 := sub_pos.mpr hb
  have hD : 0 ≤ (m : ℝ)+1/(b-1) := by positivity
  have hu : ∀ k, (ringDegreeSequence b m k : ℝ) ≤ ((m : ℝ)+1/(b-1))*b^k := by
    intro k
    have h := ringDegreeSequence_upper_shift b hb m hm k
    have hc : 0 ≤ 1/(b-1) := by positivity
    linarith
  rw [Nat.cast_sum]
  calc
    _ ≤ ∑ k ∈ Finset.range K, ((m : ℝ)+1/(b-1))*b^k :=
      Finset.sum_le_sum (fun k _ => hu k)
    _ = ((m : ℝ)+1/(b-1))*(∑ k ∈ Finset.range K, b^k) := (Finset.mul_sum _ _ _).symm
    _ ≤ ((m : ℝ)+1/(b-1))*(b^K/(b-1)) :=
      mul_le_mul_of_nonneg_left (geometric_prefix_upper b hb K) hD
    _ = _ := by ring

end
end CofactorSpectral
