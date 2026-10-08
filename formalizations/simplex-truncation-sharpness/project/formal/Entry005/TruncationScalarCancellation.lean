import Entry005.TruncationFacetDeterminants
import Entry005.TruncationRationalDefect

/-! Pure scalar cancellation of the proved ordered facet determinant sums.
This module does not assert a geometric formula for entryDefect. -/

noncomputable section
open scoped BigOperators

namespace Entry005

def truncationScalarHorizontalSum (d : ℕ) (t : ℝ) : ℝ :=
  (d.factorial : ℝ) * (1 / ((d - 1).factorial : ℝ)) ^ d *
    ((1 - t ^ (d - 1)) ^ d +
      (d : ℝ) * (1 + t ^ (d - 1)) * (1 - t ^ (d - 1)) ^ (d - 1))

def truncationScalarLiftedSum (d : ℕ) (t : ℝ) : ℝ :=
  ((d + 1).factorial : ℝ) * (1 / ((d - 1).factorial : ℝ)) ^ (d + 1) *
    ((1 - t ^ (d - 1)) ^ d * (1 + t ^ d) +
      (d : ℝ) * (1 - t ^ (d - 1)) ^ (d - 1) * (t ^ (d - 1) - t ^ d))

theorem truncation_scalar_cancellation {d : ℕ} (hd : 2 ≤ d)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    truncationScalarLiftedSum d t /
        ((d + 1 : ℝ) * (d : ℝ) * ((1 - t ^ d) / (d.factorial : ℝ)) *
          truncationScalarHorizontalSum d t) - 1 / (d + 1 : ℝ) =
      truncationRationalDefect d t := by
  let c : ℝ := 1 / ((d - 1).factorial : ℝ)
  let q : ℝ := t ^ (d - 1)
  let s : ℝ := t ^ d
  let r : ℝ := 1 - q
  let B₀ : ℝ := r + (d : ℝ) * (1 + q)
  let B₁ : ℝ := r * (1 + s) + (d : ℝ) * (q - s)
  have hd0 : 0 < d := by omega
  have hd1 : 0 < d - 1 := by omega
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd0
  have hdp : 0 < (d + 1 : ℝ) := by positivity
  have hf : 0 < (d.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos d
  have hfm : 0 < ((d - 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (d - 1)
  have hc : 0 < c := div_pos zero_lt_one hfm
  have hq : 0 < q := pow_pos ht _
  have hr : 0 < r := by
    exact sub_pos.mpr (pow_lt_one₀ ht.le ht1 hd1.ne')
  have hs : 0 < 1 - s := by
    exact sub_pos.mpr (pow_lt_one₀ ht.le ht1 hd0.ne')
  have hB₀ : 0 < B₀ := by dsimp [B₀]; positivity
  have hcf : c * (d.factorial : ℝ) = (d : ℝ) := by
    have hn : d - 1 + 1 = d := by omega
    have hfact : (d.factorial : ℝ) = (d : ℝ) * ((d - 1).factorial : ℝ) := by
      have hh := congrArg (fun n : ℕ => (n : ℝ)) (Nat.factorial_succ (d - 1))
      simpa only [hn, Nat.cast_mul] using hh
    rw [hfact]
    dsimp [c]
    field_simp [hfm.ne']
  have hM : (d : ℝ) * ((1 - s) / (d.factorial : ℝ)) = c * (1 - s) := by
    rw [← hcf]
    field_simp [hf.ne']
  have hrpow : r ^ d = r ^ (d - 1) * r := by
    have hn : d - 1 + 1 = d := by omega
    rw [← pow_succ, hn]
  have hH : truncationScalarHorizontalSum d t =
      (d.factorial : ℝ) * c ^ d * r ^ (d - 1) * B₀ := by
    change (d.factorial : ℝ) * c ^ d *
      (r ^ d + (d : ℝ) * (1 + q) * r ^ (d - 1)) = _
    rw [hrpow]
    dsimp [B₀]
    ring
  have hL : truncationScalarLiftedSum d t =
      (d + 1 : ℝ) * c * (d.factorial : ℝ) * c ^ d * r ^ (d - 1) * B₁ := by
    change ((d + 1).factorial : ℝ) * c ^ (d + 1) *
      (r ^ d * (1 + s) + (d : ℝ) * r ^ (d - 1) * (q - s)) = _
    rw [hrpow, pow_succ, Nat.factorial_succ]
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    dsimp [B₁]
    ring
  have hratio : truncationScalarLiftedSum d t /
      ((d + 1 : ℝ) * (d : ℝ) * ((1 - s) / (d.factorial : ℝ)) *
        truncationScalarHorizontalSum d t) = B₁ / ((1 - s) * B₀) := by
    rw [hH, hL]
    rw [show (d + 1 : ℝ) * (d : ℝ) * ((1 - s) / (d.factorial : ℝ)) =
      (d + 1 : ℝ) * (c * (1 - s)) by rw [mul_assoc, hM]]
    field_simp [hdp.ne', hf.ne', hc.ne', hr.ne', hs.ne', hB₀.ne']
  change truncationScalarLiftedSum d t /
    ((d + 1 : ℝ) * (d : ℝ) * ((1 - s) / (d.factorial : ℝ)) *
      truncationScalarHorizontalSum d t) - 1 / (d + 1 : ℝ) = _
  rw [hratio]
  have hB₀form : B₀ = (d + 1 : ℝ) + (d - 1 : ℝ) * q := by
    dsimp [B₀, r]
    ring
  have hst : s = t * q := by
    have hn : d - 1 + 1 = d := by omega
    dsimp [s, q]
    have hp : t ^ d = t ^ (d - 1) * t := by
      simpa only [hn] using pow_succ t (d - 1)
    exact hp.trans (mul_comm _ _)
  change B₁ / ((1 - s) * B₀) - 1 / (d + 1 : ℝ) =
    q * ((d : ℝ) * (d - 1) - (d + 1) * (d - 2) * t - 2 * s) /
      ((d + 1) * (1 - s) * ((d + 1) + (d - 1) * q))
  rw [← hB₀form]
  field_simp [hdp.ne', hs.ne', hB₀.ne']
  dsimp [B₁, B₀, r]
  rw [hst]
  ring

#print axioms truncation_scalar_cancellation

end Entry005
