import APPTReview.PlateauOptimizer

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

/-- A rounded displacement in [0,1] uniquely minimizes the squared fractional
distance on its integer lattice, even though the denominator is asymmetric. -/
theorem fractional_rounding_strict (H s d : ℝ) (hH : 0 < H)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hd : 0 < H+d)
    (hsep : d ≤ s-2 ∨ s+2 ≤ d) :
    s^2/(H+s)^2 < d^2/(H+d)^2 := by
  have hHs : 0 < H+s := by linarith
  have hleft : 0 ≤ s/(H+s) := div_nonneg hs hHs.le
  have hright : 0 ≤ |d|/(H+d) := div_nonneg (abs_nonneg _) hd.le
  have hratio : s/(H+s) < |d|/(H+d) := by
    apply (div_lt_div_iff₀ hHs hd).2
    rcases hsep with hlo | hhi
    · have hdneg : d < 0 := by linarith
      rw [abs_of_neg hdneg]
      have hds : 0 ≤ -(d+s) := by linarith
      have hprod := mul_nonneg hH.le hds
      by_cases hs0 : s=0
      · subst s
        have hp := mul_pos (neg_pos.mpr hdneg) hH
        nlinarith
      · have hsp : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
        have hp := mul_pos hsp (neg_pos.mpr hdneg)
        nlinarith
    · have hdn : 0 ≤ d := by linarith
      rw [abs_of_nonneg hdn]
      have hp := mul_pos hH (show 0 < d-s by linarith)
      nlinarith
  have hsq : (s/(H+s))^2 < (|d|/(H+d))^2 := by nlinarith
  simpa only [div_pow,sq_abs] using hsq

/-- Every rank other than the ceiling rank is strictly suboptimal inside
the complete projection-plateau family. Both parities are included. -/
theorem plateauScaledPurity_lt_ceiling {m n k : ℕ} (hm : 2 ≤ m) (hn : 0 < n)
    (hk : k ≠ ((m-1)*n+1)/2) :
    plateauScaledPurity m n k < plateauScaledPurity m n (((m-1)*n+1)/2) := by
  let t := ((m-1)*n+1)/2
  let H : ℝ := ((m:ℝ)^2-1)*n
  let s : ℝ := 2*(t:ℝ)-((m:ℝ)-1)*n
  let d : ℝ := 2*(k:ℝ)-((m:ℝ)-1)*n
  let C : ℝ := (m:ℝ)^2/((m:ℝ)^2-1)
  have hmR : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hmP : (0:ℝ) < m := by linarith
  have hbase : (0:ℝ) < (m:ℝ)^2-1 := by nlinarith
  have hC : 0 < C := div_pos (sq_pos_of_pos hmP) hbase
  have hH : 0 < H := mul_pos hbase hnR
  have hnat : (m-1)*n ≤ 2*t ∧ 2*t ≤ (m-1)*n+1 := by dsimp [t]; omega
  have hcast : (((m-1)*n:ℕ):ℝ)=((m:ℝ)-1)*n := by
    rw [Nat.cast_mul,Nat.cast_sub (by omega : 1 ≤ m),Nat.cast_one]
  have h0 : ((m:ℝ)-1)*n ≤ 2*(t:ℝ) := by rw [← hcast]; exact_mod_cast hnat.1
  have h1 : 2*(t:ℝ) ≤ ((m:ℝ)-1)*n+1 := by rw [← hcast]; exact_mod_cast hnat.2
  have hs : 0 ≤ s := by dsimp [s]; linarith
  have hs1 : s ≤ 1 := by dsimp [s]; linarith
  have hZ (j : ℕ) : 0 < (m:ℝ)*n*((m:ℝ)-1)+2*(j:ℝ) := by
    have hsub : (0:ℝ) < (m:ℝ)-1 := by linarith
    positivity
  have hek : H+d=(m:ℝ)*n*((m:ℝ)-1)+2*(k:ℝ) := by dsimp [H,d]; ring
  have het : H+s=(m:ℝ)*n*((m:ℝ)-1)+2*(t:ℝ) := by dsimp [H,s]; ring
  have hd : 0 < H+d := by rw [hek]; exact hZ k
  have hsep : d ≤ s-2 ∨ s+2 ≤ d := by
    rcases lt_or_gt_of_ne (show k≠t from hk) with hkt | htk
    · left
      have ht : (k:ℝ)+1 ≤ t := by exact_mod_cast (show k+1 ≤ t by omega)
      dsimp [d,s]
      linarith
    · right
      have ht : (t:ℝ)+1 ≤ k := by exact_mod_cast (show t+1 ≤ k by omega)
      dsimp [d,s]
      linarith
  have hdif := fractional_rounding_strict H s d hH hs hs1 hd hsep
  have hmul := mul_lt_mul_of_pos_left hdif hC
  have hid (j : ℕ) := plateau_rounding_identity (m:ℝ) (n:ℝ) (j:ℝ)
    (ne_of_gt hbase) (ne_of_gt (hZ j))
  have hidk : C-plateauScaledPurity m n k=C*(d^2/(H+d)^2) := by
    rw [hek]
    simpa only [C,d,plateauScaledPurity,plateauDenominator,mul_div_assoc] using hid k
  have hidt : C-plateauScaledPurity m n t=C*(s^2/(H+s)^2) := by
    rw [het]
    simpa only [C,s,plateauScaledPurity,plateauDenominator,mul_div_assoc] using hid t
  change plateauScaledPurity m n k < plateauScaledPurity m n t
  linarith

/-- The ceiling is the unique integer maximizing rank, not a freely chosen
rounding of the continuous optimizer. This statement ranges over all naturals. -/
theorem plateauScaledPurity_ceiling_unique {m n : ℕ} (hm : 2 ≤ m) (hn : 0 < n)
    (k : ℕ) :
    plateauScaledPurity m n k ≤ plateauScaledPurity m n (((m-1)*n+1)/2) ∧
    (plateauScaledPurity m n k=plateauScaledPurity m n (((m-1)*n+1)/2) ↔
      k=((m-1)*n+1)/2) := by
  by_cases hk : k=((m-1)*n+1)/2
  · subst k
    simp
  · have hs := plateauScaledPurity_lt_ceiling hm hn hk
    exact ⟨hs.le,⟨fun he => (ne_of_lt hs he).elim,fun he => (hk he).elim⟩⟩

end APPTReview
