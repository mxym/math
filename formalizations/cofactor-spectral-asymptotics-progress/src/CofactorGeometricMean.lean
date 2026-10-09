import CofactorFiniteEntropy

/-! A direct shifted-sum proof of the mean-index estimate for geometric separation. -/
set_option autoImplicit false
open scoped BigOperators
namespace CofactorSpectral
noncomputable section

theorem geometrically_separated_mean_bound (n : ℕ) (b : ℝ) (hb : 1 < b)
    (p : Fin (n+1) → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (hsep : ∀ i : Fin n, b * p i.succ ≤ p i.castSucc) :
    (∑ i, (i.val : ℝ) * p i) ≤ 1/(b-1) := by
  have hshift : (∑ i : Fin (n+1), (i.val : ℝ) * p i) =
      ∑ i : Fin n, ((i.val : ℝ)+1) * p i.succ := by
    rw [Fin.sum_univ_succ]
    simp [Nat.cast_add,Nat.cast_one]
  have htotal : (∑ i : Fin (n+1), ((i.val : ℝ)+1) * p i) =
      (∑ i, (i.val : ℝ) * p i) + 1 := by
    simp_rw [add_mul,one_mul,Finset.sum_add_distrib]
    rw [hs]
  have hprefix : (∑ i : Fin n, ((i.val : ℝ)+1) * p i.castSucc) ≤
      (∑ i : Fin (n+1), ((i.val : ℝ)+1) * p i) := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last]
    have hlast : 0 ≤ ((n : ℝ)+1)*p (Fin.last n) := mul_nonneg (by positivity) (hp _)
    linarith
  have hmul : b * (∑ i : Fin (n+1), (i.val : ℝ)*p i) ≤
      (∑ i : Fin (n+1), (i.val : ℝ)*p i) + 1 := by
    rw [hshift,Finset.mul_sum]
    calc
      _ ≤ ∑ i : Fin n, ((i.val : ℝ)+1) * p i.castSucc := by
        apply Finset.sum_le_sum
        intro i _
        have h := mul_le_mul_of_nonneg_left (hsep i)
          (show (0 : ℝ) ≤ (i.val : ℝ)+1 by positivity)
        nlinarith
      _ ≤ _ := by simpa only [hshift] using hprefix.trans_eq htotal
  apply (le_div_iff₀ (sub_pos.mpr hb)).mpr
  nlinarith

end
end CofactorSpectral
