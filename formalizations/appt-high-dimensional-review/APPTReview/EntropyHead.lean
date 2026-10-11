import APPTReview.LogBounds
import APPTReview.Star

open scoped BigOperators
namespace APPTReview

noncomputable def entropyGap (x : ℝ) : ℝ := x^2/2 - entropyKernel x

theorem entropyGap_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ entropyGap x := by
  have h := entropy_positive_gap_bound hx
  have hq : 0 ≤ x^3/(3*(x+2)) := by positivity
  exact hq.trans h

theorem entropy_negative_bounded {z y : ℝ} (hz : 0 ≤ z) (hzy : z ≤ y)
    (hy : y ≤ 1) : entropyKernel (-z) ≤ (1/(2-y))*z^2 := by
  have hden : 0 < 2-y := by linarith
  have hd : 2-y ≤ 2-z := by linarith
  calc
    entropyKernel (-z) ≤ z^2/(2-z) := entropy_negative_bound hz (hzy.trans hy)
    _ ≤ z^2/(2-y) := div_le_div_of_nonneg_left (sq_nonneg z) hden hd
    _ = (1/(2-y))*z^2 := by ring

noncomputable def entropyHead {n : ℕ} (a : Fin (n+1) → ℝ)
    (β : Fin (n+2) → ℝ) : ℝ :=
  (∑ i, (entropyKernel (a i)+a i*β i.castSucc)) + ∑ i, entropyKernel (-β i)

/-- Exact bound before the last scalar split; no logarithmic head estimate is assumed. -/
theorem entropyHead_prebound {n : ℕ} (a : Fin (n+1) → ℝ) (β : Fin (n+2) → ℝ)
    (ha : ∀ i, 0 ≤ a i) (ha0 : ∀ i, a i ≤ a 0)
    (hβ : ∀ i, 0 ≤ β i) (hβanti : Antitone β) (hy : β 0 ≤ 1)
    (hstar : (∑ i : Fin (n+1), (a i+β i.succ)^2) ≤ 4*(1-β 0)) :
    entropyHead a β ≤ 2 + β 0*(a 0-1)-entropyGap (a 0) := by
  let c : ℝ := 1/(2-β 0)
  have hden : 0 < 2-β 0 := by linarith
  have hc : (1/2 : ℝ) ≤ c := by
    dsimp [c]
    apply (le_div_iff₀ hden).2
    linarith [hβ 0]
  have hc0 : 0 ≤ c := by linarith
  have hbtop (i : Fin (n+2)) : β i ≤ β 0 := hβanti (Fin.zero_le i)
  have hn (i : Fin (n+2)) : entropyKernel (-β i) ≤ c*(β i)^2 :=
    entropy_negative_bounded (hβ i) (hbtop i) hy
  have hterm (i : Fin (n+1)) :
      entropyKernel (a i) + a i*β i.succ + entropyKernel (-β i.succ) + entropyGap (a i)
        ≤ c*(a i+β i.succ)^2 := by
    have hp := mul_nonneg (ha i) (hβ i.succ)
    have hh := mul_nonneg (show 0 ≤ c-1/2 by linarith)
      (show 0 ≤ (a i)^2+2*a i*β i.succ by nlinarith [sq_nonneg (a i)])
    dsimp [entropyGap]
    nlinarith [hn i.succ]
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hterm i)
  rw [← Finset.mul_sum] at hsum
  simp only [Finset.sum_add_distrib] at hsum
  have hdiff : (∑ i : Fin (n+1), (β i.castSucc-β i.succ)) =
      β 0 - β (Fin.last (n+1)) := by
    rw [Finset.sum_sub_distrib]
    have h1 := Fin.sum_univ_castSucc β
    have h2 := Fin.sum_univ_succ β
    linarith
  have htel : (∑ i : Fin (n+1), a i*(β i.castSucc-β i.succ)) ≤ a 0*β 0 := by
    calc
      _ ≤ ∑ i : Fin (n+1), a 0*(β i.castSucc-β i.succ) := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_right (ha0 i)
          (sub_nonneg.mpr (hβanti (by change i.val ≤ i.val+1; omega : i.castSucc ≤ i.succ)))
      _ = a 0*(β 0-β (Fin.last (n+1))) := by rw [← Finset.mul_sum, hdiff]
      _ ≤ _ := by nlinarith [mul_nonneg (ha 0) (hβ (Fin.last (n+1)))]
  have hsplit : (∑ i : Fin (n+1), a i*β i.castSucc) =
      (∑ i : Fin (n+1), a i*β i.succ) +
        ∑ i : Fin (n+1), a i*(β i.castSucc-β i.succ) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hgap : entropyGap (a 0) ≤ ∑ i : Fin (n+1), entropyGap (a i) := by
    exact Finset.single_le_sum (fun i _ => entropyGap_nonneg (ha i)) (Finset.mem_univ 0)
  have hbudget := mul_le_mul_of_nonneg_left hstar hc0
  have hcancel : c*(4*(1-β 0)+(β 0)^2)=2-β 0 := by
    dsimp [c]
    field_simp
    ring
  dsimp [entropyHead]
  rw [Fin.sum_univ_succ (fun i : Fin (n+2) => entropyKernel (-β i))]
  simp only [Finset.sum_add_distrib]
  nlinarith [hn 0]

/-- The complete nonlinear exceptional-head estimate from the reviewed entropy proof. -/
theorem entropyHead_le_two {n : ℕ} (a : Fin (n+1) → ℝ) (β : Fin (n+2) → ℝ)
    (ha : ∀ i, 0 ≤ a i) (ha0 : ∀ i, a i ≤ a 0)
    (hβ : ∀ i, 0 ≤ β i) (hβanti : Antitone β) (hy : β 0 ≤ 1)
    (hstar : (∑ i : Fin (n+1), (a i+β i.succ)^2) ≤ 4*(1-β 0)) :
    entropyHead a β ≤ 2 := by
  have hp := entropyHead_prebound a β ha ha0 hβ hβanti hy hstar
  by_cases hsmall : a 0 ≤ 1
  · have hg := entropyGap_nonneg (ha 0)
    have hc := mul_nonpos_of_nonneg_of_nonpos (hβ 0) (by linarith : a 0-1 ≤ 0)
    linarith
  · have hlow : 1 ≤ a 0 := le_of_lt (lt_of_not_ge hsmall)
    have he : (a 0+β (0 : Fin (n+1)).succ)^2 ≤
        ∑ i : Fin (n+1), (a i+β i.succ)^2 := by
      exact Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => sq_nonneg (a i+β i.succ)) (Finset.mem_univ (0 : Fin (n+1)))
    have hprod := mul_nonneg (ha 0) (hβ (0 : Fin (n+1)).succ)
    have hs : (a 0)^2 ≤ 4*(1-β 0) := by
      nlinarith [sq_nonneg (β (0 : Fin (n+1)).succ)]
    have hu : a 0 ≤ 2 := by nlinarith [hβ 0]
    have hm := entropy_head_outlier_margin hlow hu
    have hc := mul_le_mul_of_nonneg_right
      (show β 0 ≤ 1-(a 0)^2/4 by nlinarith) (show 0 ≤ a 0-1 by linarith)
    dsimp [entropyGap] at hp
    linarith


/-- Physical APPT-to-entropy-head bridge for explicit eigenvalue placements.
The PSD-star budget is derived from APPT, not assumed in this theorem. -/
theorem appt_eigenvalue_entropyHead_bound {n : ℕ} {b : Type*}
    [Fintype b] [DecidableEq b]
    {A : Matrix (Fin (n+2) × b) (Fin (n+2) × b) ℂ}
    (hA : A.IsHermitian) (h : APPT.Quantum.AbsolutelyPPT A)
    (σ : Equiv.Perm (Fin (n+2) × b))
    (e : Fin (n+2) → b) (he : Function.Injective e)
    (t : ℝ) (ht : 0 < t)
    (a : Fin (n+1) → ℝ) (β : Fin (n+2) → ℝ)
    (ha : ∀ i, 0 ≤ a i) (ha0 : ∀ i, a i ≤ a 0)
    (hβ : ∀ i, 0 ≤ β i) (hβanti : Antitone β) (hy : β 0 ≤ 1)
    (hc : hA.eigenvalues (σ (0,e 0)) ≤ t*(1-β 0))
    (hd : ∀ i : Fin (n+1), hA.eigenvalues (σ (i.succ,e i.succ)) ≤ t)
    (ho : ∀ i j : Fin (n+2), i < j →
      hA.eigenvalues (σ (i,e j)) ≤ hA.eigenvalues (σ (j,e i)))
    (hedge : ∀ i : Fin (n+1), hA.eigenvalues (σ (i.succ,e 0)) -
      hA.eigenvalues (σ (0,e i.succ)) = t*(a i+β i.succ)) :
    entropyHead a β ≤ 2 := by
  have hs := appt_eigenvalue_star_bound hA h σ e he (t*(1-β 0)) t ht hc hd ho
  simp_rw [hedge, mul_pow] at hs
  rw [← Finset.mul_sum] at hs
  apply entropyHead_le_two a β ha ha0 hβ hβanti hy
  have ht2 : 0 < t^2 := sq_pos_of_pos ht
  nlinarith

end APPTReview

