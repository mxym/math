import APPTSubunit.HalfHeadScalar

open scoped BigOperators
namespace APPTSubunit
open APPTReview

noncomputable def halfEntropyHead {n : ℕ} (a : Fin (n+1) → ℝ)
    (β : Fin (n+2) → ℝ) : ℝ :=
  (∑ i,(halfEntropyKernel (a i)+a i*β i.castSucc))+∑ i,halfEntropyKernel (-β i)

/-- The nonlinear half-order exceptional-head bound from the actual shifted
star budget. Its negative endpoint is allowed, and its dimension is arbitrary.
This is the key new estimate for subunit Renyi orders, not a finite search. -/
theorem halfEntropyHead_le_two {n : ℕ} (a : Fin (n+1) → ℝ) (β : Fin (n+2) → ℝ)
    (ha : ∀ i,0≤a i) (ha0 : ∀ i,a i≤a 0)
    (hβ : ∀ i,0≤β i) (hβanti : Antitone β) (hy : β 0≤1)
    (hstar : (∑ i : Fin (n+1),(a i+β i.succ)^2)≤4*(1-β 0)) :
    halfEntropyHead a β≤2 := by
  let r := Real.sqrt (1-β 0)
  let c : ℝ := 2/(1+r)^2
  have hr0 : 0≤r := Real.sqrt_nonneg _
  have hr2 : r^2=1-β 0 := Real.sq_sqrt (by linarith)
  have hr1 : r≤1 := by
    have hh := Real.sqrt_le_sqrt (show 1-β 0≤(1:ℝ) by linarith [hβ 0])
    simpa only [Real.sqrt_one] using hh
  have hden : 0<(1+r)^2 := sq_pos_of_pos (by linarith)
  have hc : (1/2:ℝ)≤c := by
    dsimp [c]
    apply (le_div_iff₀ hden).2
    nlinarith
  have hc0 : 0≤c := by linarith
  have hn (i : Fin (n+2)) : halfEntropyKernel (-β i)≤c*(β i)^2 :=
    half_kernel_negative_bounded (β i) (β 0) (hβ i) (hβanti (Fin.zero_le i)) hy
  have hterm (i : Fin (n+1)) :
      halfEntropyKernel (a i)+a i*β i.succ+halfEntropyKernel (-β i.succ)+halfEntropyGap (a i)
        ≤c*(a i+β i.succ)^2 := by
    have hp := mul_nonneg (ha i) (hβ i.succ)
    have hh := mul_nonneg (show 0≤c-1/2 by linarith)
      (show 0≤(a i)^2+2*a i*β i.succ by nlinarith [sq_nonneg (a i)])
    dsimp [halfEntropyGap]
    nlinarith [hn i.succ]
  have hsum := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hterm i)
  rw [← Finset.mul_sum] at hsum
  simp only [Finset.sum_add_distrib] at hsum
  have hdiff : (∑ i : Fin (n+1),(β i.castSucc-β i.succ))=β 0-β (Fin.last (n+1)) := by
    rw [Finset.sum_sub_distrib]
    have h1 := Fin.sum_univ_castSucc β
    have h2 := Fin.sum_univ_succ β
    linarith
  have htel : (∑ i : Fin (n+1),a i*(β i.castSucc-β i.succ))≤a 0*β 0 := by
    calc
      _ ≤ ∑ i : Fin (n+1),a 0*(β i.castSucc-β i.succ) := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_right (ha0 i)
          (sub_nonneg.mpr (hβanti (by change i.val ≤ i.val+1; omega : i.castSucc ≤ i.succ)))
      _ = a 0*(β 0-β (Fin.last (n+1))) := by rw [← Finset.mul_sum,hdiff]
      _ ≤ _ := by nlinarith [mul_nonneg (ha 0) (hβ (Fin.last (n+1)))]
  have hsplit : (∑ i : Fin (n+1),a i*β i.castSucc)=(∑ i : Fin (n+1),a i*β i.succ)+
      ∑ i : Fin (n+1),a i*(β i.castSucc-β i.succ) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hgap : halfEntropyGap (a 0)≤∑ i : Fin (n+1),halfEntropyGap (a i) :=
    Finset.single_le_sum (fun i _ => halfEntropyGap_nonneg (a i) (ha i)) (Finset.mem_univ 0)
  have hbudget := mul_le_mul_of_nonneg_left hstar hc0
  have he : c*(4*(1-β 0)+(β 0)^2)=2*(1+r^2)^2/(1+r)^2 := by
    dsimp [c]
    field_simp
    nlinarith [sq_nonneg (β 0)]
  have hfirst : (a 0+β (0 : Fin (n+1)).succ)^2≤4*(1-β 0) :=
    (Finset.single_le_sum (fun i (_ : i∈Finset.univ) => sq_nonneg (a i+β i.succ))
      (Finset.mem_univ (0 : Fin (n+1)))).trans hstar
  have hasize : a 0≤2*r := by
    nlinarith [mul_nonneg (ha 0) (hβ (0 : Fin (n+1)).succ),sq_nonneg (β (0 : Fin (n+1)).succ)]
  have hcomp := half_head_scalar_comparison (a 0) r (ha 0) hr0 hr1 hasize
  have hpre : halfEntropyHead a β≤c*(4*(1-β 0)+(β 0)^2)+a 0*β 0-halfEntropyGap (a 0) := by
    dsimp [halfEntropyHead]
    rw [Fin.sum_univ_succ (fun i : Fin (n+2) => halfEntropyKernel (-β i))]
    simp only [Finset.sum_add_distrib]
    nlinarith [hn 0]
  rw [he] at hpre
  have hyEq : β 0=1-r^2 := by linarith
  rw [hyEq] at hpre
  exact hpre.trans hcomp

/-- The bound is sharp even at a non-flat negative spectral head. -/
theorem halfEntropyHead_endpoint :
    halfEntropyHead (fun _ : Fin 1 => (0:ℝ)) (fun i : Fin 2 => if i=0 then 1 else 0)=2 := by
  unfold halfEntropyHead
  rw [Fin.sum_univ_one,Fin.sum_univ_two]
  norm_num [halfEntropyKernel]

end APPTSubunit
