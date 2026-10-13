import APPTReview.EffectiveAsymptotic

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

/-- Uniform constructive lower half for the spike-plus-plateau branch, including
fixed, growing and arbitrarily unbalanced local dimensions. -/
theorem appt_total_dimension_branch_lower (ε : ℝ) (hε : 0<ε) :
    ∃ N : ℕ, ∀ (m n : ℕ), 2≤m → m≤n → N≤m*n →
      ∃ A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ,
        APPT.Quantum.IsDensity A ∧ APPT.Quantum.AbsolutelyPPT A ∧
        (1-ε)*(4+((m:ℝ)*n)/((m:ℝ)^2-1)) ≤
          ((m:ℝ)*n)^2*(APPT.Quantum.purity A-1/((m:ℝ)*n)) := by
  let δ := min (ε/4) (1/4)
  have hδ : 0<δ := lt_min (by positivity) (by norm_num)
  have hδ1 : δ≤1/4 := min_le_right _ _
  have hδε : 4*δ≤ε := by have ht := min_le_left (ε/4) (1/4:ℝ); dsimp [δ]; linarith
  obtain ⟨M,hM⟩ := appt_growing_branch_lower δ hδ
  obtain ⟨L,hL⟩ := exists_nat_gt (max ((M:ℝ)+2) (1/δ))
  have hL2 : (2:ℝ)≤L := by have ht := le_max_left ((M:ℝ)+2) (1/δ); linarith [show (0:ℝ)≤M from Nat.cast_nonneg _]
  obtain ⟨N,hN⟩ := exists_nat_gt (5*(L:ℝ)^2/ε)
  refine ⟨N,?_⟩
  intro m n hm hmn hND
  have hmR : (2:ℝ)≤m := by exact_mod_cast hm
  have hmP : (0:ℝ)<m := by linarith
  have hnR : (m:ℝ)≤n := by exact_mod_cast hmn
  have hnP : (0:ℝ)<n := by linarith
  let D : ℝ := (m:ℝ)*n
  let E : ℝ := 4+D/((m:ℝ)^2-1)
  have hDP : 0<D := mul_pos hmP hnP
  have hden : (0:ℝ)<(m:ℝ)^2-1 := by nlinarith
  have hEP : 0<E := by dsimp [E]; positivity
  by_cases hbig : L≤m
  · have hbigR : (L:ℝ)≤m := by exact_mod_cast hbig
    have hmM : M≤m := by
      have hx := (le_max_left ((M:ℝ)+2) (1/δ)).trans_lt (hL.trans_le hbigR)
      have ht : (M:ℝ)≤m := by linarith
      exact_mod_cast ht
    obtain ⟨A,hd,ha,hlo⟩ := hM m n hmM hmn
    refine ⟨A,hd,ha,?_⟩
    have hsize : 1/δ≤(m:ℝ) := (le_max_right _ _).trans (hL.le.trans hbigR)
    have hmul : 1≤(m:ℝ)*δ := (div_le_iff₀ hδ).mp hsize
    have hmulsq := mul_le_mul_of_nonneg_right hmul hmP.le
    have hinv : 1/(m:ℝ)^2≤δ := (div_le_iff₀ (sq_pos_of_pos hmP)).2 (by nlinarith)
    have hid := branch_coefficient_identity (m:ℝ) D (ne_of_gt hmP) (ne_of_gt hden)
    have hfrac : D/(m:ℝ)^2=(n:ℝ)/m := by dsimp [D]; field_simp
    have hcoeff : (1-δ)*E≤4+(n:ℝ)/m := by
      have hx := mul_le_mul_of_nonneg_right (show 1-δ≤1-1/(m:ℝ)^2 by linarith) hEP.le
      rw [hfrac] at hid
      change 4+(n:ℝ)/m=(1-1/(m:ℝ)^2)*E+4/(m:ℝ)^2 at hid
      linarith [div_nonneg (by norm_num : (0:ℝ)≤4) (sq_nonneg (m:ℝ))]
    have hc : 0≤1-δ := by linarith
    have hrel := mul_le_mul_of_nonneg_left hcoeff hc
    have hsq : 1-ε≤(1-δ)^2 := by nlinarith
    have hstep := mul_le_mul_of_nonneg_right hsq hEP.le
    have hx : (1-ε)*E≤(1-δ)*(4+(n:ℝ)/m) := by nlinarith
    exact hx.trans hlo
  · have hmL : (m:ℝ)≤L := by exact_mod_cast (show m≤L by omega)
    have hNR : (N:ℝ)≤D := by change (N:ℝ)≤(m:ℝ)*n; exact_mod_cast hND
    have hsize : 5*(L:ℝ)^2/ε<D := hN.trans_le hNR
    have heps : 5*(L:ℝ)^2<D*ε := (div_lt_iff₀ hε).mp hsize
    have hmsq : (m:ℝ)^2≤(L:ℝ)^2 := pow_le_pow_left₀ hmP.le hmL 2
    have hbudget : 5≤ε*(D/((m:ℝ)^2-1)) := by
      rw [← mul_div_assoc]
      apply (le_div_iff₀ hden).2
      nlinarith
    obtain ⟨A,hd,ha,hlo⟩ := exists_projection_excess_lower hm hmn
    refine ⟨A,hd,ha,?_⟩
    have hratio : (m:ℝ)/n≤1 := (div_le_one hnP).2 hnR
    have hsmall : (1-ε)*E≤D/((m:ℝ)^2-1)-(m:ℝ)/n := by
      dsimp [E]
      nlinarith
    exact hsmall.trans hlo

end APPTReview
