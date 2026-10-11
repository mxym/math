import APPTReview.FixedLocalLimit

open scoped BigOperators ComplexOrder Topology
open Matrix Filter
namespace APPTReview

/-- Fixed-local excess-purity bound before taking any limit. -/
theorem density_appt_fixed_excess_upper {m n : ℕ} (hm : 2≤m) (hn : 2*m≤n)
    {A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) (happt : APPT.Quantum.AbsolutelyPPT A) :
    ((m:ℝ)*n)^2*(APPT.Quantum.purity A-1/((m:ℝ)*n)) ≤
      ((m:ℝ)*n)/((m:ℝ)^2-1)+13*(m:ℝ)^2 := by
  have hmR : (2:ℝ)≤m := by exact_mod_cast hm
  have hnP : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hmP : (0:ℝ)<m := by linarith
  have hD : (0:ℝ)<(m:ℝ)*n := mul_pos hmP hnP
  have hc : (0:ℝ)<(m:ℝ)^2-1 := by nlinarith
  have hu := density_appt_fixed_local_upper hm hn hρ happt
  have hh := mul_le_mul_of_nonneg_left (sub_le_sub_right hu 1) hD.le
  have hl : ((m:ℝ)*n)^2*(APPT.Quantum.purity A-1/((m:ℝ)*n)) =
      ((m:ℝ)*n)*(((m:ℝ)*n)*APPT.Quantum.purity A-1) := by
    field_simp <;> ring
  rw [hl]
  have he : ((m:ℝ)*n)*((m:ℝ)^2/((m:ℝ)^2-1)+13*(m:ℝ)/n-1)=
      ((m:ℝ)*n)/((m:ℝ)^2-1)+13*(m:ℝ)^2 := by
    field_simp <;> ring
  rwa [he] at hh

/-- One total-dimension threshold covers fixed, growing, and arbitrarily
unbalanced local dimensions. This remains the upper half, not matching attainment. -/
theorem appt_total_dimension_uniform_upper (ε : ℝ) (hε : 0<ε) :
    ∃ N : ℕ, ∀ (m n : ℕ), 2≤m → m≤n → N≤m*n →
      ∀ A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ,
      APPT.Quantum.IsDensity A → APPT.Quantum.AbsolutelyPPT A →
      ((m:ℝ)*n)^2*(APPT.Quantum.purity A-1/((m:ℝ)*n)) ≤
        (1+ε)*max 8 (4+((m:ℝ)*n)/((m:ℝ)^2-1)) := by
  obtain ⟨M,hM⟩ := appt_uniform_asymptotic_upper ε hε
  let L : ℕ := max M 2
  obtain ⟨N,hN⟩ := exists_nat_gt (max (2*(L:ℝ)^2) (13*(L:ℝ)^4/ε))
  refine ⟨N,?_⟩
  intro m n hm hmn hND A hρ happt
  have hmR : (2:ℝ)≤m := by exact_mod_cast hm
  have hmP : (0:ℝ)<m := by linarith
  have hnP : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hD : (0:ℝ)<(m:ℝ)*n := mul_pos hmP hnP
  have hden : (0:ℝ)<(m:ℝ)^2-1 := by nlinarith
  have heP : 0≤1+ε := by linarith
  by_cases hmM : M≤m
  · have hu := hM m n hmM hmn A hρ happt
    have hratio : (n:ℝ)/m≤((m:ℝ)*n)/((m:ℝ)^2-1) := by
      calc
        _ = ((m:ℝ)*n)/(m:ℝ)^2 := by field_simp <;> ring
        _ ≤ _ := div_le_div_of_nonneg_left hD.le hden (by linarith)
    exact hu.trans (mul_le_mul_of_nonneg_left
      (max_le_max le_rfl (by linarith : (4:ℝ)+(n:ℝ)/m≤4+((m:ℝ)*n)/((m:ℝ)^2-1))) heP)
  · have hmL : m≤L := by dsimp [L]; omega
    have hmLR : (m:ℝ)≤L := by exact_mod_cast hmL
    have hL0 : (0:ℝ)≤L := Nat.cast_nonneg _
    have hsq : (m:ℝ)^2≤(L:ℝ)^2 := pow_le_pow_left₀ hmP.le hmLR 2
    have hNR : (N:ℝ)≤(m:ℝ)*n := by exact_mod_cast hND
    have hlarge : 2*(L:ℝ)^2<(m:ℝ)*n := (le_max_left _ _).trans_lt (hN.trans_le hNR)
    have herrLarge : 13*(L:ℝ)^4/ε<(m:ℝ)*n := (le_max_right _ _).trans_lt (hN.trans_le hNR)
    have hn2 : 2*m≤n := by
      by_contra hbad
      have hnR : (n:ℝ)<2*(m:ℝ) := by exact_mod_cast (lt_of_not_ge hbad)
      have hh := mul_lt_mul_of_pos_left hnR hmP
      nlinarith
    have hu := density_appt_fixed_excess_upper hm hn2 hρ happt
    have hpoly : (m:ℝ)^2*((m:ℝ)^2-1)≤(L:ℝ)^4 := by
      have hh := mul_le_mul hsq (show (m:ℝ)^2-1≤(L:ℝ)^2 by linarith)
        hden.le (sq_nonneg (L:ℝ))
      nlinarith
    have hlargeE : 13*(L:ℝ)^4<((m:ℝ)*n)*ε := (div_lt_iff₀ hε).1 herrLarge
    have herr : 13*(m:ℝ)^2≤ε*(((m:ℝ)*n)/((m:ℝ)^2-1)) := by
      rw [← mul_div_assoc]
      apply (le_div_iff₀ hden).2
      nlinarith
    have hfirst : ((m:ℝ)*n)^2*(APPT.Quantum.purity A-1/((m:ℝ)*n)) ≤
        (1+ε)*(((m:ℝ)*n)/((m:ℝ)^2-1)) := by nlinarith
    exact hfirst.trans (mul_le_mul_of_nonneg_left
      (le_trans (by linarith : ((m:ℝ)*n)/((m:ℝ)^2-1)≤4+((m:ℝ)*n)/((m:ℝ)^2-1))
        (le_max_right _ _)) heP)

end APPTReview
