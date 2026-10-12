import APPTReview.PurityNormalization

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

/-- The paper pivot has a prefix of at least one third of all eigenvalue slots. -/
theorem pairedPivot_prefix_large {h n : ℕ} (hh : 1≤h) (hmn : h+1≤n) :
    Fintype.card (Fin (h+1) × Fin n) ≤ 3*((pairedPivot (by omega) hmn).val+1) := by
  let D := Fintype.card (Fin (h+1) × Fin n)
  let R := Fintype.card (UpperPair (h+1))
  have hc := upperPair_card (h+1)
  have hd : (h+1)*(h+1)≤D := by
    simpa [D] using Nat.mul_le_mul_left (h+1) hmn
  have hp := pairPlacementBound hmn
  have he : (pairedPivot (by omega) hmn).val+R+(h+1)=D := by
    change D-R-(h+1)+R+(h+1)=D
    dsimp [R,D] at *
    omega
  dsimp only [R,D] at he hd
  nlinarith

/-- Explicit bounds uniform in the aspect ratio. No limiting maximizer is selected. -/
theorem uniform_purity_constants (h D q : ℝ)
    (hh : 7≤h) (hD : (h+1)^2≤D) (hqD : D≤3*q) :
    let C := max 8 (4+D/h^2)
    let K := max 8 (4+D/(h+1)^2)
    C<q ∧ C/(1-Real.sqrt (C/q))^2 ≤ ((h+1)/(h-6))^2*K := by
  dsimp only
  let C := max 8 (4+D/h^2)
  let K := max 8 (4+D/(h+1)^2)
  have hhp : 0<h := by linarith
  have hh2 : 0<h^2 := sq_pos_of_pos hhp
  have hmp : 0<h+1 := by linarith
  have hm2 : 0<(h+1)^2 := sq_pos_of_pos hmp
  have hDp : 0<D := lt_of_lt_of_le hm2 hD
  have hqp : 0<q := by linarith
  have hC0 : 0≤C := le_trans (by norm_num : (0:ℝ)≤8) (le_max_left _ _)
  have hK0 : 0≤K := le_trans (by norm_num : (0:ℝ)≤8) (le_max_left _ _)
  have hCrough : C≤8+D/h^2 := by
    dsimp [C]
    refine max_le ?_ ?_
    · have he : 0≤D/h^2 := div_nonneg hDp.le hh2.le; linarith
    · linarith
  have hCq : C*h^2≤27*q := by
    have he : (8+D/h^2)*h^2=8*h^2+D := by field_simp <;> ring
    have hc := mul_le_mul_of_nonneg_right hCrough hh2.le
    rw [he] at hc
    nlinarith
  have hsmall : C<q := by
    by_contra hn
    have he := mul_le_mul_of_nonneg_right (le_of_not_gt hn) hh2.le
    have hh27 : 0<h^2-27 := by nlinarith
    have hp := mul_pos hqp hh27
    nlinarith
  have hsqrt2 : (Real.sqrt (C/q)*h)^2≤27 := by
    rw [mul_pow, Real.sq_sqrt (div_nonneg hC0 hqp.le)]
    have he : C/q*h^2=(C*h^2)/q := by ring
    rw [he]
    exact (div_le_iff₀ hqp).2 hCq
  have hsqrt : Real.sqrt (C/q)≤6/h := by
    apply (le_div_iff₀ hhp).2
    nlinarith [sq_nonneg (Real.sqrt (C/q)*h-6)]
  have hd0 : 0<1-6/h := by
    have he : 6/h<1 := (div_lt_one hhp).2 (by linarith)
    linarith
  have hden : (1-6/h)^2≤(1-Real.sqrt (C/q))^2 :=
    pow_le_pow_left₀ hd0.le (by linarith) 2
  have hnorm : C/(1-Real.sqrt (C/q))^2≤C/(1-6/h)^2 :=
    div_le_div_of_nonneg_left hC0 (sq_pos_of_pos hd0) hden
  have hK8 : 8≤K := le_max_left _ _
  have hKb : 4+D/(h+1)^2≤K := le_max_right _ _
  have hKmass : 4*(h+1)^2+D≤K*(h+1)^2 := by
    have hh := mul_le_mul_of_nonneg_right hKb hm2.le
    have he : (4+D/(h+1)^2)*(h+1)^2=4*(h+1)^2+D := by field_simp <;> ring
    rwa [he] at hh
  have hscale : C≤K*(h+1)^2/h^2 := by
    dsimp [C]
    refine max_le ?_ ?_
    · apply (le_div_iff₀ hh2).2
      have he := mul_le_mul_of_nonneg_right hK8 hm2.le
      nlinarith
    · apply (le_div_iff₀ hh2).2
      have he : (4+D/h^2)*h^2=4*h^2+D := by field_simp <;> ring
      rw [he]
      nlinarith
  have he : (K*(h+1)^2/h^2)/(1-6/h)^2=((h+1)/(h-6))^2*K := by
    have hx : h-6≠0 := by linarith
    field_simp <;> ring
  refine ⟨hsmall, ?_⟩
  exact hnorm.trans (by rw [← he]; exact div_le_div_of_nonneg_right hscale (sq_nonneg _))

/-- A fully dimension-only finite upper bound, with explicit relative error tending to zero. -/
theorem density_appt_explicit_uniform_upper {h n : ℕ} (hh : 7≤h) (hmn : h+1≤n)
    {A : Matrix (Fin (h+1) × Fin n) (Fin (h+1) × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) (happt : APPT.Quantum.AbsolutelyPPT A) :
    let D := (((h+1 : ℕ) : ℝ)*n)
    D^2*(APPT.Quantum.purity A-1/D) ≤
      (((h:ℝ)+1)/((h:ℝ)-6))^2 * max 8 (4+D/((h:ℝ)+1)^2) := by
  let D := (Fintype.card (Fin (h+1) × Fin n):ℝ)
  let q := (((pairedPivot (by omega) hmn).val+1:ℕ):ℝ)
  have hdim : ((h:ℝ)+1)^2≤D := by
    have hn : (h+1)*(h+1)≤Fintype.card (Fin (h+1) × Fin n) := by
      simpa using Nat.mul_le_mul_left (h+1) hmn
    dsimp only [D]
    exact_mod_cast (show (h+1)^2≤Fintype.card (Fin (h+1) × Fin n) by nlinarith [hn])
  have hpref : D≤3*q := by
    dsimp only [D,q]
    exact_mod_cast pairedPivot_prefix_large (by omega : 1≤h) hmn
  have hc := uniform_purity_constants (h:ℝ) D q (by exact_mod_cast hh) hdim hpref
  have hu := density_appt_normalized_purity_bound (by omega : 1≤h) hmn hρ happt hc.1
  have hv := hu.trans hc.2
  simpa [D] using hv

end APPTReview
