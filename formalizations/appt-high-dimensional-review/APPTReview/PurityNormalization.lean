import APPTReview.FinitePurity
import Mathlib.Order.Interval.Finset.Fin

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

/-- The centered second moment is exactly the excess over the uniform spectrum. -/
theorem ordered_variance_identity {D : ℕ} (hD : 0<D) (f : Fin D → ℝ)
    (hs : (∑ i, f i)=1) :
    (∑ i, (f i-1/(D:ℝ))^2) = (∑ i, (f i)^2)-1/(D:ℝ) := by
  have hn : (D:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hD)
  simp [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul, hs]
  field_simp
  ring

/-- A high ordered pivot forces a definite centered variance in every preceding slot. -/
theorem ordered_pivot_variance {D : ℕ} (hD : 0<D) (f : Fin D → ℝ)
    (hf : Antitone f) (hs : (∑ i, f i)=1) (k : Fin D)
    (hk : 1/(D:ℝ)≤f k) :
    ((k.val+1 : ℕ) : ℝ)*(f k-1/(D:ℝ))^2 ≤ (∑ i, (f i)^2)-1/(D:ℝ) := by
  have hlocal (i : Fin D) (hi : i∈Finset.Iic k) :
      (f k-1/(D:ℝ))^2≤(f i-1/(D:ℝ))^2 := by
    have hord := hf (Finset.mem_Iic.mp hi)
    exact pow_le_pow_left₀ (sub_nonneg.mpr hk) (sub_le_sub_right hord _) 2
  calc
    _ = ∑ _i ∈ Finset.Iic k, (f k-1/(D:ℝ))^2 := by simp
    _ ≤ ∑ i ∈ Finset.Iic k, (f i-1/(D:ℝ))^2 := Finset.sum_le_sum hlocal
    _ ≤ ∑ i, (f i-1/(D:ℝ))^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun i _ _ => sq_nonneg _)
    _ = _ := ordered_variance_identity hD f hs

/-- Eliminate a positive pivot using its prefix variance, with the denominator kept explicit. -/
theorem scalar_pivot_normalization (D q C b V : ℝ)
    (hD : 0<D) (hq : 0<q) (hC : 0≤C) (hsmall : C<q) (hb : 0<b)
    (hV : V≤C*b^2) (hprefix : 1/D≤b → q*(b-1/D)^2≤V) :
    D^2*V≤C/(1-Real.sqrt (C/q))^2 := by
  let r := Real.sqrt (C/q)
  have hr : 0≤r := Real.sqrt_nonneg _
  have hrsq : r^2=C/q := Real.sq_sqrt (div_nonneg hC hq.le)
  have hratio : C/q<1 := (div_lt_one hq).2 hsmall
  have hrlt : r<1 := by nlinarith
  have hone : 0<1-r := by linarith
  have hmu : 0<1/D := one_div_pos.mpr hD
  have hbnd : b≤(1/D)/(1-r) := by
    apply (le_div_iff₀ hone).2
    by_cases hlow : b≤1/D
    · have hbr := mul_nonneg hb.le hr
      nlinarith
    · have hprefix' := (hprefix (le_of_not_ge hlow)).trans hV
      have he : q*(b*r)^2=C*b^2 := by
        rw [mul_pow, hrsq]
        field_simp
      have hsq : (b-1/D)^2≤(b*r)^2 := by
        have hh : q*(b-1/D)^2≤q*(b*r)^2 := by rw [he]; exact hprefix'
        exact (mul_le_mul_iff_right₀ hq).mp hh
      have hbr : 0≤b*r := mul_nonneg hb.le hr
      have hdiff : b-1/D≤b*r := by
        by_contra hbad
        have h1 : 0<(b-1/D)-(b*r) := by linarith
        have h2 : 0<(b-1/D)+(b*r) := by linarith
        have hh := mul_pos h1 h2
        nlinarith
      nlinarith
  have hbsq : b^2≤((1/D)/(1-r))^2 := pow_le_pow_left₀ hb.le hbnd 2
  have hbound := hV.trans (mul_le_mul_of_nonneg_left hbsq hC)
  have he : D^2*(C*((1/D)/(1-r))^2)=C/(1-r)^2 := by
    field_simp
  calc
    D^2*V ≤ D^2*(C*((1/D)/(1-r))^2) := mul_le_mul_of_nonneg_left hbound (sq_nonneg D)
    _ = _ := he

/-- A general ordered trace-one vector version; the quadratic cap is explicit here only. -/
theorem ordered_normalized_variance {D : ℕ} (hD : 0<D) (f : Fin D → ℝ)
    (hf : Antitone f) (hs : (∑ i, f i)=1) (k : Fin D) (hb : 0<f k)
    (C : ℝ) (hC : 0≤C) (hsmall : C<((k.val+1 : ℕ) : ℝ))
    (hV : (∑ i, (f i)^2)-1/(D:ℝ)≤C*(f k)^2) :
    (D:ℝ)^2*((∑ i, (f i)^2)-1/(D:ℝ)) ≤
      C/(1-Real.sqrt (C/((k.val+1 : ℕ) : ℝ)))^2 := by
  apply scalar_pivot_normalization (D:ℝ) ((k.val+1 : ℕ):ℝ) C (f k)
    ((∑ i, (f i)^2)-1/(D:ℝ)) (by exact_mod_cast hD) (by positivity) hC hsmall hb hV
  exact ordered_pivot_variance hD f hf hs k

/-- Dimension-only normalization of the actual finite APPT purity bound. -/
theorem density_appt_normalized_purity_bound {h n : ℕ} (hh : 1≤h) (hmn : h+1≤n)
    {A : Matrix (Fin (h+1) × Fin n) (Fin (h+1) × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) (happt : APPT.Quantum.AbsolutelyPPT A)
    (hsmall : max 8 (4+(Fintype.card (Fin (h+1) × Fin n):ℝ)/(h:ℝ)^2) <
      (((pairedPivot (by omega) hmn).val+1 : ℕ):ℝ)) :
    let D := (Fintype.card (Fin (h+1) × Fin n):ℝ)
    let C := max 8 (4+D/(h:ℝ)^2)
    let j := (((pairedPivot (by omega) hmn).val+1 : ℕ):ℝ)
    D^2*(APPT.Quantum.purity A-1/D)≤C/(1-Real.sqrt (C/j))^2 := by
  dsimp only
  rw [purity_eq_ordered_eigenvalues hρ.1.isHermitian]
  apply ordered_normalized_variance
    (by simp only [Fintype.card_prod,Fintype.card_fin]; exact Nat.mul_pos (by omega) (by omega))
    hρ.1.isHermitian.eigenvalues₀ hρ.1.isHermitian.eigenvalues₀_antitone
    (ordered_eigenvalues_sum hρ.1.isHermitian hρ.2)
    (pairedPivot (by omega) hmn) (density_pairedPivot_positive hh hmn hρ happt)
    _ (le_trans (by norm_num : (0:ℝ)≤8) (le_max_left _ _)) hsmall
  exact density_appt_ordered_variance_bound hh hmn hρ happt

end APPTReview
