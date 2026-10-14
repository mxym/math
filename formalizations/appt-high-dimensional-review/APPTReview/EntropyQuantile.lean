import APPTReview.FullEntropyBound
import APPTReview.PurityNormalization

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

/-- Complementary low-pivot variance bound: the suffix is retained as well as
the prefix, so trace normalization is controlled in both directions. -/
theorem ordered_low_pivot_variance {D : ℕ} (hD : 0<D) (f : Fin D → ℝ)
    (hf : Antitone f) (hs : (∑ i,f i)=1) (p : Fin D) (hp : f p≤1/(D:ℝ)) :
    ((D-p.val:ℕ):ℝ)*(f p-1/(D:ℝ))^2≤(∑ i,(f i)^2)-1/(D:ℝ) := by
  have hlocal (i : Fin D) (hi : i∈Finset.Ici p) :
      (f p-1/(D:ℝ))^2≤(f i-1/(D:ℝ))^2 := by
    have ho := hf (Finset.mem_Ici.mp hi)
    have hh := pow_le_pow_left₀ (sub_nonneg.mpr hp)
      (show 1/(D:ℝ)-f p≤1/(D:ℝ)-f i by linarith) 2
    nlinarith
  calc
    _ = ∑ _i∈Finset.Ici p,(f p-1/(D:ℝ))^2 := by simp
    _ ≤ ∑ i∈Finset.Ici p,(f i-1/(D:ℝ))^2 := Finset.sum_le_sum hlocal
    _ ≤ ∑ i,(f i-1/(D:ℝ))^2 := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun i _ _ => sq_nonneg _)
    _ = _ := ordered_variance_identity hD f hs

/-- Any quantile with sufficiently many points on each side controls the
normalization error, without assuming which side of the mean it occupies. -/
theorem ordered_two_sided_pivot_variance {D : ℕ} (hD : 0<D) (f : Fin D → ℝ)
    (hf : Antitone f) (hs : (∑ i,f i)=1) (p : Fin D) (q : ℝ)
    (hl : q≤((p.val+1:ℕ):ℝ)) (hr : q≤((D-p.val:ℕ):ℝ)) :
    q*(f p-1/(D:ℝ))^2≤(∑ i,(f i)^2)-1/(D:ℝ) := by
  by_cases hp : 1/(D:ℝ)≤f p
  · exact (mul_le_mul_of_nonneg_right hl (sq_nonneg _)).trans (ordered_pivot_variance hD f hf hs p hp)
  · exact (mul_le_mul_of_nonneg_right hr (sq_nonneg _)).trans
      (ordered_low_pivot_variance hD f hf hs p (le_of_not_ge hp))

theorem ordered_normalized_moment_budget {D : ℕ} (hD : 0<D)
    (f : Fin D → ℝ) (hf : Antitone f) (hs : (∑ i,f i)=1)
    (p : Fin D) (hb : 0<f p) (q C : ℝ) (hq : 0<q)
    (hl : q≤((p.val+1:ℕ):ℝ)) (hr : q≤((D-p.val:ℕ):ℝ))
    (hV : (∑ i,(f i)^2)-1/(D:ℝ)≤C*(f p)^2) :
    (1/((D:ℝ)*f p)-1)^2≤C/q ∧
    (∑ i,(f i/f p-1)^2)≤C+(D:ℝ)*(C/q) := by
  have hDr : (D:ℝ)≠0 := by exact_mod_cast (ne_of_gt hD)
  have hv := (ordered_two_sided_pivot_variance hD f hf hs p q hl hr).trans hV
  have he : q*(f p-1/(D:ℝ))^2=(f p)^2*(q*(1/((D:ℝ)*f p)-1)^2) := by field_simp;ring
  rw [he,mul_comm C ((f p)^2)] at hv
  have hnorm := (mul_le_mul_iff_right₀ (sq_pos_of_pos hb)).mp hv
  have hmean : (1/((D:ℝ)*f p)-1)^2≤C/q := (le_div_iff₀ hq).2 (by nlinarith)
  refine ⟨hmean,?_⟩
  have hquad := spectrum_quadratic_centering hD f hs (f p) hb
  have hV' : ((∑ i,(f i)^2)-1/(D:ℝ))/(f p)^2≤C := (div_le_iff₀ (sq_pos_of_pos hb)).2 hV
  have hm := mul_le_mul_of_nonneg_left hmean (Nat.cast_nonneg D)
  linarith

/-- The actual paper quantile has at least m^2/4 positions on either side. -/
theorem paper_pivot_quarter_bounds {k n : ℕ} (hmn : k+2≤n) :
    (((k+2:ℕ):ℝ)^2/4≤(((paperPivot hmn).val+1:ℕ):ℝ)) ∧
    (((k+2:ℕ):ℝ)^2/4≤((Fintype.card (Fin (k+2) × Fin n)-(paperPivot hmn).val:ℕ):ℝ)) := by
  let m := k+2
  let D := Fintype.card (Fin (k+2) × Fin n)
  let R := Fintype.card (UpperPair (k+2))
  let p := (paperPivot hmn).val
  have hc : 2*R+m=m*m := upperPair_card (k+2)
  have hd : 2*R+m≤D := pairPlacementBound hmn
  have hp : p+R+m=D := by
    dsimp only [p]
    rw [← pairedPivot_eq_paperPivot hmn]
    change D-R-m+R+m=D
    omega
  have hDsub : D-p=R+m := by omega
  have hcR : 2*(R:ℝ)+(m:ℝ)=(m:ℝ)*(m:ℝ) := by exact_mod_cast hc
  have hdR : 2*(R:ℝ)+(m:ℝ)≤(D:ℝ) := by exact_mod_cast hd
  have hpR : (p:ℝ)+(R:ℝ)+(m:ℝ)=(D:ℝ) := by exact_mod_cast hp
  have hmR : (2:ℝ)≤m := by exact_mod_cast (show 2≤m by dsimp [m];omega)
  change (m:ℝ)^2/4≤((p+1:ℕ):ℝ) ∧ (m:ℝ)^2/4≤((D-p:ℕ):ℝ)
  rw [hDsub]
  push_cast
  constructor <;> nlinarith

noncomputable def entropyVarianceCap (k n : ℕ) : ℝ :=
  max 8 (4+(Fintype.card (Fin (k+2) × Fin n):ℝ)/((k+1:ℕ):ℝ)^2)

/-- Quantitative two-sided pivot and entire-moment estimates from the original
physical APPT assumptions. They are sufficient for every fixed aspect ratio. -/
theorem density_appt_entropy_normalization_budget {k n : ℕ} (hmn : k+2≤n)
    {A : Matrix (Fin (k+2) × Fin n) (Fin (k+2) × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) (hP : APPT.Quantum.AbsolutelyPPT A) :
    let D := (Fintype.card (Fin (k+2) × Fin n):ℝ)
    let f := hρ.1.isHermitian.eigenvalues₀
    let b := f (paperPivot hmn)
    (1/(D*b)-1)^2≤4*entropyVarianceCap k n/((k+2:ℕ):ℝ)^2 ∧
    (∑ i,(f i/b-1)^2)≤(1+4*D/((k+2:ℕ):ℝ)^2)*entropyVarianceCap k n := by
  dsimp only
  have hq := paper_pivot_quarter_bounds hmn
  have hp := paper_head_pivot_positive hmn hρ hP
  have hvar := density_appt_ordered_variance_bound (h:=k+1) (by omega) hmn hρ hP
  rw [pairedPivot_eq_paperPivot hmn] at hvar
  have hh := ordered_normalized_moment_budget
    (by simp only [Fintype.card_prod,Fintype.card_fin];exact Nat.mul_pos (by omega) (by omega) : 0<Fintype.card (Fin (k+2) × Fin n))
    hρ.1.isHermitian.eigenvalues₀ hρ.1.isHermitian.eigenvalues₀_antitone
    (ordered_eigenvalues_sum hρ.1.isHermitian hρ.2) (paperPivot hmn) hp
    (((k+2:ℕ):ℝ)^2/4) (entropyVarianceCap k n) (by positivity) hq.1 hq.2 hvar
  have he : entropyVarianceCap k n/(((k+2:ℕ):ℝ)^2/4)=4*entropyVarianceCap k n/((k+2:ℕ):ℝ)^2 := by ring
  rw [he] at hh
  refine ⟨hh.1,?_⟩
  convert hh.2 using 1 <;> ring

end APPTReview
