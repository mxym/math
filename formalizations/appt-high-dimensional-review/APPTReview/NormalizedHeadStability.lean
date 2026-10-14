import APPTReview.EntropyHeadStability

open scoped BigOperators
namespace APPTReview

/-- Normalize the entire spectrum by trace one, rather than silently replacing
its positive pivot by the uniform eigenvalue. -/
theorem trace_normalized_contrast {D : ℕ} (f : Fin D → ℝ) (b a y : ℝ)
    (hb : 0 < b) (ha : 0 ≤ a) (hy : 0 ≤ y) (hyh : y ≤ 1/2)
    (hsum : (∑ i, f i)=1)
    (hlo : ∀ i, b*(1-y) ≤ f i) (hhi : ∀ i, f i ≤ b*(1+a)) :
    ∀ i, |(D:ℝ)*f i-1| ≤ 2*(a+y) := by
  have hl := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hlo i)
  have hu := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hhi i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,hsum] at hl hu
  have hDb : 0 ≤ (D:ℝ)*b := mul_nonneg (Nat.cast_nonneg _) hb.le
  have hhalf := mul_le_mul_of_nonneg_left hyh hDb
  have hbound : (D:ℝ)*b ≤ 2 := by nlinarith only [hhalf,hl]
  intro i
  have hli := mul_le_mul_of_nonneg_left (hlo i) (Nat.cast_nonneg D : (0:ℝ) ≤ D)
  have hui := mul_le_mul_of_nonneg_left (hhi i) (Nat.cast_nonneg D : (0:ℝ) ≤ D)
  have hc := mul_le_mul_of_nonneg_right hbound (add_nonneg ha hy)
  exact abs_le.mpr ⟨by nlinarith only [hli,hu,hc],by nlinarith only [hui,hl,hc]⟩

/-- An explicit cubic modulus of spectral flatness. The hypotheses are all
finite quantities; no dimension limit is assumed. -/
theorem normalized_spectrum_cubic_stability {D : ℕ}
    (f : Fin D → ℝ) (b a y Δ : ℝ)
    (hb : 0 < b) (ha : 0 ≤ a) (hy : 0 ≤ y) (hy1 : y ≤ 1)
    (hsum : (∑ i, f i)=1)
    (hlo : ∀ i, b*(1-y) ≤ f i) (hhi : ∀ i, f i ≤ b*(1+a))
    (hΔ : 0 ≤ Δ) (hsmall : Δ ≤ 1/144)
    (hac : a^3 ≤ 300*Δ) (hyc : y ≤ 72*Δ) :
    ∀ i, |(D:ℝ)*f i-1|^3 ≤ 11904*Δ := by
  have hyh : y ≤ 1/2 := by linarith
  have hab := trace_normalized_contrast f b a y hb ha hy hyh hsum hlo hhi
  have hy2 : y^2 ≤ 1 := by nlinarith only [hy,hy1]
  have hy3 := mul_le_mul_of_nonneg_right hy2 hy
  have hsum3 : (a+y)^3 ≤ 4*(a^3+y^3) := by
    have hpos := mul_nonneg (sq_nonneg (a-y)) (add_nonneg ha hy)
    nlinarith only [hpos]
  intro i
  have hc := pow_le_pow_left₀ (abs_nonneg ((D:ℝ)*f i-1)) (hab i) 3
  nlinarith only [hc,hsum3,hy3,hac,hyc]

/-- Cubes reflect strict order on nonnegative reals, without numerical roots. -/
theorem nonnegative_lt_of_cube_lt {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y)
    (h : x^3 < y^3) : x < y := by
  by_contra hn
  have hrev := pow_le_pow_left₀ hy.le (le_of_not_gt hn) 3
  linarith

end APPTReview
