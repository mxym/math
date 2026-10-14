import APPTReview.NormalizedHeadVariance

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

/-- Real logarithmic remainder; this is exact, including the zero eigenvalue
endpoint x=-1, rather than a numerical or polynomial surrogate for entropy. -/
noncomputable def entropyRemainder (x : ℝ) : ℝ := entropyKernel x-x^2/2

noncomputable def spectralVonNeumannEntropy {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) : ℝ :=
  -(∑ i,hA.eigenvalues₀ i*Real.log (hA.eigenvalues₀ i))

theorem scaled_entropyKernel (b x : ℝ) (hb : 0<b) (hx : 0≤x) :
    b*entropyKernel (x/b-1)=x*Real.log x-x*Real.log b-x+b := by
  by_cases hx0 : x=0
  · subst x;simp [entropyKernel]
  · have hxP : 0<x := lt_of_le_of_ne hx (Ne.symm hx0)
    have he : 1+(x/b-1)=x/b := by ring
    unfold entropyKernel
    rw [he,Real.log_div (ne_of_gt hxP) (ne_of_gt hb)]
    field_simp
    ring

/-- Exact trace-one normalization of the full entropy deficit. Zero entries
are handled before splitting logarithms; no full-rank hypothesis is used. -/
theorem spectrum_entropy_centering {D : ℕ} (hD : 0<D)
    (f : Fin D → ℝ) (hn : ∀ i,0≤f i) (hs : (∑ i,f i)=1)
    (b : ℝ) (hb : 0<b) :
    (Real.log (D:ℝ)+(∑ i,f i*Real.log (f i)))/b=
      (∑ i,entropyKernel (f i/b-1))-(D:ℝ)*entropyKernel (1/((D:ℝ)*b)-1) := by
  have hDr : (0:ℝ)<D := by exact_mod_cast hD
  have hDb : (D:ℝ)*b≠0 := ne_of_gt (mul_pos hDr hb)
  have hsum := Finset.sum_congr (s₁:=Finset.univ) (s₂:=Finset.univ) rfl
    (fun i _ => scaled_entropyKernel b (f i) hb (hn i))
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,
    ← Finset.sum_mul,hs,one_mul,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
  have hmean : (D:ℝ)*b*entropyKernel (1/((D:ℝ)*b)-1)=
      -Real.log (D:ℝ)-Real.log b-1+(D:ℝ)*b := by
    have he : 1+(1/((D:ℝ)*b)-1)=1/((D:ℝ)*b) := by ring
    unfold entropyKernel
    rw [he,one_div,Real.log_inv,Real.log_mul (ne_of_gt hDr) (ne_of_gt hb)]
    field_simp
    ring
  apply (div_eq_iff (ne_of_gt hb)).2
  nlinarith

/-- Exact quadratic centering, with the same nonuniform normalization pivot. -/
theorem spectrum_quadratic_centering {D : ℕ} (hD : 0<D)
    (f : Fin D → ℝ) (hs : (∑ i,f i)=1) (b : ℝ) (hb : 0<b) :
    (∑ i,(f i/b-1)^2)-(D:ℝ)*(1/((D:ℝ)*b)-1)^2=
      ((∑ i,(f i)^2)-1/(D:ℝ))/b^2 := by
  have hDr : (D:ℝ)≠0 := by exact_mod_cast (ne_of_gt hD)
  simp only [sub_sq,div_pow,Finset.sum_add_distrib,Finset.sum_sub_distrib,
    ← Finset.mul_sum,← Finset.sum_div,hs,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,one_pow,mul_one]
  field_simp
  ring

/-- Full entropy is half the centered purity plus the exact sum of logarithmic
remainders. The trace-centering remainder is subtracted, never discarded. -/
theorem spectrum_entropy_remainder_identity {D : ℕ} (hD : 0<D)
    (f : Fin D → ℝ) (hn : ∀ i,0≤f i) (hs : (∑ i,f i)=1)
    (b : ℝ) (hb : 0<b) :
    (Real.log (D:ℝ)+(∑ i,f i*Real.log (f i)))/b=
      ((∑ i,(f i)^2)-1/(D:ℝ))/b^2/2+
      (∑ i,entropyRemainder (f i/b-1))-(D:ℝ)*entropyRemainder (1/((D:ℝ)*b)-1) := by
  rw [spectrum_entropy_centering hD f hn hs b hb]
  have hq := spectrum_quadratic_centering hD f hs b hb
  simp only [entropyRemainder,Finset.sum_sub_distrib,← Finset.sum_div]
  nlinarith

end APPTReview
