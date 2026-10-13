import APPTReview.OrderedPrefix

open scoped BigOperators
namespace APPTReview

/-- A sublevel with a prescribed unique boundary point is convex. The exact
Jensen defect is retained, so equality is not inferred from numerical optimality. -/
theorem convex_unique_spectral_sublevel {ν : Type*} [Fintype ν]
    (C : ℝ) (z : ν → ℝ) :
    Convex ℝ {f : ν → ℝ | spectralSquares f ≤ C ∧ (spectralSquares f=C → f=z)} := by
  intro x hx y hy a b ha hb hab
  have hid := spectralSquares_mixture x y a b hab
  have hd : 0 ≤ a*b*∑ i,(x i-y i)^2 := by positivity
  have hxc := mul_le_mul_of_nonneg_left hx.1 ha
  have hyc := mul_le_mul_of_nonneg_left hy.1 hb
  have hsum : a*C+b*C=C := by rw [← add_mul,hab,one_mul]
  refine ⟨by change spectralSquares (a • x+b • y) ≤ C;linarith,?_⟩
  intro he
  by_cases ha0 : a=0
  · have hb1 : b=1 := by linarith
    have hyE : spectralSquares y=C := by simpa [ha0,hb1] using he
    simpa [ha0,hb1] using hy.2 hyE
  · by_cases hb0 : b=0
    · have ha1 : a=1 := by linarith
      have hxE : spectralSquares x=C := by simpa [hb0,ha1] using he
      simpa [hb0,ha1] using hx.2 hxE
    · have haP : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      have hbP : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
      have hxE : spectralSquares x=C := by
        by_contra hn
        have ht := mul_lt_mul_of_pos_left (lt_of_le_of_ne hx.1 hn) haP
        nlinarith
      have hyE : spectralSquares y=C := by
        by_contra hn
        have ht := mul_lt_mul_of_pos_left (lt_of_le_of_ne hy.1 hn) hbP
        nlinarith
      rw [hx.2 hxE,hy.2 hyE,← add_smul,hab,one_smul]

/-- Complete equality reduction for an arbitrary ordered probability spectrum
in the cut simplex. Every possible crossing vertex is covered. -/
theorem ordered_spectrum_cut_unique {D : ℕ} (f c z : Fin D → ℝ) (C : ℝ)
    (hf : Antitone f) (hn : ∀ i,0 ≤ f i) (hs : (∑ i,f i)=1)
    (hcut : (∑ i,c i*f i) ≤ 0)
    (hv : ∀ k,(∑ i,c i*uniformPrefix k i) ≤ 0 →
      spectralSquares (uniformPrefix k) ≤ C ∧
      (spectralSquares (uniformPrefix k)=C → uniformPrefix k=z))
    (he : ∀ k l,0 < (∑ i,c i*uniformPrefix k i) → (∑ i,c i*uniformPrefix l i) ≤ 0 →
      let v := cutPair (∑ i,c i*uniformPrefix k i) (-(∑ i,c i*uniformPrefix l i))
        (uniformPrefix k) (uniformPrefix l)
      spectralSquares v ≤ C ∧ (spectralSquares v=C → v=z)) :
    spectralSquares f ≤ C ∧ (spectralSquares f=C → f=z) := by
  have h := convex_mem_of_cut_simplex
    {v : Fin D → ℝ | spectralSquares v ≤ C ∧ (spectralSquares v=C → v=z)}
    (convex_unique_spectral_sublevel C z) (orderedSimplexWeight f)
    (fun k => ∑ i,c i*uniformPrefix k i) uniformPrefix
    (orderedSimplexWeight_nonneg f hf hn) ((orderedSimplexWeight_sum f).trans hs)
    (by rw [ordered_prefix_linear];exact hcut) hv he
  rwa [ordered_prefix_expansion] at h

end APPTReview
