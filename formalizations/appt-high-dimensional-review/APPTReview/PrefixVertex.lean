import APPTReview.PrefixCut

open scoped BigOperators
namespace APPTReview

theorem cutPair_spectralSquares {ν : Type*} [Fintype ν]
    (a b : ℝ) (u v : ν → ℝ) :
    spectralSquares (cutPair a b u v)=
      (b^2*spectralSquares u+2*a*b*(∑ i,u i*v i)+a^2*spectralSquares v)/(a+b)^2 := by
  have he (i : ν) : ((b*u i+a*v i)/(a+b))^2=
      (b^2*(u i)^2+2*a*b*(u i*v i)+a^2*(v i)^2)/(a+b)^2 := by
    rw [div_pow]
    ring
  change (∑ i, ((b*u i+a*v i)/(a+b))^2)=_
  simp_rw [he]
  rw [← Finset.sum_div,Finset.sum_add_distrib,Finset.sum_add_distrib]
  simp only [← Finset.mul_sum,spectralSquares]

/-- Exact crossing-edge moment after clearing the two prefix normalizations. -/
theorem crossing_rational_identity (i j h s : ℝ) (hi : i≠0) (hj : j≠0)
    (hz : h*j+s*i≠0) :
    (((s/j)^2)*(1/i)+2*(h/i)*(s/j)*(1/j)+(h/i)^2*(1/j))/(h/i+s/j)^2=
      (h^2*j+2*i*h*s+i*s^2)/(h*j+s*i)^2 := by
  have hd : h/i+s/j=(h*j+s*i)/(i*j) := by field_simp <;> ring
  rw [hd]
  generalize he : h*j+s*i=z at *
  field_simp
  ring

/-- Actual moments of the crossing vertices agree with the four-parameter
rational objective; the longer support and its integer cardinality are retained. -/
theorem uniformPrefix_crossing_purity {D : ℕ} (k l : Fin D) (hkl : k ≤ l)
    (L h s : ℝ) (hh : 0 < h) (hs : 0 ≤ s)
    (hl : ((l.val+1:ℕ):ℝ)=L+s) :
    spectralSquares (cutPair (h/((k.val+1:ℕ):ℝ)) (s/((l.val+1:ℕ):ℝ))
      (uniformPrefix k) (uniformPrefix l))=
      cutEdgePurity L h ((k.val+1:ℕ):ℝ) s := by
  have hiP : (0:ℝ) < ((k.val+1:ℕ):ℝ) := by positivity
  have hjP : (0:ℝ) < ((l.val+1:ℕ):ℝ) := by positivity
  have hZ : h*((l.val+1:ℕ):ℝ)+s*((k.val+1:ℕ):ℝ)≠0 := by positivity
  rw [cutPair_spectralSquares,uniformPrefix_squares,uniformPrefix_squares,
    uniformPrefix_inner k l hkl,
    crossing_rational_identity _ _ h s (ne_of_gt hiP) (ne_of_gt hjP) hZ]
  rw [hl]
  unfold cutEdgePurity
  congr 1 <;> ring

end APPTReview
