import LocalCap.Compression

open scoped BigOperators ComplexOrder
open Matrix
namespace ExtractionLocalCap

variable {a b : Type*} [Fintype a] [Fintype b] [LinearOrder a] [DecidableEq b]

/-- The full signed Schmidt spectrum has exactly the squared Schmidt sum as
absolute mass, including every positive and negative pair. -/
theorem schmidtSigned_absolute_mass (s : a → ℝ) (hs : ∀ i, 0 ≤ s i) :
    (∑ p : a × a, |APPTReview.schmidtSigned s p|) = (∑ i, s i)^2 := by
  have hp (p : a × a) :
      |APPTReview.schmidtSigned s p| = s p.1 * s p.2 := by
    unfold APPTReview.schmidtSigned
    split_ifs with he hl
    · simp only [he, pow_two]
      exact abs_of_nonneg (mul_nonneg (hs _) (hs _))
    · exact abs_of_nonneg (mul_nonneg (hs _) (hs _))
    · rw [abs_neg, abs_of_nonneg (mul_nonneg (hs _) (hs _))]
  simp only [hp, Fintype.sum_prod_type, ← Finset.mul_sum, ← Finset.sum_mul, pow_two]

/-- The physical pure-state partial transpose has absolute Schmidt mass at most
the smaller local coordinate count times the original vector's squared norm.
No Schmidt data are caller supplied. -/
theorem pure_partialTranspose_pairing_le (X : Matrix (a × b) (a × b) ℂ)
    (c : ℝ) (hc : 0 ≤ c)
    (hlo : (c • (1 : Matrix (a × b) (a × b) ℂ) + X).PosSemidef)
    (hhi : (c • (1 : Matrix (a × b) (a × b) ℂ) - X).PosSemidef)
    (w : a × b → ℂ) :
    (X * APPT.Quantum.partialTranspose (Matrix.vecMulVec w (star w))).trace.re ≤
      (c * Fintype.card a) * (star w ⬝ᵥ w).re := by
  obtain ⟨s,L,hs,hss,hL,hW⟩ := APPTReview.exists_pure_signed_model w
  rw [hW]
  calc
    _ ≤ c * ∑ p : a × a, |APPTReview.schmidtSigned s p| :=
      trace_signed_congruence_le X L _ c hc hL hlo hhi
    _ = c * (∑ i, s i)^2 := by rw [schmidtSigned_absolute_mass s hs]
    _ ≤ c * ((Fintype.card a : ℝ) * ∑ i, (s i)^2) :=
      mul_le_mul_of_nonneg_left (APPTReview.tail_cauchy s) hc
    _ = _ := by rw [hss]; ring

end ExtractionLocalCap
