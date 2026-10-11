import APPTReview.AsymptoticUpper
import Mathlib.Order.Interval.Finset.Fin

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

/-- The all-ones test retains the linear gap budget, not only a norm bound. -/
theorem gap_mass_cap {m : ℕ} (G : Matrix (Fin m) (Fin m) ℝ) (c : ℝ)
    (hs : ∀ i j, G i j=G j i) (hd : ∀ i, G i i=0)
    (hp : (c • (1 : Matrix (Fin m) (Fin m) ℝ)-G).PosSemidef) :
    2*(∑ p : UpperPair m, G p.val.1 p.val.2) ≤ (m:ℝ)*c := by
  have hq := hp.dotProduct_mulVec_nonneg (fun _ => (1:ℝ))
  have he := symmetric_degree_mass G hs hd
  simp [dotProduct, Matrix.mulVec, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply, Finset.sum_sub_distrib] at hq
  nlinarith

/-- The last large eigenvalue and the paper's lower-tail pivot bound a bulk
interval of ratio (m+1)/(m-1). All eigenvalue placement is physical. -/
theorem density_appt_bulk_ratio {m n : ℕ} (hm : 2≤m) (hmn : m≤n)
    {A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) (happt : APPT.Quantum.AbsolutelyPPT A)
    (hR : 0<Fintype.card (UpperPair m)) :
    ((m:ℝ)-1) * hρ.1.isHermitian.eigenvalues₀
      (finalTop hR (gapPrefixBound hmn)) ≤
      ((m:ℝ)+1)*hρ.1.isHermitian.eigenvalues₀ (pairedPivot (by omega) hmn) := by
  let R := Fintype.card (UpperPair m)
  let f := hρ.1.isHermitian.eigenvalues₀
  let b := f (pairedPivot (by omega) hmn)
  let t := f (finalTop hR (gapPrefixBound hmn))
  let G := gapMatrix (placedSpectrum hmn (rowRank m) f)
  have hw := appt_all_ordered_pair_witnesses hmn hρ.1.isHermitian happt (rowRank m)
  have hG := gapMatrix_hermitian _ hw
  have hsym (i j : Fin m) : G i j=G j i := by
    have he := congrArg (fun M => M j i) hG.eq
    simpa [Matrix.conjTranspose_apply] using he
  have hcap := gap_mass_cap G (2*b) hsym (gapMatrix_diag _)
    (witness_gap_psd_bound _ b hw
      (placedSpectrum_diagonal_le (by omega) hmn (rowRank m) f
        hρ.1.isHermitian.eigenvalues₀_antitone))
  have hsum : (∑ p : UpperPair m, G p.val.1 p.val.2) =
      ∑ i : Fin R, sortedGap (gapPrefixBound hmn) f i := by
    dsimp only [G]
    simp_rw [placed_gap_eq_sortedGap]
    exact (rowRank m).sum_comp _
  rw [hsum] at hcap
  have hlo (i : Fin R) : t-b ≤ sortedGap (gapPrefixBound hmn) f i := by
    have htop : t ≤ f (Fin.castLE (gapPrefixBound hmn) i) := by
      apply hρ.1.isHermitian.eigenvalues₀_antitone
      change i.val ≤ R-1
      omega
    have hbot : f (Fin.rev (Fin.castLE (gapPrefixBound hmn) i)) ≤ b := by
      apply hρ.1.isHermitian.eigenvalues₀_antitone
      change Fintype.card (Fin m × Fin n)-R-m ≤
        Fintype.card (Fin m × Fin n)-(i.val+1)
      have hi := i.isLt
      have hc := pairPlacementBound hmn
      omega
    dsimp [sortedGap]
    linarith
  have hl := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hlo i)
  have hl' : (R:ℝ)*(t-b) ≤ ∑ i : Fin R, sortedGap (gapPrefixBound hmn) f i := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hl
    exact hl
  have hcN := upperPair_card m
  have hc : 2*(R:ℝ)+(m:ℝ)=(m:ℝ)^2 := by
    dsimp [R]
    simpa only [pow_two] using (show 2*(Fintype.card (UpperPair m):ℝ)+(m:ℝ)=(m:ℝ)*(m:ℝ) by exact_mod_cast hcN)
  have hmR : (0:ℝ)<m := by exact_mod_cast (by omega : 0<m)
  change ((m:ℝ)-1)*t ≤ ((m:ℝ)+1)*b
  by_contra hbad
  have hneg : 0<(m:ℝ)*(((m:ℝ)-1)*t-((m:ℝ)+1)*b) :=
    mul_pos hmR (sub_pos.mpr (lt_of_not_ge hbad))
  have he : (m:ℝ)*(((m:ℝ)-1)*t-((m:ℝ)+1)*b) =
      2*(R:ℝ)*(t-b)-2*(m:ℝ)*b := by
    have heq := congrArg (fun x : ℝ => x*(t-b)) hc
    nlinarith [heq]
  rw [he] at hneg
  nlinarith

end APPTReview
