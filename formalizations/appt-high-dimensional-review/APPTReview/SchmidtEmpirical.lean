import APPTReview.LogScaleCoordinates
import APPTReview.PairLocalization

open scoped BigOperators NNReal
open MeasureTheory
namespace APPTReview

theorem unit_schmidt_entry_le_one {m : ℕ} (s : Fin m → ℝ)
    (hn : ∀ i,0≤s i) (hs : (∑ i,(s i)^2)=1) (i : Fin m) : s i≤1 := by
  have h := Finset.single_le_sum (fun j (_ : j∈Finset.univ) => sq_nonneg (s j)) (Finset.mem_univ i)
  rw [hs] at h
  nlinarith [hn i]

noncomputable def schmidtCoordinates {m : ℕ} (s : Fin m → ℝ)
    (hn : ∀ i,0≤s i) (hs : (∑ i,(s i)^2)=1) (L : ℝ) (hL : 0<L) :
    Fin m → ScaleInterval := fun i => schmidtScalePoint L (s i) hL (hn i) (unit_schmidt_entry_le_one s hn hs i)

noncomputable def schmidtEmpirical {m : ℕ} (s : Fin m → ℝ)
    (hn : ∀ i,0≤s i) (hs : (∑ i,(s i)^2)=1) (L : ℝ) (hL : 0<L) :
    ProbabilityMeasure ScaleInterval :=
  finiteAtomicProbability (fun i => (s i)^2) (schmidtCoordinates s hn hs L hL)
    (fun i => sq_nonneg (s i)) hs

theorem exp_half_square (a : ℝ) : (Real.exp (a/2))^2=Real.exp a := by
  rw [pow_two,← Real.exp_add]
  congr 1
  ring

/-- Coordinates below the logarithmic cutoff have uniformly vanishing total mass. -/
theorem small_schmidt_mass {m : ℕ} (s : Fin m → ℝ) (hn : ∀ i,0≤s i)
    (L η : ℝ) (hM : Real.exp L=(m:ℝ)) :
    (∑ i,if s i<Real.exp (-(1+η)*L/2) then (s i)^2 else 0)≤Real.exp (-η*L) := by
  have hle (i : Fin m) : (if s i<Real.exp (-(1+η)*L/2) then (s i)^2 else 0)≤Real.exp (-(1+η)*L) := by
    split_ifs with hi
    · rw [← exp_half_square]
      exact pow_le_pow_left₀ (hn i) hi.le 2
    · exact (Real.exp_pos _).le
  have hsum := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hle i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
  have he : (m:ℝ)*Real.exp (-(1+η)*L)=Real.exp (-η*L) := by
    rw [← hM,← Real.exp_add]
    congr 1
    ring
  exact hsum.trans_eq he

theorem schmidt_pair_square_mass {m : ℕ} (s : Fin m → ℝ)
    (hs : (∑ i,(s i)^2)=1) :
    (∑ p : UpperPair m,(s p.val.1*s p.val.2)^2)≤1/2 := by
  have h := upperPair_mass_le_half (fun i j => (s i)^2*(s j)^2)
    (fun i j => mul_comm _ _) (fun i => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  simp only [← Finset.mul_sum,← Finset.sum_mul,hs,mul_one] at h
  simpa only [mul_pow] using h

end APPTReview
