import GaussianAllCellsFlux

/-! Adding the negative sum of a linearly independent row family produces
an affinely independent centered simplex. This is the nondegeneracy step in
the principal-block Gaussian covariance realization. -/
open MeasureTheory ProbabilityTheory Set Module Matrix
open scoped RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d n : ℕ}

noncomputable def centeredRowFamily (r : Fin n → Space d) : Fin (n+1) → Space d :=
  Fin.cons (-(∑ i, r i)) r

lemma centeredRowFamily_sum (r : Fin n → Space d) : ∑ i, centeredRowFamily r i = 0 := by
  simp [centeredRowFamily,Fin.sum_univ_succ]

theorem centeredRowFamily_affineIndependent (r : Fin n → Space d)
    (hr : LinearIndependent ℝ r) : AffineIndependent ℝ (centeredRowFamily r) := by
  classical
  apply (affineIndependent_iff_of_fintype ℝ _).mpr
  intro g hg hc
  rw [Finset.weightedVSub_eq_linear_combination _ hg] at hc
  have hcoeff : (∑ i : Fin n, (g i.succ-g 0) • r i) = 0 := by
    rw [Fin.sum_univ_succ] at hc
    simp only [centeredRowFamily,Fin.cons_zero,Fin.cons_succ,smul_neg,Finset.smul_sum] at hc
    simp only [sub_smul,Finset.sum_sub_distrib]
    convert hc using 1
    abel
  have hci := (Fintype.linearIndependent_iff.mp hr) (fun i => g i.succ-g 0) hcoeff
  have hi (i : Fin n) : g i.succ = g 0 := sub_eq_zero.mp (hci i)
  rw [Fin.sum_univ_succ] at hg
  simp_rw [hi] at hg
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hg
  have h0 : g 0 = 0 := by
    have hh : ((n:ℝ)+1)*g 0 = 0 := by linarith
    exact (mul_eq_zero.mp hh).resolve_left (by positivity)
  intro i
  exact Fin.cases h0 (fun j => (hi j).trans h0) i

end GaussianMeasureBridge
