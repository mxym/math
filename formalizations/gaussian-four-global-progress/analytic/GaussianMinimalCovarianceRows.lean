import GaussianCovarianceValue

/-! A centered positive-semidefinite (n+1)-label covariance has an explicit
score realization in exactly n ambient dimensions. The principal block gives
the non-base rows; their negative sum gives the remaining row. -/
open MeasureTheory ProbabilityTheory Set Module Matrix
open scoped RealInnerProductSpace MatrixOrder
namespace GaussianMeasureBridge
variable {n : ℕ} [NeZero n]

noncomputable def principalCovariance (Q : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := Q.submatrix Fin.succ Fin.succ

noncomputable def minimalCovarianceRows (Q : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    Fin (n+1) → Space n :=
  Fin.cons (-(∑ i, covarianceRows (principalCovariance Q) i)) (covarianceRows (principalCovariance Q))

lemma minimalCovarianceRows_sum (Q : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    (∑ i, minimalCovarianceRows Q i) = 0 := by
  simp [minimalCovarianceRows,Fin.sum_univ_succ]

theorem scoreGram_minimalCovarianceRows
    (Q : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hQ : Q.PosSemidef)
    (hz : ∀ i, (∑ j, Q i j) = 0) : scoreGram (minimalCovarianceRows Q) = Q := by
  have hP : (principalCovariance Q).PosSemidef := hQ.submatrix Fin.succ
  have hg := scoreGram_covarianceRows (principalCovariance Q) hP
  have hs (i j : Fin (n+1)) : Q i j = Q j i := by
    simpa using hQ.isHermitian.apply j i
  have hr (i : Fin (n+1)) : (∑ j : Fin n, Q i j.succ) = -Q i 0 := by
    have hh := hz i
    rw [Fin.sum_univ_succ] at hh
    linarith
  have hc (j : Fin (n+1)) : (∑ i : Fin n, Q i.succ j) = -Q 0 j := by
    simp_rw [hs _ j]
    rw [hr,hs j 0]
  have hnorm (i j : Fin n) :
      ⟪covarianceRows (principalCovariance Q) i,covarianceRows (principalCovariance Q) j⟫ =
        Q i.succ j.succ := congrArg (fun A => A i j) hg
  ext i j
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero =>
      simp only [scoreGram,minimalCovarianceRows,Fin.cons_zero,inner_neg_left,inner_neg_right,
        neg_neg,sum_inner,inner_sum,hnorm]
      rw [Finset.sum_neg_distrib,neg_neg,Finset.sum_comm]
      calc
        (∑ i : Fin n, ∑ j : Fin n, Q i.succ j.succ) = ∑ i : Fin n, -Q i.succ 0 :=
          Finset.sum_congr rfl (fun i _ => hr i.succ)
        _ = -(∑ i : Fin n, Q i.succ 0) := by rw [Finset.sum_neg_distrib]
        _ = Q 0 0 := by rw [hc]; ring
    | succ j =>
      simp only [scoreGram,minimalCovarianceRows,Fin.cons_zero,Fin.cons_succ,inner_neg_left,
        sum_inner,hnorm,hc,neg_neg]
  | succ i =>
    cases j using Fin.cases with
    | zero =>
      simp only [scoreGram,minimalCovarianceRows,Fin.cons_zero,Fin.cons_succ,inner_neg_right,
        inner_sum,hnorm,hr,neg_neg]
    | succ j => exact hnorm i j

theorem covarianceValue_minimal_rows
    (Q : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hQ : Q.PosSemidef)
    (hz : ∀ i, (∑ j, Q i j) = 0) :
    covarianceValue Q = equalMassValue (minimalCovarianceRows Q) := by
  calc
    covarianceValue Q = covarianceValue (scoreGram (minimalCovarianceRows Q)) :=
      congrArg covarianceValue (scoreGram_minimalCovarianceRows Q hQ hz).symm
    _ = equalMassValue (minimalCovarianceRows Q) := covarianceValue_scoreGram _

end GaussianMeasureBridge
