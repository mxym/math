import MinimaxProfile.UniversalFinite
import SpectralProtocol.MultisectorMass
import Mathlib.Tactic.NoncommRing

open scoped BigOperators ComplexOrder
open Matrix
namespace OperationalCompletion
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual orthogonal sector between two nested source projections. -/
def projectionDifference (P Q : Matrix ι ι ℂ) : Matrix ι ι ℂ := Q-P

theorem projectionDifference_hermitian (P Q : Matrix ι ι ℂ)
    (hP : P.IsHermitian) (hQ : Q.IsHermitian) :
    (projectionDifference P Q).IsHermitian := hQ.sub hP

theorem projectionDifference_idempotent (P Q : Matrix ι ι ℂ)
    (hP : P*P=P) (hQ : Q*Q=Q) (hPQ : P*Q=P) (hQP : Q*P=P) :
    projectionDifference P Q * projectionDifference P Q = projectionDifference P Q := by
  unfold projectionDifference
  rw [sub_mul,mul_sub,mul_sub,hP,hQ,hPQ,hQP]
  abel

theorem projectionDifference_rank_le (P Q : Matrix ι ι ℂ) (hQ : Q*Q=Q)
    (hPQ : P*Q=P) : (projectionDifference P Q).rank ≤ Q.rank := by
  have h : projectionDifference P Q * Q = projectionDifference P Q := by
    simp only [projectionDifference,sub_mul,hQ,hPQ]
  rw [← h]
  exact Matrix.rank_mul_le_right _ _

theorem projectionDifferences_orthogonal (P Q R S : Matrix ι ι ℂ)
    (hPR : P*R=P) (hPS : P*S=P) (hQR : Q*R=Q) (hQS : Q*S=Q) :
    projectionDifference P Q * projectionDifference R S = 0 := by
  simp only [projectionDifference,sub_mul,mul_sub,hPR,hPS,hQR,hQS,sub_self]

def chainSector (P : ℕ → Matrix ι ι ℂ) (j : ℕ) : Matrix ι ι ℂ :=
  projectionDifference (P j) (P (j+1))

theorem chainSector_sum (P : ℕ → Matrix ι ι ℂ) (J : ℕ) :
    (∑ j : Fin J, chainSector P j) = P J - P 0 := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Fin.sum_univ_castSucc]
    change (∑ j : Fin J, chainSector P j) + chainSector P J = _
    rw [ih]
    unfold chainSector projectionDifference
    abel

theorem chainSector_orthogonal (P : ℕ → Matrix ι ι ℂ)
    (hP : ∀ j,(P j).IsHermitian)
    (hnest : ∀ i j,i≤j → P i*P j=P i)
    (i j : ℕ) (hij : i≠j) : chainSector P i * chainSector P j=0 := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact projectionDifferences_orthogonal _ _ _ _
      (hnest _ _ (by omega)) (hnest _ _ (by omega))
      (hnest _ _ (by omega)) (hnest _ _ (by omega))
  · have hrev : chainSector P j * chainSector P i=0 :=
      projectionDifferences_orthogonal _ _ _ _
        (hnest _ _ (by omega)) (hnest _ _ (by omega))
        (hnest _ _ (by omega)) (hnest _ _ (by omega))
    have hc := congrArg Matrix.conjTranspose hrev
    have hi : (chainSector P i).IsHermitian :=
      projectionDifference_hermitian _ _ (hP i) (hP (i+1))
    have hj : (chainSector P j).IsHermitian :=
      projectionDifference_hermitian _ _ (hP j) (hP (j+1))
    simpa only [Matrix.conjTranspose_mul,Matrix.conjTranspose_zero,
      hi.eq,hj.eq] using hc

end
end OperationalCompletion
