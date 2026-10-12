import GaussianCenteredRowIndependence
import GaussianMinimalCovarianceRows
import GaussianActualEnvelope

/-! A symmetric centered covariance is determined by its principal block.
The centered-row operation also preserves genuine differentiable score paths. -/
open MeasureTheory ProbabilityTheory Set Module Matrix Filter
open scoped RealInnerProductSpace Topology
namespace GaussianMeasureBridge
variable {d n : ℕ} [NeZero n]

theorem centered_covariance_ext
    (Q R : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hQ : Q.IsHermitian) (hR : R.IsHermitian)
    (hzQ : ∀ i, (∑ j,Q i j) = 0) (hzR : ∀ i, (∑ j,R i j) = 0)
    (hp : principalCovariance Q = principalCovariance R) : Q = R := by
  have hsQ (i j : Fin (n+1)) : Q i j = Q j i := by simpa using hQ.apply j i
  have hsR (i j : Fin (n+1)) : R i j = R j i := by simpa using hR.apply j i
  have hrQ (i : Fin (n+1)) : Q i 0 = -(∑ j : Fin n,Q i j.succ) := by
    have h := hzQ i; rw [Fin.sum_univ_succ] at h; linarith
  have hrR (i : Fin (n+1)) : R i 0 = -(∑ j : Fin n,R i j.succ) := by
    have h := hzR i; rw [Fin.sum_univ_succ] at h; linarith
  have hss (i j : Fin n) : Q i.succ j.succ = R i.succ j.succ :=
    congrArg (fun A => A i j) hp
  have hs0 (i : Fin n) : Q i.succ 0 = R i.succ 0 := by
    rw [hrQ,hrR]
    exact congrArg Neg.neg (Finset.sum_congr rfl fun j _ => hss i j)
  have h0s (j : Fin n) : Q 0 j.succ = R 0 j.succ := by rw [hsQ,hsR]; exact hs0 j
  have h00 : Q 0 0 = R 0 0 := by
    rw [hrQ,hrR]
    exact congrArg Neg.neg (Finset.sum_congr rfl fun j _ => h0s j)
  ext i j
  cases i using Fin.cases with
  | zero => exact Fin.cases h00 h0s j
  | succ i => exact Fin.cases (hs0 i) (hss i) j

lemma centeredRowFamily_gram_centered (r : Fin n → Space d) (i : Fin (n+1)) :
    (∑ j, scoreGram (centeredRowFamily r) i j) = 0 := by
  simp only [scoreGram,← inner_sum,centeredRowFamily_sum,inner_zero_right]

lemma centeredRowFamily_gram_principal (r : Fin n → Space d) :
    principalCovariance (scoreGram (centeredRowFamily r)) = scoreGram r := by
  ext i j
  rfl

theorem centeredRowFamily_path_hasDerivAt (r : ℝ → Fin n → Space d)
    (h : Fin n → Space d) (t : ℝ) (hd : HasDerivAt r h t) :
    HasDerivAt (fun s => centeredRowFamily (r s)) (centeredRowFamily h) t := by
  apply hasDerivAt_pi.mpr
  intro i
  cases i using Fin.cases with
  | zero =>
    exact (HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => hasDerivAt_pi.mp hd j)).neg
  | succ i => exact hasDerivAt_pi.mp hd i

end GaussianMeasureBridge
