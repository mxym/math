import Entry005.IidTransport
import Mathlib.MeasureTheory.Integral.Pi

/-! The iid determinant second moment as an actual probability integral. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Entry005

variable {α : Type*} [MeasurableSpace α] {ν : Measure α} [IsProbabilityMeasure ν]

def sampledMatrix {n : ℕ} (X : α → Fin n → ℝ) (w : Fin n → α) :
    Matrix (Fin n) (Fin n) ℝ := fun i j => X (w j) i

def secondMomentMatrix {n : ℕ} (ν : Measure α) (X : α → Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ := fun i j => ∫ x, X x i * X x j ∂ν

theorem sampled_determinant_integrable {n : ℕ} (X : α → Fin n → ℝ)
    (hX : ∀ i, Integrable (fun x => X x i) ν) :
    Integrable (fun w : Fin n → α => (sampledMatrix X w).det) (iidLaw ν n) := by
  simp only [Matrix.det_apply', sampledMatrix]
  exact integrable_finsetSum _ fun p _ =>
    (Integrable.fintype_prod (fun i => hX (p i))).const_mul _

omit [MeasurableSpace α] in
theorem determinant_square_expansion {n : ℕ} (X : α → Fin n → ℝ) (w : Fin n → α) :
    (sampledMatrix X w).det ^ 2 =
      ∑ p : Equiv.Perm (Fin n), ∑ q : Equiv.Perm (Fin n),
        (((p.sign : ℤ) : ℝ) * ((q.sign : ℤ) : ℝ)) *
          ∏ i, (X (w i) (p i) * X (w i) (q i)) := by
  rw [pow_two, Matrix.det_apply']
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  simp only [sampledMatrix, Finset.prod_mul_distrib]
  ring

theorem determinant_moment_integral_expansion {n : ℕ} (X : α → Fin n → ℝ)
    (hpair : ∀ i j, Integrable (fun x => X x i * X x j) ν) :
    (∫ w : Fin n → α, (sampledMatrix X w).det ^ 2 ∂iidLaw ν n) =
      ∑ p : Equiv.Perm (Fin n), ∑ q : Equiv.Perm (Fin n),
        (((p.sign : ℤ) : ℝ) * ((q.sign : ℤ) : ℝ)) *
          ∏ i, secondMomentMatrix ν X (p i) (q i) := by
  have ht (p q : Equiv.Perm (Fin n)) :
      Integrable (fun w : Fin n → α =>
        (((p.sign : ℤ) : ℝ) * ((q.sign : ℤ) : ℝ)) *
          ∏ i, (X (w i) (p i) * X (w i) (q i))) (iidLaw ν n) :=
    (Integrable.fintype_prod (fun i => hpair (p i) (q i))).const_mul _
  simp_rw [determinant_square_expansion]
  rw [integral_finsetSum _ (fun p _ => integrable_finsetSum _ (fun q _ => ht p q))]
  apply Finset.sum_congr rfl
  intro p _
  rw [integral_finsetSum _ (fun q _ => ht p q)]
  apply Finset.sum_congr rfl
  intro q _
  rw [integral_const_mul]
  congr 1
  exact integral_fintype_prod_eq_prod (fun i x => X x (p i) * X x (q i))

theorem determinant_permutation_second_moment {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    (∑ p : Equiv.Perm (Fin n), ∑ q : Equiv.Perm (Fin n),
      (((p.sign : ℤ) : ℝ) * ((q.sign : ℤ) : ℝ)) * ∏ i, A (p i) (q i)) =
        (n.factorial : ℝ) * A.det := by
  have hinner (p : Equiv.Perm (Fin n)) :
      (∑ q : Equiv.Perm (Fin n), ((q.sign : ℤ) : ℝ) * ∏ i, A (p i) (q i)) =
        ((p.sign : ℤ) : ℝ) * A.det := by
    calc
      _ = (A.submatrix p id).transpose.det := by rw [Matrix.det_apply']; rfl
      _ = ((p.sign : ℤ) : ℝ) * A.det := by rw [Matrix.det_transpose, Matrix.det_permute]
  calc
    _ = ∑ p : Equiv.Perm (Fin n), ((p.sign : ℤ) : ℝ) *
        ∑ q : Equiv.Perm (Fin n), ((q.sign : ℤ) : ℝ) * ∏ i, A (p i) (q i) := by
      simp_rw [mul_assoc, Finset.mul_sum]
    _ = ∑ p : Equiv.Perm (Fin n), A.det := by
      apply Finset.sum_congr rfl
      intro p _
      rw [hinner, ← mul_assoc]
      have hs : ((p.sign : ℤ) : ℝ) * ((p.sign : ℤ) : ℝ) = 1 := by
        have h : (p.sign : ℤ) * (p.sign : ℤ) = 1 := by simp
        exact_mod_cast h
      rw [hs, one_mul]
    _ = (n.factorial : ℝ) * A.det := by simp [Fintype.card_perm]

theorem iid_determinant_second_moment {n : ℕ} (X : α → Fin n → ℝ)
    (hpair : ∀ i j, Integrable (fun x => X x i * X x j) ν) :
    (∫ w : Fin n → α, (sampledMatrix X w).det ^ 2 ∂iidLaw ν n) =
      (n.factorial : ℝ) * (secondMomentMatrix ν X).det := by
  rw [determinant_moment_integral_expansion X hpair]
  exact determinant_permutation_second_moment (secondMomentMatrix ν X)

theorem probability_integral_square_le {f : α → ℝ} (hf : Integrable f ν)
    (hf2 : Integrable (fun x => f x ^ 2) ν) :
    (∫ x, f x ∂ν) ^ 2 ≤ ∫ x, f x ^ 2 ∂ν := by
  let m := ∫ x, f x ∂ν
  have hpoint (x : α) : (f x - m) ^ 2 = f x ^ 2 - (2 * m) * f x + m ^ 2 := by ring
  have hvariance : (∫ x, (f x - m) ^ 2 ∂ν) = (∫ x, f x ^ 2 ∂ν) - m ^ 2 := by
    simp_rw [hpoint]
    rw [integral_add (f := fun x => f x ^ 2 - (2 * m) * f x) (g := fun _ => m ^ 2)
      (hf2.sub (hf.const_mul _)) (integrable_const _),
      integral_sub (f := fun x => f x ^ 2) (g := fun x => (2 * m) * f x)
        hf2 (hf.const_mul _), integral_const_mul]
    simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
    change (∫ x, f x ^ 2 ∂ν) - (2 * m) * m + m ^ 2 = _
    ring
  have hnonneg : 0 ≤ ∫ x, (f x - m) ^ 2 ∂ν := integral_nonneg (fun x => sq_nonneg (f x - m))
  rw [hvariance] at hnonneg
  exact sub_nonneg.1 hnonneg

theorem dot_square_expansion {n : ℕ} (u : Fin n → ℝ) (x : Fin n → ℝ) :
    (dotProduct u x) ^ 2 = ∑ i, ∑ j, (u i * u j) * (x i * x j) := by
  rw [dotProduct, pow_two, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [IsProbabilityMeasure ν] in
theorem dot_square_integrable {n : ℕ} (X : α → Fin n → ℝ) (u : Fin n → ℝ)
    (hpair : ∀ i j, Integrable (fun x => X x i * X x j) ν) :
    Integrable (fun x => (dotProduct u (X x)) ^ 2) ν := by
  simp_rw [dot_square_expansion]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (hpair i j).const_mul _

omit [IsProbabilityMeasure ν] in
theorem integral_dot_square {n : ℕ} (X : α → Fin n → ℝ) (u : Fin n → ℝ)
    (hpair : ∀ i j, Integrable (fun x => X x i * X x j) ν) :
    (∫ x, (dotProduct u (X x)) ^ 2 ∂ν) =
      dotProduct u ((secondMomentMatrix ν X).mulVec u) := by
  simp_rw [dot_square_expansion]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ =>
    (hpair i j).const_mul _)]
  simp_rw [integral_finsetSum _ (fun j _ => (hpair _ j).const_mul _), integral_const_mul]
  simp only [dotProduct, Matrix.mulVec, secondMomentMatrix, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

def liftedCoordinates {d : ℕ} (X : α → Fin d → ℝ) (x : α) : Fin (d + 1) → ℝ :=
  Fin.cases 1 (X x)

theorem centered_lifted_moment_det {d : ℕ} (X : α → Fin d → ℝ)
    (hcenter : ∀ i, (∫ x, X x i ∂ν) = 0) :
    (secondMomentMatrix ν (liftedCoordinates X)).det = (secondMomentMatrix ν X).det := by
  let A := secondMomentMatrix ν (liftedCoordinates X)
  have hminor : A.submatrix (0 : Fin (d + 1)).succAbove Fin.succ = secondMomentMatrix ν X := by
    ext i j
    simp [A, secondMomentMatrix, liftedCoordinates, Matrix.submatrix]
  change A.det = _
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ, hminor]
  have h00 : A 0 0 = 1 := by simp [A, secondMomentMatrix, liftedCoordinates]
  have hcol (i : Fin d) : A i.succ 0 = 0 := by
    simp [A, secondMomentMatrix, liftedCoordinates, hcenter i]
  simp [h00, hcol]

theorem centered_lifted_determinant_second_moment {d : ℕ} (X : α → Fin d → ℝ)
    (hX : ∀ i, Integrable (fun x => X x i) ν)
    (hcenter : ∀ i, (∫ x, X x i ∂ν) = 0)
    (hpair : ∀ i j, Integrable (fun x => X x i * X x j) ν) :
    (∫ w : Fin (d + 1) → α,
      |liftedDeterminant (fun i => X (w i.succ)) (X (w 0))| ^ 2 ∂iidLaw ν (d + 1)) =
      ((d + 1).factorial : ℝ) * (secondMomentMatrix ν X).det := by
  have hpairLift (i j : Fin (d + 1)) :
      Integrable (fun x => liftedCoordinates X x i * liftedCoordinates X x j) ν := by
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => simp [liftedCoordinates]
      | succ j => simpa [liftedCoordinates] using hX j
    | succ i =>
      induction j using Fin.cases with
      | zero => simpa [liftedCoordinates] using hX i
      | succ j => simpa [liftedCoordinates] using hpair i j
  have hmatrix (w : Fin (d + 1) → α) : sampledMatrix (liftedCoordinates X) w =
      witnessMatrix (fun i => X (w i.succ)) (X (w 0)) := by
    ext i j
    induction j using Fin.cases <;> simp [sampledMatrix, liftedCoordinates, witnessMatrix]
  have h := iid_determinant_second_moment (liftedCoordinates X) hpairLift
  simp only [hmatrix, centered_lifted_moment_det X hcenter] at h
  simpa only [sq_abs, liftedDeterminant] using h

end Entry005
