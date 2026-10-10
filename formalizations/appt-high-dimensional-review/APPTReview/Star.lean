import APPTReview.QuantumWitness

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

/-- Entrywise comparison is valid for quadratic forms on nonnegative real vectors. -/
theorem quadratic_mono_nonneg {ι : Type*} [Fintype ι]
    (M N : Matrix ι ι ℝ) (x : ι → ℝ)
    (hMN : ∀ i j, M i j ≤ N i j) (hx : ∀ i, 0 ≤ x i) :
    star x ⬝ᵥ (M *ᵥ x) ≤ star x ⬝ᵥ (N *ᵥ x) := by
  simp only [dotProduct, Matrix.mulVec, star_trivial]
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (hx i)
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_right (hMN i j) (hx j)

def starVector {n : ℕ} (z : ℝ) (u : Fin n → ℝ) : Fin (n+1) → ℝ :=
  Fin.cases z u
@[simp] theorem starVector_zero {n : ℕ} (z : ℝ) (u : Fin n → ℝ) :
    starVector z u 0 = z := rfl
@[simp] theorem starVector_succ {n : ℕ} (z : ℝ) (u : Fin n → ℝ) (i : Fin n) :
    starVector z u i.succ = u i := rfl

def starMatrix {n : ℕ} (c b : ℝ) (u : Fin n → ℝ) :
    Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  fun i j => Fin.cases (Fin.cases (2*c) (fun j => -u j) j)
    (fun i => Fin.cases (-u i) (fun j => if i=j then 2*b else 0) j) i

/-- The chosen vector makes every leaf component vanish exactly. -/
theorem starMatrix_quadratic {n : ℕ} (c b : ℝ) (u : Fin n → ℝ) :
    star (starVector (2*b) u) ⬝ᵥ (starMatrix c b u *ᵥ starVector (2*b) u) =
      2*b*(4*c*b-∑ i, (u i)^2) := by
  have hm : starMatrix c b u *ᵥ starVector (2*b) u =
      starVector (4*c*b-∑ i, (u i)^2) (fun _ => 0) := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, starMatrix, starVector,
        neg_mul, Finset.sum_neg_distrib, pow_two]
      ring
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, starMatrix, starVector]
      ring
  rw [hm]
  simp [dotProduct, Fin.sum_univ_succ, starVector, star_trivial]

/-- Dimension-uniform real PSD star bound, retaining the actual central diagonal.
No eigenvalue or graph norm assumption replaces positivity of the matrix. -/
theorem psd_star_bound {n : ℕ} (M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hM : M.PosSemidef) (u : Fin n → ℝ) (hu : ∀ i, 0 ≤ u i)
    (c b : ℝ) (hb : 0 < b) (hc : M 0 0 ≤ 2*c)
    (hd : ∀ i : Fin n, M i.succ i.succ ≤ 2*b)
    (hs : ∀ i : Fin n, M 0 i.succ = -u i)
    (ho : ∀ i j : Fin n, i≠j → M i.succ j.succ ≤ 0) :
    (∑ i, (u i)^2) ≤ 4*c*b := by
  have hm : ∀ i j, M i j ≤ starMatrix c b u i j := by
    intro i j
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · exact hc
      · simpa [starMatrix] using le_of_eq (hs j)
    · refine Fin.cases ?_ (fun j => ?_) j
      · have he : M i.succ 0 = M 0 i.succ := by
          have he := congrArg (fun A => A 0 i.succ) hM.isHermitian.eq
          simpa [Matrix.conjTranspose_apply] using he
        simpa [starMatrix, he] using le_of_eq (hs i)
      · by_cases hij : i=j
        · subst j; simpa [starMatrix] using hd i
        · simpa [starMatrix, hij] using ho i j hij
  have hx : ∀ i, 0 ≤ starVector (2*b) u i := by
    intro i
    exact Fin.cases (by dsimp [starVector]; positivity) hu i
  have hp := (hM.dotProduct_mulVec_nonneg (starVector (2*b) u)).trans
    (quadratic_mono_nonneg M (starMatrix c b u) _ hm hx)
  rw [starMatrix_quadratic] at hp
  by_contra hbad
  have hneg : 4*c*b-∑ i, (u i)^2 < 0 := by linarith
  have hmul := mul_neg_of_pos_of_neg (show 0 < 2*b by positivity) hneg
  linarith

/-- The least-diagonal version in the normalization used by the entropy proof. -/
theorem psd_shifted_star_bound {n : ℕ}
    (M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hM : M.PosSemidef)
    (u : Fin n → ℝ) (hu : ∀ i, 0 ≤ u i) (y : ℝ)
    (hc : M 0 0 ≤ 2*(1-y))
    (hd : ∀ i : Fin n, M i.succ i.succ ≤ 2)
    (hs : ∀ i : Fin n, M 0 i.succ = -u i)
    (ho : ∀ i j : Fin n, i≠j → M i.succ j.succ ≤ 0) :
    (∑ i, (u i)^2) ≤ 4*(1-y) := by
  simpa using psd_star_bound M hM u hu (1-y) 1 (by norm_num) hc (by simpa using hd) hs ho

/-- Physical APPT star inequality in every finite rectangular dimension. -/
theorem diagonal_appt_star_bound {n : ℕ} {b : Type*} [Fintype b] [DecidableEq b]
    (d : Fin (n+1) × b → ℝ)
    (h : APPT.Quantum.AbsolutelyPPT (Matrix.diagonal (fun p => (d p : ℂ))))
    (e : Fin (n+1) → b) (he : Function.Injective e)
    (c t : ℝ) (ht : 0<t) (hc : d (0,e 0) ≤ c)
    (hd : ∀ i : Fin n, d (i.succ,e i.succ) ≤ t)
    (ho : ∀ i j : Fin (n+1), i<j → d (i,e j) ≤ d (j,e i)) :
    (∑ i : Fin n, (d (i.succ,e 0)-d (0,e i.succ))^2) ≤ 4*c*t := by
  let M := witnessMatrix (fun p : Fin (n+1) × Fin (n+1) => d (p.1,e p.2))
  have hu : ∀ i : Fin n, 0 ≤ d (i.succ,e 0)-d (0,e i.succ) := by
    intro i
    exact sub_nonneg.mpr (ho 0 i.succ (Fin.succ_pos i))
  apply psd_star_bound M (diagonal_appt_witness_posSemidef d h e he)
    (fun i => d (i.succ,e 0)-d (0,e i.succ)) hu c t ht
  · simpa [M, witnessMatrix] using mul_le_mul_of_nonneg_left hc (show (0:ℝ)≤2 by norm_num)
  · intro i
    simpa [M, witnessMatrix] using mul_le_mul_of_nonneg_left (hd i) (show (0:ℝ)≤2 by norm_num)
  · intro i
    have h0 : (0 : Fin (n+1)) ≠ i.succ := (Fin.succ_pos i).ne
    simp [M, witnessMatrix, h0, Fin.succ_pos, sub_eq_add_neg, add_comm]
  · intro i j hij
    by_cases hlt : i<j
    · simpa [M, witnessMatrix, hij, Fin.succ_inj, hlt] using sub_nonpos.mpr (ho i.succ j.succ (Fin.succ_lt_succ_iff.mpr hlt))
    · have hjlt : j < i := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hij)
      simpa [M, witnessMatrix, hij, Fin.succ_inj, hlt] using sub_nonpos.mpr (ho j.succ i.succ (Fin.succ_lt_succ_iff.mpr hjlt))
end APPTReview
