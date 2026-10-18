import SchurCompletion.HaarSubgroupAverage

open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix MeasureTheory

namespace ExtractionSchur
open SymmetricSupport ExtractionSpectrum ExtractionRankSupport
noncomputable section
set_option backward.isDefEq.respectTransparency false

def frontMinor (D s : ℕ) (hsD : s ≤ D) (A : Matrix (Fin s) (Fin D) ℂ) :
    Matrix (Fin s) (Fin s) ℂ := A.submatrix id (coordinateLetterEmbedding hsD)

def principalMinor (D s : ℕ) (hsD : s ≤ D) (U : OneCopyUnitary D) :
    Matrix (Fin s) (Fin s) ℂ :=
  (U : Matrix (Fin D) (Fin D) ℂ).submatrix (coordinateLetterEmbedding hsD)
    (coordinateLetterEmbedding hsD)

def minorObservable (D s k : ℕ) (hsD : s ≤ D) (U : OneCopyUnitary D) : ℂ :=
  (Complex.normSq (principalMinor D s hsD U).det : ℂ)^k

def haarMinorMoment (D s k : ℕ) (hsD : s ≤ D) : ℂ :=
  ∫ U, minorObservable D s k hsD U ∂unitaryHaar D

theorem continuous_minorObservable (D s k : ℕ) (hsD : s ≤ D) :
    Continuous (minorObservable D s k hsD) := by
  unfold minorObservable principalMinor
  fun_prop

theorem normSq_unitary_det (D : ℕ) (U : OneCopyUnitary D) :
    Complex.normSq (U : Matrix (Fin D) (Fin D) ℂ).det = 1 := by
  have h := congrArg Matrix.det U.prop.1
  simp only [Matrix.star_eq_conjTranspose, Matrix.det_mul, Matrix.det_conjTranspose,
    Matrix.det_one] at h
  have h' : (Complex.normSq (U : Matrix (Fin D) (Fin D) ℂ).det : ℂ) = 1 := by
    rw [Complex.normSq_eq_conj_mul_self]
    exact h
  exact_mod_cast h'

theorem frontMinor_left_mul (D s : ℕ) (hsD : s ≤ D)
    (W : Matrix (Fin s) (Fin s) ℂ) (A : Matrix (Fin s) (Fin D) ℂ) :
    frontMinor D s hsD (W*A) = W * frontMinor D s hsD A := by
  ext i j
  rfl

theorem coisometry_frontMinor_moment (D s k : ℕ) (hsD : s ≤ D)
    (A : Matrix (Fin s) (Fin D) ℂ) (hA : A*Aᴴ = 1) :
    (∫ U : OneCopyUnitary D,
      (Complex.normSq (frontMinor D s hsD (A * (U : Matrix (Fin D) (Fin D) ℂ))).det : ℂ)^k
      ∂unitaryHaar D) = haarMinorMoment D s k hsD := by
  let C := Extraction.coordinateIsometry (coordinateLetterEmbedding hsD)
  have hC : Cᴴ*C = 1 := Extraction.coordinateIsometry_isometry _
  obtain ⟨W,hW⟩ := Extraction.exists_unitary_between_isometries C Aᴴ hC
    (by simpa only [Matrix.conjTranspose_conjTranspose] using hA)
  have hAC : A = Cᴴ * (W : Matrix (Fin D) (Fin D) ℂ)ᴴ := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] using
      (congrArg Matrix.conjTranspose hW).symm
  have he (U : OneCopyUnitary D) :
      frontMinor D s hsD (A * (U : Matrix (Fin D) (Fin D) ℂ)) =
        principalMinor D s hsD (W⁻¹ * U) := by
    rw [hAC]
    simp only [frontMinor, principalMinor, Matrix.UnitaryGroup.mul_val,
      Matrix.UnitaryGroup.inv_val, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
    ext i j
    simp [C, Extraction.coordinateIsometry, Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp_rw [he]
  change (∫ U, minorObservable D s k hsD (W⁻¹ * U) ∂unitaryHaar D) = _
  exact integral_mul_left_eq_self _ _

theorem haarMinorMoment_zero_degree (D s : ℕ) (hsD : s ≤ D) :
    haarMinorMoment D s 0 hsD = 1 := by
  simp [haarMinorMoment, minorObservable]

theorem haarMinorMoment_zero_rank (D k : ℕ) : haarMinorMoment D 0 k (Nat.zero_le D) = 1 := by
  simp [haarMinorMoment, minorObservable, Matrix.det_isEmpty]


/-- The first-column stabilizer reduces a genuine principal-minor moment
by one row and one column. The required alignments and coisometries are
constructed internally, including zero first columns and degree zero. -/
theorem coisometry_fixFirst_minor_moment (n s k : ℕ) (hs : s ≤ n)
    (A : Matrix (Fin (s+1)) (Fin (n+1)) ℂ) (hA : A*Aᴴ = 1) :
    (∫ V : OneCopyUnitary n,
      (Complex.normSq (frontMinor (n+1) (s+1) (Nat.add_le_add_right hs 1)
        (A * fixFirstMatrix n V)).det : ℂ)^k ∂unitaryHaar n) =
      (columnEnergy (fun i => A i 0) : ℂ)^k * haarMinorMoment n s k hs := by
  let b : Fin (s+1) → ℂ := fun i => A i 0
  let r : ℂ := Real.sqrt (columnEnergy b)
  obtain ⟨W,hW⟩ := exists_unitary_align_column s b
  let B := (W : Matrix (Fin (s+1)) (Fin (s+1)) ℂ) * A
  have hB : B*Bᴴ = 1 := by
    simp only [B, Matrix.conjTranspose_mul]
    calc
      _ = (W : Matrix (Fin (s+1)) (Fin (s+1)) ℂ) * (A*Aᴴ) *
          (W : Matrix (Fin (s+1)) (Fin (s+1)) ℂ)ᴴ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hA, Matrix.mul_one]; exact W.prop.2
  have hcol (i : Fin (s+1)) : B i 0 = if i = 0 then r else 0 := hW i
  let C : Matrix (Fin s) (Fin n) ℂ := B.submatrix Fin.succ Fin.succ
  have hC : C*Cᴴ = 1 := by
    ext i j
    have h := congrArg (fun M : Matrix (Fin (s+1)) (Fin (s+1)) ℂ => M i.succ j.succ) hB
    simpa [C, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ,
      hcol, Matrix.one_apply, ne_comm] using h
  have he (V : OneCopyUnitary n) :
      (Complex.normSq (frontMinor (n+1) (s+1) (Nat.add_le_add_right hs 1)
          (A * fixFirstMatrix n V)).det : ℂ)^k =
        (columnEnergy b : ℂ)^k *
          (Complex.normSq (frontMinor n s hs (C * (V : Matrix (Fin n) (Fin n) ℂ))).det : ℂ)^k := by
    let M₀ := frontMinor (n+1) (s+1) (Nat.add_le_add_right hs 1) (A * fixFirstMatrix n V)
    let M₁ := frontMinor (n+1) (s+1) (Nat.add_le_add_right hs 1) (B * fixFirstMatrix n V)
    have hM : M₁ = (W : Matrix (Fin (s+1)) (Fin (s+1)) ℂ) * M₀ := by
      dsimp only [M₀, M₁, B]
      rw [Matrix.mul_assoc, frontMinor_left_mul]
    have hd : Complex.normSq M₁.det = Complex.normSq M₀.det := by
      rw [hM, Matrix.det_mul, Complex.normSq_mul, normSq_unitary_det, one_mul]
    have hfirst (i : Fin (s+1)) : M₁ i 0 = if i = 0 then r else 0 := by
      change (B * fixFirstMatrix n V) i 0 = _
      simpa [Matrix.mul_apply, fixFirstMatrix, Matrix.of_apply, Fin.sum_univ_succ] using hcol i
    have hbottom : M₁.submatrix Fin.succ Fin.succ =
        frontMinor n s hs (C * (V : Matrix (Fin n) (Fin n) ℂ)) := by
      ext i j
      change (B * fixFirstMatrix n V) i.succ (coordinateLetterEmbedding hs j).succ =
        (C * (V : Matrix (Fin n) (Fin n) ℂ)) i (coordinateLetterEmbedding hs j)
      simp [Matrix.mul_apply, fixFirstMatrix, Matrix.of_apply, Fin.sum_univ_succ, C]
    have hdet : M₁.det = r * (frontMinor n s hs (C * (V : Matrix (Fin n) (Fin n) ℂ))).det := by
      rw [Matrix.det_succ_column_zero]
      simp [hfirst, hbottom]
    have hr : Complex.normSq r = columnEnergy b := by
      dsimp only [r]
      rw [Complex.normSq_ofReal]
      exact Real.mul_self_sqrt (columnEnergy_nonneg b)
    change (Complex.normSq M₀.det : ℂ)^k = _
    rw [← hd, hdet, Complex.normSq_mul, hr, Complex.ofReal_mul, mul_pow]
  simp_rw [he]
  rw [integral_const_mul, coisometry_frontMinor_moment n s k hs C hC]


theorem coordinateRankProjection_trace_entries (D s : ℕ) (hsD : s ≤ D)
    (Q : Matrix (Fin D) (Fin D) ℂ) :
    (coordinateRankProjection D s hsD * Q).trace =
      ∑ i : Fin s, Q (coordinateLetterEmbedding hsD i) (coordinateLetterEmbedding hsD i) := by
  rw [coordinateRankProjection, Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp [Extraction.coordinateIsometry, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply]

theorem unitaryPureEntry_eq_normSq (D : ℕ) (a b : Fin D) (U : OneCopyUnitary D) :
    unitaryPureEntry D a b U =
      (Complex.normSq ((U : Matrix (Fin D) (Fin D) ℂ) b a) : ℂ) := by
  rw [unitaryPureEntry, coordinatePureProjection_eq_single]
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.single,
    ite_and, Complex.star_def, Complex.mul_conj]

theorem columnEnergy_eq_projection_trace (D s : ℕ) (hsD : s ≤ D)
    (a : Fin D) (U : OneCopyUnitary D) :
    (columnEnergy (fun i : Fin s => (U : Matrix (Fin D) (Fin D) ℂ)
      (coordinateLetterEmbedding hsD i) a) : ℂ) =
      (coordinateRankProjection D s hsD *
        ((U : Matrix (Fin D) (Fin D) ℂ) * coordinatePureProjection D a *
          (U : Matrix (Fin D) (Fin D) ℂ)ᴴ)).trace := by
  rw [coordinateRankProjection_trace_entries]
  simp only [columnEnergy, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact (unitaryPureEntry_eq_normSq D a (coordinateLetterEmbedding hsD i) U).symm

/-- Genuine Haar principal-minor moments obey the one-column beta recursion.
The complete internal proof uses actual subgroup averaging, not a supplied
Jacobi law or rectangular Schur dimension. -/
theorem haarMinorMoment_succ (n s k : ℕ) (hs : s ≤ n) :
    haarMinorMoment (n+1) (s+1) k (Nat.add_le_add_right hs 1) =
      (((s+k).choose k : ℂ) / ((n+k).choose k : ℂ)) * haarMinorMoment n s k hs := by
  have havg := unitaryHaar_right_double_average (n+1) n (fixFirstUnitary n)
    (continuous_fixFirstUnitary n) (minorObservable (n+1) (s+1) k (Nat.add_le_add_right hs 1))
    (continuous_minorObservable (n+1) (s+1) k (Nat.add_le_add_right hs 1))
  have hinner (U : OneCopyUnitary (n+1)) :
      (∫ V, minorObservable (n+1) (s+1) k (Nat.add_le_add_right hs 1)
        (U * fixFirstUnitary n V) ∂unitaryHaar n) =
        (columnEnergy (fun i : Fin (s+1) => (U : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
          (coordinateLetterEmbedding (Nat.add_le_add_right hs 1) i) 0) : ℂ)^k *
          haarMinorMoment n s k hs := by
    let A : Matrix (Fin (s+1)) (Fin (n+1)) ℂ :=
      (U : Matrix (Fin (n+1)) (Fin (n+1)) ℂ).submatrix
        (coordinateLetterEmbedding (Nat.add_le_add_right hs 1)) id
    have hA : A*Aᴴ = 1 := by
      ext i j
      have h := congrArg (fun M : Matrix (Fin (n+1)) (Fin (n+1)) ℂ =>
        M (coordinateLetterEmbedding (Nat.add_le_add_right hs 1) i)
          (coordinateLetterEmbedding (Nat.add_le_add_right hs 1) j)) U.prop.2
      simpa only [A, Matrix.star_eq_conjTranspose, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Matrix.submatrix_apply, id_eq, Matrix.one_apply,
        (coordinateLetterEmbedding (Nat.add_le_add_right hs 1)).injective.eq_iff] using h
    have he (V : OneCopyUnitary n) :
        principalMinor (n+1) (s+1) (Nat.add_le_add_right hs 1) (U * fixFirstUnitary n V) =
          frontMinor (n+1) (s+1) (Nat.add_le_add_right hs 1) (A * fixFirstMatrix n V) := by
      ext i j
      rfl
    simp only [minorObservable, he]
    exact coisometry_fixFirst_minor_moment n s k hs A hA
  unfold haarMinorMoment at havg ⊢
  rw [← havg]
  simp_rw [hinner, columnEnergy_eq_projection_trace]
  rw [integral_mul_const, unitary_column_projection_power_moment]
  simp only [show s+1+k-1 = s+k by omega, show n+1+k-1 = n+k by omega]
  rfl

/-- Exact all-rank principal-minor moments, derived entirely from genuine
unitary Haar integration. This is a rectangular moment identity, not a
classification of all tensor Schur blocks. -/
theorem haarMinorMoment_product (t s k : ℕ) :
    haarMinorMoment (t+s) s k (by omega) =
      ∏ i ∈ Finset.range s,
        (((i+k).choose k : ℂ) / ((t+i+k).choose k : ℂ)) := by
  induction s with
  | zero => simp [haarMinorMoment_zero_rank]
  | succ s ih =>
    have h := haarMinorMoment_succ (t+s) s k (by omega)
    rw [ih] at h
    rw [Finset.prod_range_succ]
    simpa only [Nat.add_assoc, mul_comm] using h

end
end ExtractionSchur
