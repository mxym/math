import SchurCompletion.GeneralPurity
import SchurCompletion.HaarTwirl

open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix MeasureTheory Filter

namespace ExtractionSchur
open SymmetricSupport ExtractionSpectrum ExtractionRankSupport
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem cyclic_tensor_product (s k : ℕ) [NeZero s] (x : Fin s → ℝ) (w : Word s k) :
    (∏ a : Fin s, ∏ r : Fin k, x (w r+a)) = (∏ i : Fin s, x i)^k := by
  rw [Finset.prod_comm]
  have he (r : Fin k) : (∏ a : Fin s, x (w r+a)) = ∏ i : Fin s, x i :=
    Equiv.prod_comp (Equiv.addLeft (w r)) x
  simp only [he, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem cyclic_tensor_mean_lower (s k q : ℕ) (hs : 0 < s) (hk : k ≤ s*q)
    (x : Fin s → ℝ) (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i ≤ 1) (w : Word s k) :
    (∏ i : Fin s, x i)^q ≤ (∑ a : Fin s, ∏ r : Fin k, x (w r+a))/(s : ℝ) := by
  letI : NeZero s := ⟨hs.ne'⟩
  have hp0 : 0 ≤ ∏ i : Fin s, x i := Finset.prod_nonneg (fun i hi => hx0 i)
  have hp1 : (∏ i : Fin s, x i) ≤ 1 := Finset.prod_le_one₀ (fun i hi => hx0 i) (fun i hi => hx1 i)
  have hmean0 : 0 ≤ (∑ a : Fin s, ∏ r : Fin k, x (w r+a))/(s : ℝ) :=
    div_nonneg (Finset.sum_nonneg (fun a ha => Finset.prod_nonneg (fun r hr => hx0 _))) (Nat.cast_nonneg _)
  have h := prod_le_arithmetic_mean_pow s hs (fun a => ∏ r : Fin k, x (w r+a))
    (fun a => Finset.prod_nonneg (fun r hr => hx0 _))
  rw [cyclic_tensor_product] at h
  have hp := pow_le_pow_of_le_one hp0 hp1 hk
  have hh : ((∏ i : Fin s, x i)^q)^s ≤
      ((∑ a : Fin s, ∏ r : Fin k, x (w r+a))/(s : ℝ))^s := by
    rw [← pow_mul, Nat.mul_comm q s]
    exact hp.trans h
  exact (pow_le_pow_iff_left₀ (pow_nonneg hp0 _) hmean0 hs.ne').mp hh

def permutationUnitary (s : ℕ) (σ : Equiv.Perm (Fin s)) : OneCopyUnitary s :=
  ⟨σ.permMatrix ℂ, by
    rw [Matrix.mem_unitaryGroup_iff]
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_permMatrix,
      ← Matrix.permMatrix_mul, inv_mul_cancel, mul_inv_cancel, Matrix.permMatrix_one]⟩

theorem permutationUnitary_diagonal (s : ℕ) (σ : Equiv.Perm (Fin s)) (x : Fin s → ℂ) :
    (permutationUnitary s σ : Matrix (Fin s) (Fin s) ℂ) * Matrix.diagonal x *
      (permutationUnitary s σ : Matrix (Fin s) (Fin s) ℂ)ᴴ = Matrix.diagonal (x ∘ σ) := by
  simp only [permutationUnitary, Matrix.conjTranspose_permMatrix]
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul,
    Equiv.Perm.permMatrix, PEquiv.mul_toMatrix_toPEquiv]
  ext i j
  simp [Matrix.diagonal_apply, Equiv.Perm.inv_def, σ.injective.eq_iff]

theorem tensorConjugate_right (D k : ℕ) (A : Matrix (Word D k) (Word D k) ℂ)
    (U V : OneCopyUnitary D) :
    tensorConjugate D k (tensorConjugate D k A V) U = tensorConjugate D k A (U*V) := by
  simp only [tensorConjugate, Matrix.UnitaryGroup.mul_val, tensorMatrix_mul,
    Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem haarTwirl_tensorConjugate (D k : ℕ) (A : Matrix (Word D k) (Word D k) ℂ)
    (V : OneCopyUnitary D) :
    haarTwirl D k (tensorConjugate D k A V) = haarTwirl D k A := by
  unfold haarTwirl
  simp_rw [tensorConjugate_right]
  exact integral_mul_right_eq_self _ _

theorem haarTwirl_sub (D k : ℕ) (A B : Matrix (Word D k) (Word D k) ℂ) :
    haarTwirl D k (A-B) = haarTwirl D k A-haarTwirl D k B := by
  simp only [haarTwirl, tensorConjugate, Matrix.mul_sub, Matrix.sub_mul]
  exact integral_sub (integrable_tensorConjugate D k A) (integrable_tensorConjugate D k B)

theorem haarTwirl_real_smul (D k : ℕ) (a : ℝ) (A : Matrix (Word D k) (Word D k) ℂ) :
    haarTwirl D k (a • A) = a • haarTwirl D k A := by
  simp only [haarTwirl, tensorConjugate, Matrix.mul_smul, Matrix.smul_mul, integral_smul]

theorem haarTwirl_posSemidef (D k : ℕ) (A : Matrix (Word D k) (Word D k) ℂ)
    (hA : A.PosSemidef) : (haarTwirl D k A).PosSemidef := by
  change (∫ U : OneCopyUnitary D, tensorConjugate D k A U ∂unitaryHaar D).PosSemidef
  exact (integral_nonneg (fun U : OneCopyUnitary D =>
    (hA.mul_mul_conjTranspose_same (tensorMatrix (U : Matrix (Fin D) (Fin D) ℂ) k)).nonneg)).posSemidef

def cyclicTensorMean (s k : ℕ) [NeZero s] (x : Fin s → ℝ) :
    Matrix (Word s k) (Word s k) ℂ :=
  (s : ℝ)⁻¹ • ∑ a : Fin s, tensorMatrix (Matrix.diagonal (fun i => (x (i+a) : ℂ))) k

theorem cyclicTensorMean_eq_diagonal (s k : ℕ) [NeZero s] (x : Fin s → ℝ) :
    cyclicTensorMean s k x = Matrix.diagonal (fun w : Word s k =>
      (((∑ a : Fin s, ∏ r : Fin k, x (w r+a))/(s : ℝ) : ℝ) : ℂ)) := by
  simp only [cyclicTensorMean, tensorMatrix_diagonal_complex]
  ext w v
  by_cases h : w=v
  · subst v
    simp [Matrix.smul_apply, Matrix.sum_apply, Matrix.diagonal_apply_eq, purePower,
      RCLike.real_smul_eq_coe_mul, div_eq_mul_inv, mul_comm, ← Complex.ofReal_prod,
      ← Complex.ofReal_sum]
  · simp [Matrix.smul_apply, Matrix.sum_apply, Matrix.diagonal_apply, h]

theorem cyclicTensorMean_lower (s k q : ℕ) (hs : 0 < s) (hk : k ≤ s*q)
    (x : Fin s → ℝ) (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i ≤ 1) :
    letI : NeZero s := ⟨hs.ne'⟩
    (cyclicTensorMean s k x - (∏ i : Fin s, x i)^q • (1 : Matrix (Word s k) (Word s k) ℂ)).PosSemidef := by
  letI : NeZero s := ⟨hs.ne'⟩
  rw [cyclicTensorMean_eq_diagonal]
  have he : Matrix.diagonal (fun w : Word s k =>
      (((∑ a : Fin s, ∏ r : Fin k, x (w r+a))/(s : ℝ) : ℝ) : ℂ)) -
      (∏ i : Fin s, x i)^q • (1 : Matrix (Word s k) (Word s k) ℂ) =
      Matrix.diagonal (fun w : Word s k =>
        ((((∑ a : Fin s, ∏ r : Fin k, x (w r+a))/(s : ℝ))-(∏ i : Fin s, x i)^q : ℝ) : ℂ)) := by
    ext w v
    by_cases h : w=v
    · subst v; simp [Matrix.smul_apply, RCLike.real_smul_eq_coe_mul]
    · simp [Matrix.diagonal_apply, Matrix.one_apply, h]
  rw [he]
  exact Matrix.posSemidef_diagonal_iff.mpr (fun w => by
    apply RCLike.nonneg_iff.mpr
    constructor
    · change (0 : ℝ) ≤ ((∑ a : Fin s, ∏ r : Fin k, x (w r+a))/(s : ℝ))-(∏ i : Fin s, x i)^q
      exact sub_nonneg.mpr (cyclic_tensor_mean_lower s k q hs hk x hx0 hx1 w)
    · rfl)

theorem haarTwirl_sum {ι : Type*} (D k : ℕ) (T : Finset ι)
    (A : ι → Matrix (Word D k) (Word D k) ℂ) :
    haarTwirl D k (∑ i ∈ T, A i) = ∑ i ∈ T, haarTwirl D k (A i) := by
  simp only [haarTwirl, tensorConjugate, Matrix.mul_sum, Matrix.sum_mul]
  exact integral_finset_sum T (fun i hi => integrable_tensorConjugate D k (A i))

theorem haarTwirl_cyclicTensorMean (s k : ℕ) (hs : 0 < s) (x : Fin s → ℝ) :
    letI : NeZero s := ⟨hs.ne'⟩
    haarTwirl s k (cyclicTensorMean s k x) =
      haarOrbitAverage s k (Matrix.diagonal (fun i => (x i : ℂ))) := by
  letI : NeZero s := ⟨hs.ne'⟩
  have he (a : Fin s) :
      tensorMatrix (Matrix.diagonal (fun i => (x (i+a) : ℂ))) k =
        tensorConjugate s k (tensorMatrix (Matrix.diagonal (fun i => (x i : ℂ))) k)
          (permutationUnitary s (Equiv.addRight a)) := by
    rw [tensorConjugate, ← tensorMatrix_conjTranspose, ← tensorMatrix_mul, ← tensorMatrix_mul,
      permutationUnitary_diagonal]
    rfl
  rw [cyclicTensorMean, haarTwirl_real_smul, haarTwirl_sum]
  simp_rw [he, haarTwirl_tensorConjugate]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ]
  rw [smul_smul, inv_mul_cancel₀ (by exact_mod_cast hs.ne' : (s : ℝ) ≠ 0), one_smul,
    ← haarOrbitAverage_eq_haarTwirl]

theorem haarOrbitAverage_diagonal_lower (s k q : ℕ) (hs : 0 < s) (hk : k ≤ s*q)
    (x : Fin s → ℝ) (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i ≤ 1) :
    (haarOrbitAverage s k (Matrix.diagonal (fun i => (x i : ℂ))) -
      (∏ i : Fin s, x i)^q • (1 : Matrix (Word s k) (Word s k) ℂ)).PosSemidef := by
  letI : NeZero s := ⟨hs.ne'⟩
  have h := haarTwirl_posSemidef s k _ (cyclicTensorMean_lower s k q hs hk x hx0 hx1)
  rwa [haarTwirl_sub, haarTwirl_real_smul,
    haarTwirl_eq_self_of_mem s k 1 (permutationSpan_one s k), haarTwirl_cyclicTensorMean s k hs x] at h

/-- A genuine operator lower bound for every PSD contraction's tensor Haar
twirl. The cyclic AM-GM argument uses neither representation classification
nor an assumed scalar moment or spectral formula for the Haar average. -/
theorem haarOrbitAverage_contraction_lower (s k q : ℕ) (hs : 0 < s) (hk : k ≤ s*q)
    (G : Matrix (Fin s) (Fin s) ℂ) (hG : G.PosSemidef) (hI : (1-G).PosSemidef) :
    (haarOrbitAverage s k G - G.det.re^q • (1 : Matrix (Word s k) (Word s k) ℂ)).PosSemidef := by
  let x := hG.isHermitian.eigenvalues
  have hd : G.det.re = ∏ i : Fin s, x i := by
    rw [hG.isHermitian.det_eq_prod_eigenvalues, ← RCLike.ofReal_prod]
    exact RCLike.ofReal_re (K := ℂ) _
  have h := haarOrbitAverage_diagonal_lower s k q hs hk x hG.eigenvalues_nonneg
    (fun i => contraction_eigenvalues_le_one G hG hI i)
  have he : haarOrbitAverage s k G =
      haarOrbitAverage s k (Matrix.diagonal (fun i => (x i : ℂ))) := by
    rw [haarOrbitAverage_eq_haarTwirl, haarOrbitAverage_eq_haarTwirl]
    have hcast (r : ℝ) : (RCLike.ofReal r : ℂ) = Complex.ofReal r := by rfl
    have hspec : G = (hG.isHermitian.eigenvectorUnitary : Matrix (Fin s) (Fin s) ℂ) *
        Matrix.diagonal (fun i => (x i : ℂ)) *
        (hG.isHermitian.eigenvectorUnitary : Matrix (Fin s) (Fin s) ℂ)ᴴ := by
      simpa only [Unitary.conjStarAlgAut_apply, Unitary.coe_star,
        Matrix.star_eq_conjTranspose, Function.comp_def, hcast, x] using hG.isHermitian.spectral_theorem
    rw [hspec, tensorMatrix_mul, tensorMatrix_mul, tensorMatrix_conjTranspose]
    exact haarTwirl_tensorConjugate s k _ hG.isHermitian.eigenvectorUnitary
  rwa [he, hd]

end
end ExtractionSchur
