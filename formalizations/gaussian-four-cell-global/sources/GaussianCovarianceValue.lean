import GaussianValueScaling

/-! The covariance reduction is a theorem about actual Gaussian pushforward
measures, including singular covariance matrices and repeated scores. -/
open MeasureTheory ProbabilityTheory Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace GaussianMeasureBridge

variable {d k : ℕ}

noncomputable def scoreMap (v : Fin k → Space d) : Space d →L[ℝ] Space k :=
  (EuclideanSpace.equiv (Fin k) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => innerSL ℝ (v i))

@[simp] lemma scoreMap_apply (v : Fin k → Space d) (x : Space d) (i : Fin k) :
    scoreMap v x i = ⟪v i, x⟫ := rfl

noncomputable def scoreGram (v : Fin k → Space d) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j => ⟪v i, v j⟫

lemma scoreGram_posSemidef (v : Fin k → Space d) : (scoreGram v).PosSemidef := by
  let A : Matrix (Fin k) (Fin d) ℝ := fun i j => v i j
  have heq : scoreGram v = A * Aᴴ := by
    ext i j
    rw [Matrix.mul_apply]
    simp [scoreGram, Matrix.conjTranspose, Matrix.transpose, PiLp.inner_apply, A, mul_comm]
  rw [heq]
  exact Matrix.posSemidef_self_mul_conjTranspose A

lemma scoreMap_adjoint_basis (v : Fin k → Space d) (i : Fin k) :
    (scoreMap v).adjoint ((EuclideanSpace.basisFun (Fin k) ℝ).toBasis i) = v i := by
  apply ext_inner_right ℝ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp [PiLp.inner_apply]

/-- The score vector has precisely its Gram covariance, in every ambient
finite dimension. This proof does not assume the Gram matrix is nonsingular. -/
theorem scoreMap_gaussian_law (v : Fin k → Space d) :
    (gaussian d).map (scoreMap v) = multivariateGaussian 0 (scoreGram v) := by
  apply IsGaussian.ext
  · simp only [id_eq]
    rw [ContinuousLinearMap.integral_id_map]
    · simp [gaussian]
    · exact IsGaussian.integrable_id
  · rw [← ContinuousLinearMap.toBilinForm_inj]
    apply LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
    intro i j
    rw [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.toBilinForm_apply,
      covarianceBilin_map IsGaussian.memLp_two_id, scoreMap_adjoint_basis,
      scoreMap_adjoint_basis]
    rw [show gaussian d = stdGaussian (Space d) from rfl,
      covarianceBilin_stdGaussian, covarianceBilin_multivariateGaussian (scoreGram_posSemidef v)]
    simp [scoreGram]
    rfl

variable [NeZero k]

noncomputable def coordinateMax (b : Fin k → ℝ) (y : Space k) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i => y i - b i

lemma continuous_coordinateMax (b : Fin k → ℝ) : Continuous (coordinateMax b) :=
  Continuous.finset_sup'_apply _ (fun i _ => by fun_prop)

lemma coordinateMax_scoreMap (v : Fin k → Space d) (b : Fin k → ℝ) (x : Space d) :
    coordinateMax b (scoreMap v x) = scoreMax v b x := rfl

noncomputable def covarianceValue (Q : Matrix (Fin k) (Fin k) ℝ) : ℝ :=
  sInf (Set.range fun b : Fin k → ℝ =>
    (∫ y, coordinateMax b y ∂multivariateGaussian 0 Q) + ∑ i, uniformMass k i * b i)

/-- The paper's covariance objective agrees with the original score-price
objective, by equality of genuine Gaussian laws. -/
theorem covarianceValue_scoreGram (v : Fin k → Space d) :
    covarianceValue (scoreGram v) = equalMassValue v := by
  unfold covarianceValue equalMassValue balancedValue priceObjective expectedScore
  congr 2
  funext b
  rw [← scoreMap_gaussian_law v,
    integral_map (scoreMap v).continuous.measurable.aemeasurable
      (continuous_coordinateMax b).aestronglyMeasurable]
  rfl

/-- Invariance under Gram equality also compares score families in different
dimensions and therefore supplies the dimension-transfer step. -/
theorem equalMassValue_eq_of_gram_eq {e : ℕ} (v : Fin k → Space d) (w : Fin k → Space e)
    (h : scoreGram v = scoreGram w) : equalMassValue v = equalMassValue w := by
  rw [← covarianceValue_scoreGram, ← covarianceValue_scoreGram, h]

noncomputable def covarianceRows (Q : Matrix (Fin k) (Fin k) ℝ) : Fin k → Space k :=
  fun i => WithLp.toLp 2 (CFC.sqrt Q i)

lemma scoreGram_covarianceRows (Q : Matrix (Fin k) (Fin k) ℝ) (hQ : Q.PosSemidef) :
    scoreGram (covarianceRows Q) = Q := by
  have hB := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg Q)).isHermitian
  have hBB := CFC.sqrt_mul_sqrt_self Q hQ.nonneg
  ext i j
  change ⟪WithLp.toLp 2 (CFC.sqrt Q i), WithLp.toLp 2 (CFC.sqrt Q j)⟫ = Q i j
  conv_rhs => rw [← hBB]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro l _
  have h : CFC.sqrt Q l j = CFC.sqrt Q j l := by simpa using hB.apply j l
  rw [h, mul_comm]

theorem covarianceValue_eq_rows (Q : Matrix (Fin k) (Fin k) ℝ) (hQ : Q.PosSemidef) :
    covarianceValue Q = equalMassValue (covarianceRows Q) := by
  rw [← covarianceValue_scoreGram, scoreGram_covarianceRows Q hQ]

lemma scoreGram_smul (v : Fin k → Space d) (a : ℝ) :
    scoreGram (a • v) = (a ^ 2) • scoreGram v := by
  ext i j
  simp [scoreGram, real_inner_smul_left, real_inner_smul_right, pow_two, mul_assoc]

/-- Square-root homogeneity on the entire positive-semidefinite cone. -/
theorem covarianceValue_smul (Q : Matrix (Fin k) (Fin k) ℝ) (hQ : Q.PosSemidef)
    (a : ℝ) (ha : 0 ≤ a) : covarianceValue (a • Q) = Real.sqrt a * covarianceValue Q := by
  have hgram : scoreGram (Real.sqrt a • covarianceRows Q) = a • Q := by
    rw [scoreGram_smul, Real.sq_sqrt ha, scoreGram_covarianceRows Q hQ]
  rw [← hgram, covarianceValue_scoreGram, equalMassValue_smul _ _ (Real.sqrt_nonneg a),
    ← covarianceValue_eq_rows Q hQ]

end GaussianMeasureBridge
