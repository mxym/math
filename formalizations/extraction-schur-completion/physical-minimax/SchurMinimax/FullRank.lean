import SchurMinimax.Uniform

open scoped BigOperators Topology ComplexOrder
open Matrix MeasureTheory Filter Asymptotics

namespace ExtractionSchur
open SymmetricSupport ExtractionSpectrum ExtractionRankSupport MinimaxProfile
noncomputable section

theorem coordinateRankProjection_full_rank (D : ℕ) :
    coordinateRankProjection D D (le_refl D)=1 := by
  have he : coordinateLetterEmbedding (le_refl D)=Function.Embedding.refl (Fin D) := by ext i; rfl
  have hC : Extraction.coordinateIsometry (coordinateLetterEmbedding (le_refl D)) =
      (1 : Matrix (Fin D) (Fin D) ℂ) := by
    ext i j
    simp [Extraction.coordinateIsometry, he, Matrix.one_apply]
  simp only [coordinateRankProjection, hC, Matrix.conjTranspose_one, Matrix.mul_one]

theorem flatHaarAverage_full_rank (D k : ℕ) :
    flatHaarAverage D D k (le_refl D)=tensorMatrix (flatCoordinateDensity D D (le_refl D)) k := by
  have hX : flatCoordinateDensity D D (le_refl D)=(D : ℝ)⁻¹ • (1 : Matrix (Fin D) (Fin D) ℂ) := by
    rw [flatCoordinateDensity, normalizedProjection, coordinateRankProjection_rank,
      coordinateRankProjection_full_rank]
  have he (U : OneCopyUnitary D) :
      orbitTensor D k (flatCoordinateDensity D D (le_refl D)) U =
      tensorMatrix (flatCoordinateDensity D D (le_refl D)) k := by
    unfold orbitTensor
    rw [hX]
    have hU : (U : Matrix (Fin D) (Fin D) ℂ)*(U : Matrix (Fin D) (Fin D) ℂ)ᴴ=1 := U.prop.2
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
    rw [hU]
  simp only [flatHaarAverage, haarOrbitAverage, he, integral_const, probReal_univ, one_smul]

theorem flatHaarAverage_full_rank_purity (D k : ℕ) :
    (flatHaarAverage D D k (le_refl D)*flatHaarAverage D D k (le_refl D)).trace.re = ((D : ℝ)^k)⁻¹ := by
  rw [flatHaarAverage_full_rank]
  exact flatCoordinateDensity_tensor_purity D D (le_refl D) k

/-- The full-rank class has the exact fidelity 1/K at every blocklength,
for every actual protocol class used in the minimax theorem. -/
theorem rankBudget_full_rank_minimax (C : RankProtocolClass) (m n k K : ℕ)
    (hm : 0 < m) (hn : 0 < n) (hK : 0 < K) :
    rankBudgetPhysicalMinimax C m n k (m*n) K=1/(K : ℝ) := by
  have hD : 0 < m*n := Nat.mul_pos hm hn
  have hbudget : (rankBudgetProjector (m*n) k (m*n)).rank ≤ (m^k/1)*(n^k/1) := by
    simp only [Nat.div_one, rankBudgetProjector_rank_eq_dimension (m*n) k (m*n) le_rfl, mul_pow]
    exact le_rfl
  have h := rankBudget_class_minimax_finite m n k (m*n) 1 K hD le_rfl (by omega) hK hbudget
    C.Allows C.allows_productLocal
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hlo : profile (1 : ℕ) K=1/(K : ℝ) := by
    simpa only [profile, Nat.cast_one] using min_eq_right ((div_le_one hKR).mpr hK1)
  have hsqrt : Real.sqrt (((((m*n : ℕ) : ℝ)^k)⁻¹)*
      ((((m*n : ℕ) : ℝ)^k)/(K : ℝ)^2))=1/(K : ℝ) := by
    have hDP : (0 : ℝ) < ((m*n : ℕ) : ℝ)^k := pow_pos (by exact_mod_cast hD) _
    have he : (((((m*n : ℕ) : ℝ)^k)⁻¹)*
        ((((m*n : ℕ) : ℝ)^k)/(K : ℝ)^2)) = (1/(K : ℝ))^2 := by field_simp
    rw [he, Real.sqrt_sq (by positivity)]
  apply le_antisymm
  · exact h.2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans_eq
      (by rw [flatHaarAverage_full_rank_purity, hsqrt])))
  · exact hlo ▸ h.1

end
end ExtractionSchur
