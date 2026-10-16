import SchurCompletion.HaarTwirl
import RankSupport.FiniteCoefficients

open scoped BigOperators ComplexOrder
open Matrix

namespace ExtractionSchur

open SymmetricSupport ExtractionSpectrum ExtractionRankSupport

noncomputable section

theorem trace_adjoint_pairing_vector {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B A : Matrix ι ι ℂ) :
    (Bᴴ*A).trace = star (matrixVectorEquiv B) ⬝ᵥ matrixVectorEquiv A := by
  change (∑ j, ∑ i, star (B i j) * A i j) =
    ∑ x : ι×ι, star (B x.1 x.2) * A x.1 x.2
  rw [Fintype.sum_prod_type,Finset.sum_comm]

theorem hermitian_dotProduct_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Matrix ι ι ℂ) (hQ : Q.IsHermitian) (x y : ι → ℂ) :
    star x ⬝ᵥ (Q *ᵥ y) = star (Q *ᵥ x) ⬝ᵥ y := by
  rw [Matrix.dotProduct_mulVec]
  congr 1
  ext j
  have he (i j : ι) : star (Q j i) = Q i j := by
    exact congrArg (fun M : Matrix ι ι ℂ => M i j) hQ.eq
  change (∑ i, star (x i) * Q i j) = star (∑ i, Q j i * x i)
  simp only [star_sum,star_mul,he]

/-- A finite matrix projector derived from the actual span of copy
permutation matrices, valid also when its listed generators are dependent. -/
def permutationHSProjector (D k : ℕ) :
    Matrix (Word D k × Word D k) (Word D k × Word D k) ℂ :=
  Classical.choose (MatrixSubspace.exists_subspace_projection
    ((permutationSpan D k).map matrixVectorEquiv.toLinearMap))

theorem permutationHSProjector_properties (D k : ℕ) :
    (permutationHSProjector D k).IsHermitian ∧
    permutationHSProjector D k * permutationHSProjector D k = permutationHSProjector D k ∧
    LinearMap.range (permutationHSProjector D k).mulVecLin =
      (permutationSpan D k).map matrixVectorEquiv.toLinearMap ∧
    (permutationHSProjector D k).rank =
      Module.finrank ℂ ((permutationSpan D k).map matrixVectorEquiv.toLinearMap) ∧
    ∀ v ∈ (permutationSpan D k).map matrixVectorEquiv.toLinearMap,
      permutationHSProjector D k *ᵥ v = v :=
  Classical.choose_spec (MatrixSubspace.exists_subspace_projection
    ((permutationSpan D k).map matrixVectorEquiv.toLinearMap))

def finiteHaarProjection (D k : ℕ) (A : Matrix (Word D k) (Word D k) ℂ) :
    Matrix (Word D k) (Word D k) ℂ :=
  matrixVectorEquiv.symm (permutationHSProjector D k *ᵥ matrixVectorEquiv A)

theorem finiteHaarProjection_mem (D k : ℕ) (A : Matrix (Word D k) (Word D k) ℂ) :
    finiteHaarProjection D k A ∈ permutationSpan D k := by
  have hv : permutationHSProjector D k *ᵥ matrixVectorEquiv A ∈
      (permutationSpan D k).map matrixVectorEquiv.toLinearMap := by
    rw [← (permutationHSProjector_properties D k).2.2.1]
    exact ⟨matrixVectorEquiv A,rfl⟩
  obtain ⟨B,hB,hEq⟩ := hv
  have he : finiteHaarProjection D k A = B := by
    apply matrixVectorEquiv.injective
    change matrixVectorEquiv B = permutationHSProjector D k *ᵥ matrixVectorEquiv A at hEq
    change permutationHSProjector D k *ᵥ matrixVectorEquiv A = matrixVectorEquiv B
    exact hEq.symm
  exact he ▸ hB

theorem finiteHaarProjection_pairing (D k : ℕ) (A B : Matrix (Word D k) (Word D k) ℂ)
    (hB : B ∈ permutationSpan D k) :
    (Bᴴ*finiteHaarProjection D k A).trace = (Bᴴ*A).trace := by
  rw [trace_adjoint_pairing_vector,trace_adjoint_pairing_vector]
  change star (matrixVectorEquiv B) ⬝ᵥ
    (permutationHSProjector D k *ᵥ matrixVectorEquiv A) =
      star (matrixVectorEquiv B) ⬝ᵥ matrixVectorEquiv A
  rw [hermitian_dotProduct_mulVec _ (permutationHSProjector_properties D k).1]
  have hfix : permutationHSProjector D k *ᵥ matrixVectorEquiv B = matrixVectorEquiv B :=
    (permutationHSProjector_properties D k).2.2.2.2 _ ⟨B,hB,rfl⟩
  rw [hfix]

/-- The literal Haar integral is identified with a finite, internally
constructed Hilbert--Schmidt projection. This is not a supplied Haar formula. -/
theorem haarTwirl_eq_finiteHaarProjection (D k : ℕ)
    (A : Matrix (Word D k) (Word D k) ℂ) :
    haarTwirl D k A = finiteHaarProjection D k A := by
  exact (haarTwirl_unique D k A _ (finiteHaarProjection_mem D k A)
    (fun B hB => finiteHaarProjection_pairing D k A B hB)).symm

theorem haarOrbitAverage_eq_finiteHaarProjection (D k : ℕ)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    haarOrbitAverage D k X = finiteHaarProjection D k (tensorMatrix X k) := by
  rw [haarOrbitAverage_eq_haarTwirl,haarTwirl_eq_finiteHaarProjection]

theorem haarOrbitAverage_purity_finite (D k : ℕ) (X : Matrix (Fin D) (Fin D) ℂ)
    (hX : X.IsHermitian) :
    (haarOrbitAverage D k X * haarOrbitAverage D k X).trace =
      star (matrixVectorEquiv (tensorMatrix X k)) ⬝ᵥ
        (permutationHSProjector D k *ᵥ matrixVectorEquiv (tensorMatrix X k)) := by
  have hPair := haarTwirl_pairing D k (tensorMatrix X k) (haarOrbitAverage D k X)
    (haarOrbitAverage_mem_permutationSpan D k X)
  rw [← haarOrbitAverage_eq_haarTwirl] at hPair
  have hT : (tensorMatrix X k)ᴴ = tensorMatrix X k := by
    rw [← tensorMatrix_conjTranspose,hX.eq]
  calc
    _ = (tensorMatrix X k * finiteHaarProjection D k (tensorMatrix X k)).trace := by
      rw [hPair,Matrix.trace_mul_comm,haarOrbitAverage_eq_finiteHaarProjection]
    _ = ((tensorMatrix X k)ᴴ * finiteHaarProjection D k (tensorMatrix X k)).trace := by rw [hT]
    _ = _ := trace_adjoint_pairing_vector _ _

/-- Exact finite rank and exact finite Haar second moment on actual flat
rank-s iid inputs. Sharp asymptotics require further classification/analysis. -/
theorem flatHaarAverage_two_finite_quantities (D s k : ℕ) (hs : 0 < s) (hsD : s ≤ D) :
    (flatHaarAverage D s k hsD).rank = (supportCoefficientMatrix D k s).rank ∧
    (flatHaarAverage D s k hsD * flatHaarAverage D s k hsD).trace =
      star (matrixVectorEquiv (tensorMatrix (flatCoordinateDensity D s hsD) k)) ⬝ᵥ
        (permutationHSProjector D k *ᵥ matrixVectorEquiv
          (tensorMatrix (flatCoordinateDensity D s hsD) k)) := by
  constructor
  · rw [flatHaarAverage_rank D s k hs hsD,rankBudgetProjector_rank_eq_coefficientMatrix_rank]
  · exact haarOrbitAverage_purity_finite D k _
      (flatCoordinateDensity_density D s hs hsD).1.isHermitian

end
end ExtractionSchur
