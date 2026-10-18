import CircuitRecursion.Robustness

open scoped BigOperators
open Matrix CircuitCompletion SymmetricSupport
namespace CircuitRecursion

/-- Actual pure iid density in the original bit basis equals the reindexed
literal kth tensor matrix of the one-copy pure density. -/
theorem bitPurePower_density (k : ℕ) (z : Fin 4 → ℂ) :
    pureMatrix (bitPurePower k z)=Matrix.reindexAlgEquiv ℂ ℂ (originalBitCoordinates k)
      (ExtractionSpectrum.tensorMatrix (pureMatrix z) k) := by
  ext b c
  simp only [pureMatrix,bitPurePower,Matrix.coe_reindexAlgEquiv,Matrix.reindex_apply,
    Matrix.submatrix_apply,ExtractionSpectrum.tensorMatrix,Matrix.vecMulVec_apply,
    Pi.star_apply,purePower,star_prod,Finset.prod_mul_distrib]

theorem bitPurePower_copywiseInput (k : ℕ) (z : Fin 4 → ℂ) :
    Matrix.reindexAlgEquiv ℂ ℂ (bitBipartiteCoordinates k)
      (pureMatrix (bitPurePower k z))=copywiseInput 2 2 k (pureMatrix z) := by
  rw [bitPurePower_density]
  ext p q
  simp [Matrix.coe_reindexAlgEquiv,Matrix.reindex_apply,Matrix.submatrix_apply,
    bitBipartiteCoordinates,copywiseInput]

def physicalLocalReadoutCoordinates (k : ℕ) : Fin (2^k) ≃
    Bits (bellPairYield k)×Bits (encodingPairs k) :=
  (localDigits k).trans (localReadoutCoordinates k)

theorem readoutCoordinates_physical (k : ℕ) :
    readoutCoordinates k=(bitBipartiteCoordinates k).trans
      (Equiv.prodCongr (physicalLocalReadoutCoordinates k) (physicalLocalReadoutCoordinates k)) := by
  rw [readoutCoordinates,pairwiseCoordinates_physical]
  rfl

end CircuitRecursion
