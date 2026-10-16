import SpectralProtocol.SectorKraus

open scoped BigOperators ComplexOrder Kronecker
open Matrix
namespace SpectralProtocol

variable {J α β d κ η : Type*}
  [Fintype J] [Fintype α] [Fintype β] [Fintype d] [Fintype κ] [Fintype η]
  [DecidableEq J] [DecidableEq α] [DecidableEq β] [DecidableEq d]

def productSectorEmbedding (j : J) : Matrix ((J×α)×(J×β)) (α×β) ℂ :=
  sectorEmbedding j ⊗ₖ sectorEmbedding j

theorem productSectorEmbedding_isometry (j : J) :
    (productSectorEmbedding (α := α) (β := β) j)ᴴ*productSectorEmbedding (α := α) (β := β) j=1 :=
  Extraction.kronecker_isometry _ _ (sectorEmbedding_isometry j) (sectorEmbedding_isometry j)

theorem productSectorKraus_mul_embedding
    (A : J → κ → Matrix d α ℂ) (B : J → η → Matrix d β ℂ)
    (j : J) (t : (J×κ)×(J×η)) :
    Extraction.productKraus (sectorKraus A) (sectorKraus B) t * productSectorEmbedding j =
      if t.1.1=j ∧ t.2.1=j then Extraction.productKraus (A j) (B j) (t.1.2,t.2.2) else 0 := by
  unfold Extraction.productKraus productSectorEmbedding
  rw [← Matrix.mul_kronecker_mul,sectorKraus_mul_embedding,sectorKraus_mul_embedding]
  by_cases ha : t.1.1=j <;> by_cases hb : t.2.1=j <;>
    simp_all [Matrix.zero_kronecker,Matrix.kronecker_zero]

/-- One fixed pair of complete local sector channels reads every matched sector,
removing arbitrary cross-sector coherences exactly. The input block matrix is
arbitrary and may be a coherent logical state. -/
theorem productSectorKraus_encoded
    (A : J → κ → Matrix d α ℂ) (B : J → η → Matrix d β ℂ)
    (j l : J) (X : Matrix (α×β) (α×β) ℂ) :
    Extraction.krausApply (Extraction.productKraus (sectorKraus A) (sectorKraus B))
      (productSectorEmbedding j*X*(productSectorEmbedding l)ᴴ) =
    if j=l then Extraction.krausApply (Extraction.productKraus (A j) (B j)) X else 0 := by
  rw [krausApply_encoded]
  simp only [productSectorKraus_mul_embedding]
  by_cases hjl : j=l
  · subst l
    simp only [ite_true,Fintype.sum_prod_type]
    simp [Extraction.krausApply,ite_and,apply_ite,ite_mul,mul_ite,eq_comm,Extraction.productKraus,Fintype.sum_prod_type]
  · simp only [hjl,ite_false]
    apply Finset.sum_eq_zero
    intro t _
    by_cases hj : t.1.1=j ∧ t.2.1=j
    · have hl : ¬ (t.1.1=l ∧ t.2.1=l) := by intro hl;exact hjl (hj.1.symm.trans hl.1)
      simp [hj,hl,hjl]
    · simp [hj]


theorem productSectorEmbedding_cross (j l : J) :
    (productSectorEmbedding (α := α) (β := β) j)ᴴ*
      productSectorEmbedding (α := α) (β := β) l=if j=l then 1 else 0 := by
  unfold productSectorEmbedding
  rw [Matrix.conjTranspose_kronecker,← Matrix.mul_kronecker_mul,
    sectorEmbedding_cross,sectorEmbedding_cross]
  by_cases hjl : j=l <;> simp [hjl,Matrix.one_kronecker_one]

end SpectralProtocol