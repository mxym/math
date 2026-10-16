import SpectralProtocol.MassLower

open scoped BigOperators ComplexOrder Kronecker
open Matrix
namespace SpectralProtocol

variable {J α β κ : Type*} [Fintype J] [Fintype α] [Fintype β] [Fintype κ]
  [DecidableEq J] [DecidableEq α] [DecidableEq β]

/-- A deterministic local channel records its input sector in the Kraus label,
then applies that sector's designated channel. All sectors share the same
physical output; no outcome is postselected. -/
def sectorKraus (A : J → κ → Matrix β α ℂ) (jk : J×κ) : Matrix β (J×α) ℂ :=
  fun o x => if x.1=jk.1 then A jk.1 jk.2 o x.2 else 0

/-- All sector branches together form one trace-preserving local channel. -/
theorem sectorKraus_complete (A : J → κ → Matrix β α ℂ)
    (hA : ∀ j, ∑ t,(A j t)ᴴ*A j t=1) :
    ∑ t,(sectorKraus A t)ᴴ*sectorKraus A t=1 := by
  ext ⟨j,x⟩ ⟨l,y⟩
  by_cases hjl : j=l
  · subst l
    have h := congrArg (fun M : Matrix α α ℂ => M x y) (hA j)
    simpa [sectorKraus,Matrix.sum_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,
      Fintype.sum_prod_type,Matrix.one_apply,apply_ite,ite_mul,mul_ite,eq_comm] using h
  · simp [sectorKraus,Matrix.sum_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,
      Fintype.sum_prod_type,Matrix.one_apply,apply_ite,ite_mul,mul_ite,eq_comm,hjl]

/-- The actual coordinate isometry of one sector. -/
def sectorEmbedding (j : J) : Matrix (J×α) α ℂ :=
  Extraction.coordinateIsometry ⟨fun x => (j,x),by intro x y h; exact congrArg Prod.snd h⟩

theorem sectorEmbedding_isometry (j : J) :
    (sectorEmbedding (α := α) j)ᴴ*sectorEmbedding (α := α) j=1 :=
  Extraction.coordinateIsometry_isometry _

theorem sectorKraus_mul_embedding (A : J → κ → Matrix β α ℂ) (j l : J) (t : κ) :
    sectorKraus A (j,t)*sectorEmbedding l = if j=l then A j t else 0 := by
  ext o x
  change (∑ y, (if y.1=j then A j t o y.2 else 0)*
    (if y=(l,x) then (1:ℂ) else 0)) = _
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  by_cases hjl : j=l <;> simp_all [eq_comm]

/-- Precomposition identity for an actual rectangular Kraus representation. -/
theorem krausApply_encoded {ι η ο ξ : Type*}
    [Fintype ι] [Fintype η] [Fintype ο] [Fintype ξ]
    [DecidableEq ι] [DecidableEq η] [DecidableEq ο]
    (C : ξ → Matrix ο ι ℂ) (E F : Matrix ι η ℂ) (X : Matrix η η ℂ) :
    Extraction.krausApply C (E*X*Fᴴ) = ∑ t,(C t*E)*X*(C t*F)ᴴ := by
  simp only [Extraction.krausApply,Matrix.conjTranspose_mul,Matrix.mul_assoc]

/-- All off-sector coherences are removed by the complete channel, while the
retained diagonal sector sees precisely its designated channel. -/
theorem sectorKraus_encoded (A : J → κ → Matrix β α ℂ) (j l : J)
    (X : Matrix α α ℂ) :
    Extraction.krausApply (sectorKraus A) (sectorEmbedding j*X*(sectorEmbedding l)ᴴ) =
      if j=l then Extraction.krausApply (A j) X else 0 := by
  rw [krausApply_encoded]
  simp only [Fintype.sum_prod_type,sectorKraus_mul_embedding]
  by_cases hjl : j=l
  · subst l
    simp [Extraction.krausApply,apply_ite,ite_mul,mul_ite,eq_comm]
  · simp [hjl,apply_ite,ite_mul,mul_ite,eq_comm]


theorem sectorEmbedding_cross (j l : J) :
    (sectorEmbedding (α := α) j)ᴴ*sectorEmbedding (α := α) l=
      if j=l then 1 else 0 := by
  by_cases hjl : j=l
  · subst l
    simp only [ite_true,sectorEmbedding_isometry]
  · ext x y
    simp [sectorEmbedding,Extraction.coordinateIsometry,Matrix.mul_apply,
      Matrix.conjTranspose_apply,Fintype.sum_prod_type,ite_mul,mul_ite,hjl,eq_comm]
    intro h
    exact hjl (congrArg Prod.fst h)

end SpectralProtocol