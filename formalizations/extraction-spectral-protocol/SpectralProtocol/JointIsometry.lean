import SpectralProtocol.SectorKraus

open scoped BigOperators ComplexOrder Kronecker
open Matrix
namespace SpectralProtocol

variable {ι J : Type*} {κ : J → Type*}
  [Fintype ι] [Fintype J] [∀ j,Fintype (κ j)]
  [DecidableEq ι] [DecidableEq J] [∀ j,DecidableEq (κ j)]

/-- The literal matrix concatenation of finitely many logical block embeddings. -/
def concatenateIsometries (C : ∀ j,Matrix ι (κ j) ℂ) : Matrix ι (Σ j,κ j) ℂ :=
  fun x jq => C jq.1 x jq.2

/-- Orthogonal block isometries assemble into one actual matrix isometry. -/
theorem concatenateIsometries_isometry (C : ∀ j,Matrix ι (κ j) ℂ)
    (hC : ∀ j,(C j)ᴴ*C j=1)
    (horth : ∀ j l,j≠l → (C j)ᴴ*C l=0) :
    (concatenateIsometries C)ᴴ*concatenateIsometries C=1 := by
  ext ⟨j,x⟩ ⟨l,y⟩
  by_cases hjl : j=l
  · subst l
    have h := congrArg (fun M : Matrix (κ j) (κ j) ℂ => M x y) (hC j)
    simpa [concatenateIsometries,Matrix.mul_apply,Matrix.conjTranspose_apply,
      Matrix.one_apply] using h
  · have h := congrArg (fun M : Matrix (κ j) (κ l) ℂ => M x y) (horth j l hjl)
    simpa [concatenateIsometries,Matrix.mul_apply,Matrix.conjTranspose_apply,
      Matrix.one_apply,hjl] using h

/-- One actual original-space unitary simultaneously transports every block.
It is constructed by a single finite-dimensional isometry extension, rather
than asserted separately for different blocks or for different inputs. -/
theorem exists_joint_unitary_between_orthogonal_isometries
    (C E : ∀ j,Matrix ι (κ j) ℂ)
    (hC : ∀ j,(C j)ᴴ*C j=1) (hE : ∀ j,(E j)ᴴ*E j=1)
    (hCorth : ∀ j l,j≠l → (C j)ᴴ*C l=0)
    (hEorth : ∀ j l,j≠l → (E j)ᴴ*E l=0) :
    ∃ U : Matrix.unitaryGroup ι ℂ,∀ j,(U : Matrix ι ι ℂ)*C j=E j := by
  obtain ⟨U,hU⟩ := Extraction.exists_unitary_between_isometries
    (concatenateIsometries C) (concatenateIsometries E)
    (concatenateIsometries_isometry C hC hCorth)
    (concatenateIsometries_isometry E hE hEorth)
  refine ⟨U,?_⟩
  intro j
  ext x q
  exact congrArg (fun M : Matrix ι (Σ j,κ j) ℂ => M x ⟨j,q⟩) hU

/-- Actual projection orthogonality implies orthogonality of any internal
orthonormal factorization of those projections. -/
theorem projection_factors_orthogonal
    (P : J → Matrix ι ι ℂ) (C : ∀ j,Matrix ι (κ j) ℂ)
    (hC : ∀ j,(C j)ᴴ*C j=1) (hCP : ∀ j,C j*(C j)ᴴ=P j)
    (hPorth : ∀ j l,j≠l → P j*P l=0) :
    ∀ j l,j≠l → (C j)ᴴ*C l=0 := by
  intro j l hjl
  have hleft : (C j)ᴴ*P j=(C j)ᴴ := by
    rw [← hCP j,← Matrix.mul_assoc,hC j,Matrix.one_mul]
  have hright : P l*C l=C l := by
    rw [← hCP l,Matrix.mul_assoc,hC l,Matrix.mul_one]
  calc
    (C j)ᴴ*C l = ((C j)ᴴ*P j)*(P l*C l) := by rw [hleft,hright]
    _ = (C j)ᴴ*(P j*P l)*C l := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hPorth j l hjl,Matrix.mul_zero,Matrix.zero_mul]

end SpectralProtocol