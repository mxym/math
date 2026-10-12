import APPTReview.SchmidtNormalize
import APPT.Quantum.RectangularContraction

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview
variable {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

/-- Conjugated left Schmidt vectors tensor normalized right rows; no full-rank premise. -/
def schmidtFrame (U : Matrix.unitaryGroup a ℂ) (Z : Matrix a b ℂ) :
    Matrix (a × b) (a × a) ℂ := ((U:Matrix a a ℂ)ᴴ)ᵀ.kronecker Zᵀ

theorem schmidtFrame_apply (U : Matrix.unitaryGroup a ℂ) (Z : Matrix a b ℂ)
    (i : a) (x : b) (j k : a) :
    schmidtFrame U Z (i,x) (j,k)=star ((U:Matrix a a ℂ) i j)*Z k x := rfl

theorem schmidtFrame_gram (U : Matrix.unitaryGroup a ℂ) (s : a → ℝ) (Z : Matrix a b ℂ)
    (hZ : Z*Zᴴ=Matrix.diagonal (fun i => if s i=0 then (0:ℂ) else 1)) :
    (schmidtFrame U Z)ᴴ*schmidtFrame U Z=
      Matrix.diagonal (fun p : a × a => if s p.2=0 then (0:ℂ) else 1) := by
  have hu : (U:Matrix a a ℂ)ᴴ*(U:Matrix a a ℂ)=1 := by
    simpa only [Unitary.coe_star,Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U
  have huT : (((U:Matrix a a ℂ)ᴴ)ᵀ)ᴴ*((U:Matrix a a ℂ)ᴴ)ᵀ=1 := by
    rw [Matrix.conjTranspose_transpose_eq_transpose_conjTranspose,
      Matrix.conjTranspose_conjTranspose,← Matrix.transpose_mul,hu]
    simp
  have hzT : (Zᵀ)ᴴ*Zᵀ=(Z*Zᴴ)ᵀ := by
    rw [Matrix.conjTranspose_transpose_eq_transpose_conjTranspose,Matrix.transpose_mul]
  simp only [schmidtFrame,Matrix.kronecker,Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul,huT,hzT,hZ]
  ext ⟨i,x⟩ ⟨j,y⟩
  by_cases hij : i=j <;> by_cases hxy : x=y <;>
    simp_all [Matrix.kronecker_apply,Matrix.diagonal_apply,Matrix.one_apply]

theorem schmidtFrame_contraction (U : Matrix.unitaryGroup a ℂ) (s : a → ℝ) (Z : Matrix a b ℂ)
    (hZ : Z*Zᴴ=Matrix.diagonal (fun i => if s i=0 then (0:ℂ) else 1)) :
    (1-schmidtFrame U Z*(schmidtFrame U Z)ᴴ).PosSemidef := by
  apply APPT.Quantum.one_sub_mul_conjTranspose_posSemidef
  rw [schmidtFrame_gram U s Z hZ]
  have he : (1 : Matrix (a × a) (a × a) ℂ)-
      Matrix.diagonal (fun p : a × a => if s p.2=0 then (0:ℂ) else 1)=
      Matrix.diagonal (fun p : a × a => if s p.2=0 then (1:ℂ) else 0) := by
    ext p q
    by_cases hpq : p=q <;> by_cases hs : s p.2=0 <;>
      simp_all [Matrix.diagonal_apply,Matrix.one_apply]
  rw [he]
  apply Matrix.PosSemidef.diagonal
  intro p
  change (0:ℂ) ≤ if s p.2=0 then 1 else 0
  split_ifs <;> norm_num

end APPTReview
