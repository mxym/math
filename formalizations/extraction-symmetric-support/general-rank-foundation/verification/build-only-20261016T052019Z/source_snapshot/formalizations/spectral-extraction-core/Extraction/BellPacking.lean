import Extraction.Kraus
import Mathlib.Analysis.Real.Sqrt

open scoped BigOperators ComplexOrder Kronecker
open Matrix
namespace Extraction

variable {d u v : Type*} [Fintype d] [Fintype u] [Fintype v]
  [DecidableEq d] [DecidableEq u] [DecidableEq v]

/-- Erase a local coordinate label while preserving the Bell coordinate. -/
def eraseKraus (j : u) : Matrix d (d × u) ℂ :=
  fun x p => if p.1 = x then if p.2 = j then 1 else 0 else 0

/-- This explicit local operation is trace preserving. -/
theorem eraseKraus_complete :
    (∑ j : u, (eraseKraus (d := d) j)ᴴ * eraseKraus (d := d) j) =
      (1 : Matrix (d × u) (d × u) ℂ) := by
  ext ⟨x,j⟩ ⟨y,k⟩
  by_cases hxy : x = y <;> by_cases hjk : j = k <;>
    simp_all [eraseKraus, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, Matrix.sum_apply, apply_ite, eq_comm]

/-- The local Kraus operator really selects its assigned slice. -/
theorem eraseKraus_mulVec (j : u) (w : d × u → ℂ) (x : d) :
    (eraseKraus (d := d) j *ᵥ w) x = w (x,j) := by
  simp [eraseKraus, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, ite_mul, eq_comm]

/-- The Bell vector's coefficient is kept explicit for algebraic code identities. -/
def bellVector (c : ℂ) : d × d → ℂ := fun p => if p.1 = p.2 then c else 0

/-- Many orthogonal vectors share one Bell coordinate and distinct local labels. -/
def bellCode (c : ℂ) (j : u) (l : v) : (d × u) × (d × v) → ℂ :=
  fun p => if p.1.2 = j then if p.2.2 = l then bellVector c (p.1.1,p.2.1) else 0 else 0

/-- The actual product Kraus family. -/
def productEraseKraus (jl : u × v) :
    Matrix (d × d) ((d × u) × (d × v)) ℂ :=
  eraseKraus (d := d) jl.1 ⊗ₖ eraseKraus (d := d) jl.2

theorem productEraseKraus_complete :
    (∑ jl : u × v, (productEraseKraus (d := d) jl)ᴴ * productEraseKraus (d := d) jl) =
      (1 : Matrix ((d × u) × (d × v)) ((d × u) × (d × v)) ℂ) := by
  have h (j : u) (l : v) :
      (productEraseKraus (d := d) (j,l))ᴴ * productEraseKraus (d := d) (j,l) =
      ((eraseKraus (d := d) j)ᴴ * eraseKraus (d := d) j) ⊗ₖ ((eraseKraus (d := d) l)ᴴ * eraseKraus (d := d) l) := by
    simp only [productEraseKraus, Matrix.conjTranspose_kronecker,
      ← Matrix.mul_kronecker_mul]
  simp only [Fintype.sum_prod_type, h]
  have hs : (∑ j : u, ∑ l : v,
      ((eraseKraus (d := d) j)ᴴ * eraseKraus (d := d) j) ⊗ₖ ((eraseKraus (d := d) l)ᴴ * eraseKraus (d := d) l)) =
      (∑ j : u, (eraseKraus (d := d) j)ᴴ * eraseKraus (d := d) j) ⊗ₖ
      (∑ l : v, (eraseKraus (d := d) l)ᴴ * eraseKraus (d := d) l) := by
    ext p q
    simp [Matrix.sum_apply, Matrix.kroneckerMap_apply, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_comm
  rw [hs, eraseKraus_complete, eraseKraus_complete, Matrix.one_kronecker_one]

theorem productEraseKraus_code (c : ℂ) (j j' : u) (l l' : v) :
    productEraseKraus (d := d) (j',l') *ᵥ bellCode c j l =
      if j' = j ∧ l' = l then bellVector c else 0 := by
  ext ⟨x,y⟩
  by_cases hj : j' = j <;> by_cases hl : l' = l <;>
    simp_all [productEraseKraus, eraseKraus, bellCode, bellVector, Matrix.mulVec,
      dotProduct, Matrix.kroneckerMap_apply, Fintype.sum_prod_type, ite_mul, mul_ite, eq_comm]

/-- Every selected code projector is extracted exactly by one deterministic
local product channel, with no outcome conditioning or renormalization. -/
theorem productEraseKraus_extracts_code (c : ℂ) (j : u) (l : v) :
    krausApply (productEraseKraus (d := d))
      (Matrix.vecMulVec (bellCode c j l) (star (bellCode c j l))) =
      Matrix.vecMulVec (bellVector c) (star (bellVector c)) := by
  classical
  have hpure (b : Prop) [Decidable b] :
      Matrix.vecMulVec (if b then bellVector (d := d) c else 0)
        (star (if b then bellVector (d := d) c else 0)) =
      if b then Matrix.vecMulVec (bellVector (d := d) c) (star (bellVector c)) else 0 := by
    by_cases hb : b <;> simp [hb]
  simp only [krausApply, congruence_pure, Fintype.sum_prod_type,
    productEraseKraus_code]
  simp_rw [hpure]
  simp [ite_and, eq_comm]

end Extraction
