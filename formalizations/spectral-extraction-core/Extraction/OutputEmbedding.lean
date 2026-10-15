import Extraction.FinitePacking

open scoped BigOperators ComplexOrder Kronecker
open Matrix
namespace Extraction

variable {ι ο π κ : Type*} [Fintype ι] [Fintype ο] [Fintype π] [Fintype κ]
  [DecidableEq ι] [DecidableEq ο] [DecidableEq π]

theorem postcomposeKraus_complete (A : κ → Matrix ο ι ℂ)
    (hA : ∑ j, (A j)ᴴ * A j = 1) (E : Matrix π ο ℂ) (hE : Eᴴ * E = 1) :
    (∑ j, (E * A j)ᴴ * (E * A j)) = 1 := by
  simpa only [Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc Eᴴ E, hE, Matrix.one_mul] using hA

theorem postcomposeKraus_apply (A : κ → Matrix ο ι ℂ)
    (E : Matrix π ο ℂ) (X : Matrix ι ι ℂ) :
    krausApply (fun j => E * A j) X = E * krausApply A X * Eᴴ := by
  simp only [krausApply, Matrix.conjTranspose_mul, Matrix.mul_sum,
    Matrix.sum_mul, Matrix.mul_assoc]

variable {d e : Type*} [Fintype d] [Fintype e]
  [DecidableEq d] [DecidableEq e]

/-- Pulling the larger Bell vector back through the same coordinate injection
on both parties gives its unrenormalized restriction. -/
theorem coordinate_bell_pullback (f : d ↪ e) (c : ℂ) :
    (coordinateIsometry f ⊗ₖ coordinateIsometry f)ᴴ *ᵥ bellVector c =
      bellVector (d := d) c := by
  ext ⟨x,y⟩
  by_cases hxy : x = y <;>
    simp_all [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
      Matrix.kroneckerMap_apply, coordinateIsometry, bellVector,
      Fintype.sum_prod_type, apply_ite, ite_mul, mul_ite, f.injective.eq_iff, eq_comm]

/-- The actual trace pairing of two pure projectors is the squared inner product. -/
theorem pure_projector_overlap (v w : ι → ℂ) :
    (Matrix.vecMulVec v (star v) * Matrix.vecMulVec w (star w)).trace =
      (star v ⬝ᵥ w) * star (star v ⬝ᵥ w) := by
  simp only [Matrix.vecMulVec_mul_vecMulVec, Matrix.trace_smul,
    Matrix.trace_vecMulVec]
  rw [star_dotProduct]
  simp only [star_star]
  rw [dotProduct_smul]
  simp only [smul_eq_mul]
  rw [dotProduct_comm v (star w)]

/-- Embedding a normalized Bell_d into the requested output e has exactly
dimension-ratio target fidelity; no scalar approximation is used. -/
theorem embedded_bell_overlap [Nonempty d] [Nonempty e] (f : d ↪ e) :
    (bellProjector (d := e) *
      ((coordinateIsometry f ⊗ₖ coordinateIsometry f) *
        bellProjector (d := d) *
        (coordinateIsometry f ⊗ₖ coordinateIsometry f)ᴴ)).trace.re =
      (Fintype.card d : ℝ) / Fintype.card e := by
  let J := coordinateIsometry f ⊗ₖ coordinateIsometry f
  let v := bellVector (d := e) (bellCoeff e)
  let w := J *ᵥ bellVector (d := d) (bellCoeff d)
  have hi : star v ⬝ᵥ w =
      (Fintype.card d : ℂ) * star (bellCoeff e) * bellCoeff d := by
    have ht : star v ⬝ᵥ w =
        star (Jᴴ *ᵥ v) ⬝ᵥ bellVector (d := d) (bellCoeff d) := by
      simp only [w, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose,
        Matrix.dotProduct_mulVec]
    rw [ht]
    change star ((coordinateIsometry f ⊗ₖ coordinateIsometry f)ᴴ *ᵥ
      bellVector (bellCoeff e)) ⬝ᵥ bellVector (bellCoeff d) = _
    rw [coordinate_bell_pullback]
    simp [dotProduct, bellVector, Fintype.sum_prod_type, apply_ite,
      ite_mul, mul_ite, mul_assoc]
  have hc : (bellProjector (d := e) *
      (J * bellProjector (d := d) * Jᴴ)).trace =
      (Fintype.card d : ℂ) / Fintype.card e := by
    change (Matrix.vecMulVec v (star v) *
      (J * Matrix.vecMulVec (bellVector (bellCoeff d)) (star (bellVector (bellCoeff d))) * Jᴴ)).trace = _
    rw [congruence_pure, pure_projector_overlap]
    change (star v ⬝ᵥ w) * star (star v ⬝ᵥ w) = _
    rw [hi]
    simp only [star_mul, star_natCast, star_star]
    calc
      _ = (Fintype.card d : ℂ)^2 *
          (bellCoeff d * star (bellCoeff d)) *
          (bellCoeff e * star (bellCoeff e)) := by ring
      _ = _ := by
        rw [bellCoeff_mul_star, bellCoeff_mul_star]
        push_cast
        have hd : (Fintype.card d : ℂ) ≠ 0 := by exact_mod_cast (Fintype.card_ne_zero : Fintype.card d ≠ 0)
        field_simp
  have hr : (bellProjector (d := e) *
      (J * bellProjector (d := d) * Jᴴ)).trace =
      (((Fintype.card d : ℝ) / Fintype.card e : ℝ) : ℂ) := by
    simpa using hc
  simpa only [J, Complex.ofReal_re] using congrArg Complex.re hr

end Extraction
