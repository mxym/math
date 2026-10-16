import APPT.Quantum.Basic
import Mathlib.Analysis.Matrix.Spectrum

/-!
Actual matrix consequences of the Rains effect constraints.
No Hilbert--Schmidt budget or eigenvalue bounds are caller-supplied assumptions.
The trace-pairing reindexing follows APPTReview.QuantumTrace; all proofs here belong
to this new package and do not enlarge the scope of any earlier audit.
-/

open scoped BigOperators ComplexOrder
open Matrix
namespace Extraction

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Pull an actual trace pairing through a rectangular congruence. -/
theorem trace_congruence_diagonal {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℂ) (L : Matrix ι κ ℂ) (d : κ → ℂ) :
    (A * (L * Matrix.diagonal d * Lᴴ)).trace =
      ∑ i, (Lᴴ * A * L) i i * d i := by
  have he : (A * (L * Matrix.diagonal d * Lᴴ)).trace =
      ((Lᴴ * A * L) * Matrix.diagonal d).trace := by
    simp only [← Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [he]
  simp [Matrix.trace, Matrix.mul_diagonal]

/-- A positive product has nonnegative real trace even without commutation. -/
theorem positive_product_trace_re (P Q : Matrix ι ι ℂ)
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) :
    0 ≤ (P * Q).trace.re := by
  let U := hP.isHermitian.eigenvectorUnitary
  have hdiag (i : ι) :
      0 ≤ (((U : Matrix ι ι ℂ)ᴴ * Q * (U : Matrix ι ι ℂ)) i i).re :=
    (RCLike.nonneg_iff.mp
      ((hQ.conjTranspose_mul_mul_same (U : Matrix ι ι ℂ)).diag_nonneg)).1
  have hp := hP.isHermitian.spectral_theorem
  simp only [Unitary.conjStarAlgAut_apply, Unitary.coe_star, Matrix.star_eq_conjTranspose,
    RCLike.ofReal_eq_complex_ofReal, Function.comp_def] at hp
  rw [Matrix.trace_mul_comm, hp, trace_congruence_diagonal]
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (hdiag i) (hP.eigenvalues_nonneg i)

/-- A genuine two-sided PSD order interval bounds the trace square. -/
theorem trace_square_le_of_order_interval (X : Matrix ι ι ℂ) (c : ℝ)
    (hlo : (c • (1 : Matrix ι ι ℂ) + X).PosSemidef)
    (hhi : (c • (1 : Matrix ι ι ℂ) - X).PosSemidef) :
    (X * X).trace.re ≤ Fintype.card ι * c ^ 2 := by
  have h := positive_product_trace_re
    (c • (1 : Matrix ι ι ℂ) + X) (c • (1 : Matrix ι ι ℂ) - X) hlo hhi
  have he : (c • (1 : Matrix ι ι ℂ) + X) * (c • (1 : Matrix ι ι ℂ) - X) =
      c ^ 2 • (1 : Matrix ι ι ℂ) - X * X := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, smul_add, smul_sub, smul_smul, pow_two]
    abel
  rw [he, Matrix.trace_sub, Complex.sub_re] at h
  have ht : (c ^ 2 • (1 : Matrix ι ι ℂ)).trace.re =
      Fintype.card ι * c ^ 2 := by
    simp [Matrix.trace, Matrix.smul_apply, Complex.real_smul, pow_two, Complex.mul_re, mul_comm]
  rw [ht] at h
  linarith

variable {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

/-- Actual partial transpose is self-adjoint in the bilinear trace pairing. -/
theorem trace_partialTranspose_pairing (A B : Matrix (a × b) (a × b) ℂ) :
    (A * APPT.Quantum.partialTranspose B).trace =
    (APPT.Quantum.partialTranspose A * B).trace := by
  let e : ((a × b) × (a × b)) ≃ ((a × b) × (a × b)) :=
    { toFun := fun p => ((p.2.1, p.1.2), (p.1.1, p.2.2))
      invFun := fun p => ((p.2.1, p.1.2), (p.1.1, p.2.2))
      left_inv := by intro p; rcases p with ⟨⟨i,x⟩,⟨j,y⟩⟩; rfl
      right_inv := by intro p; rcases p with ⟨⟨i,x⟩,⟨j,y⟩⟩; rfl }
  have hs := e.sum_comp
    (fun p => A p.1 p.2 * APPT.Quantum.partialTranspose B p.2 p.1)
  simpa [e, Matrix.trace, Matrix.mul_apply, APPT.Quantum.partialTranspose,
    Fintype.sum_prod_type] using hs.symm

/-- Trace-square is invariant under the physical coordinate partial transpose. -/
theorem partialTranspose_trace_square (M : Matrix (a × b) (a × b) ℂ) :
    (APPT.Quantum.partialTranspose M * APPT.Quantum.partialTranspose M).trace =
    (M * M).trace := by
  simpa using trace_partialTranspose_pairing (APPT.Quantum.partialTranspose M) M

/-- The actual Rains order constraints, with no pre-assumed norm budget. -/
def RainsEffect (K : ℕ) (M : Matrix (a × b) (a × b) ℂ) : Prop :=
  M.PosSemidef ∧ (1 - M).PosSemidef ∧
  ((1 / (K : ℝ)) • (1 : Matrix (a × b) (a × b) ℂ) +
    APPT.Quantum.partialTranspose M).PosSemidef ∧
  ((1 / (K : ℝ)) • (1 : Matrix (a × b) (a × b) ℂ) -
    APPT.Quantum.partialTranspose M).PosSemidef

/-- The squared target dimension is derived from the matrix constraints. -/
theorem rainsEffect_trace_square_le (K : ℕ)
    (M : Matrix (a × b) (a × b) ℂ) (hM : RainsEffect K M) :
    (M * M).trace.re ≤ (Fintype.card a * Fintype.card b : ℝ) / (K : ℝ)^2 := by
  have h := trace_square_le_of_order_interval
    (APPT.Quantum.partialTranspose M) (1 / (K : ℝ)) hM.2.2.1 hM.2.2.2
  rw [partialTranspose_trace_square] at h
  simpa [Fintype.card_prod, div_pow, div_eq_mul_inv, Nat.cast_mul] using h

end Extraction
