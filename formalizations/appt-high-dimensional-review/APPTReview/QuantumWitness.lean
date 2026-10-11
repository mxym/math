import APPTReview.Hadamard
import APPT.Quantum.RealPSD

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview
variable {a b : Type*} [Fintype a] [LinearOrder a] [Fintype b] [DecidableEq b]

/-- The real Schmidt-witness matrix for an arbitrarily labelled square corner. -/
def witnessMatrix (d : a × a → ℝ) : Matrix a a ℝ := fun i j =>
  if i=j then 2*d (i,i)
  else if i<j then d (i,j)-d (j,i) else d (j,i)-d (i,j)

theorem hadamard_conjugate_entry (d : a × a → ℝ) (i j : a) :
    (2 : ℂ) * (hadamard (a := a) * Matrix.diagonal (fun p => (d p : ℂ)) * (hadamard (a := a))ᴴ)
      (j,i) (i,j) = (witnessMatrix d i j : ℂ) := by
  rw [hadamard_conjTranspose, Matrix.mul_assoc, hadamard_mul_apply]
  by_cases hij : i=j
  · subst j; simp [hadamard, witnessMatrix, Matrix.diagonal_mul]
  · have hji : j≠i := Ne.symm hij
    by_cases hi : i<j
    · have hj : ¬ (j < i) := not_lt_of_gt hi
      simp [hadamard, witnessMatrix, Matrix.diagonal_mul, hij, hji, hi, hj]
      push_cast
      ring_nf
      norm_num
      ring
    · have hj : j < i := lt_of_le_of_ne (le_of_not_gt hi) hji
      simp [hadamard, witnessMatrix, Matrix.diagonal_mul, hij, hji, hi, hj]
      push_cast
      ring_nf
      norm_num
      ring

/-- A genuinely rectangular physical bridge. Every labelled corner gives a PSD
real witness matrix; no Hildebrand equivalence or assumed spectral inequalities are used. -/
theorem diagonal_appt_witness_posSemidef (d : a × b → ℝ)
    (h : APPT.Quantum.AbsolutelyPPT (Matrix.diagonal (fun p => (d p : ℂ))))
    (e : a → b) (he : Function.Injective e) :
    (witnessMatrix (fun p : a × a => d (p.1,e p.2))).PosSemidef := by
  classical
  let emb : a × a → a × b := fun p => (p.1,e p.2)
  have hinj : Function.Injective emb := by
    intro p q hpq
    exact Prod.ext (congrArg (fun z : a × b => z.1) hpq)
      (he (congrArg (fun z : a × b => z.2) hpq))
  let U := APPT.Quantum.extendedUnitary emb hinj (hadamardUnitary (a := a))
  have hp := ((h U).submatrix (fun i : a => (i,e i))).smul (show (0 : ℝ) ≤ 2 by norm_num)
  apply APPT.Quantum.real_posSemidef_of_complex
  convert hp using 1
  ext i j
  change (witnessMatrix (fun p : a × a => d (p.1,e p.2)) i j : ℂ) =
    (2 : ℂ) * ((U : Matrix (a × b) (a × b) ℂ) *
      Matrix.diagonal (fun p => (d p : ℂ)) * (U : Matrix (a × b) (a × b) ℂ)ᴴ)
      (emb (j,i)) (emb (i,j))
  rw [APPT.Quantum.extendedUnitary_conjugate_entry]
  exact (hadamard_conjugate_entry (fun p => d (p.1,e p.2)) i j).symm

/-- All permutations are obtained by actual global unitaries. -/
theorem diagonal_appt_permute (d : a × b → ℝ)
    (h : APPT.Quantum.AbsolutelyPPT (Matrix.diagonal (fun p => (d p : ℂ))))
    (σ : Equiv.Perm (a × b)) :
    APPT.Quantum.AbsolutelyPPT (Matrix.diagonal (fun p => (d (σ p) : ℂ))) := by
  have hp := APPT.Quantum.absolutelyPPT_conjugate h (APPT.Quantum.permUnitary σ)
  simpa only [APPT.Quantum.permUnitary, APPT.Quantum.permMatrix_diagonal,
    Function.comp_def] using hp

/-- The actual eigenvalue diagonal inherits APPT from a Hermitian input matrix. -/
theorem eigenvalue_diagonal_appt {A : Matrix (a × b) (a × b) ℂ}
    (hA : A.IsHermitian) (h : APPT.Quantum.AbsolutelyPPT A) :
    APPT.Quantum.AbsolutelyPPT (Matrix.diagonal (fun p => (hA.eigenvalues p : ℂ))) := by
  have hp := APPT.Quantum.absolutelyPPT_conjugate h (star hA.eigenvectorUnitary)
  have hd := hA.conjStarAlgAut_star_eigenvectorUnitary
  simpa only [Unitary.conjStarAlgAut_apply, Unitary.coe_star,
    Matrix.star_eq_conjTranspose, RCLike.ofReal_eq_complex_ofReal, Function.comp_def] using
    (hd ▸ hp)

/-- The dimension-uniform necessary test for the spectrum of an actual APPT matrix.
Every permutation of its actual eigenvalues and every embedded square corner is covered. -/
theorem appt_eigenvalue_witness_posSemidef {A : Matrix (a × b) (a × b) ℂ}
    (hA : A.IsHermitian) (h : APPT.Quantum.AbsolutelyPPT A)
    (σ : Equiv.Perm (a × b)) (e : a → b) (he : Function.Injective e) :
    (witnessMatrix (fun p : a × a => hA.eigenvalues (σ (p.1,e p.2)))).PosSemidef :=
  diagonal_appt_witness_posSemidef _
    (diagonal_appt_permute _ (eigenvalue_diagonal_appt hA h) σ) e he
end APPTReview
