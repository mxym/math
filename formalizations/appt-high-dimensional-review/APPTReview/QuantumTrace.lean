import APPTReview.SchmidtFrame

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview
variable {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

/-- Partial transpose is self-adjoint for the bilinear trace pairing. -/
theorem trace_partialTranspose_pairing (A B : Matrix (a × b) (a × b) ℂ) :
    (A*APPT.Quantum.partialTranspose B).trace=(APPT.Quantum.partialTranspose A*B).trace := by
  let e : ((a × b) × (a × b)) ≃ ((a × b) × (a × b)) :=
    { toFun := fun p => ((p.2.1,p.1.2),(p.1.1,p.2.2))
      invFun := fun p => ((p.2.1,p.1.2),(p.1.1,p.2.2))
      left_inv := by intro p; rcases p with ⟨⟨i,x⟩,⟨j,y⟩⟩; rfl
      right_inv := by intro p; rcases p with ⟨⟨i,x⟩,⟨j,y⟩⟩; rfl }
  have hs := e.sum_comp (fun p => A p.1 p.2*APPT.Quantum.partialTranspose B p.2 p.1)
  simpa [e,Matrix.trace,Matrix.mul_apply,APPT.Quantum.partialTranspose,Fintype.sum_prod_type] using hs.symm

/-- The outer-product trace pairing is the actual complex quadratic form. -/
theorem trace_mul_pure (A : Matrix (a × b) (a × b) ℂ) (v : a × b → ℂ) :
    (A*Matrix.vecMulVec v (star v)).trace=star v ⬝ᵥ (A*ᵥv) := by
  change (∑ i, ∑ j, A i j*(v j*star (v i)))=∑ i, star (v i)*(∑ j, A i j*v j)
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Pull a trace pairing back through a rectangular congruence. -/
theorem trace_congruence_diagonal {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (A : Matrix ι ι ℂ) (L : Matrix ι κ ℂ) (d : κ → ℂ) :
    (A*(L*Matrix.diagonal d*Lᴴ)).trace=
      ∑ i, (Lᴴ*A*L) i i*d i := by
  have he : (A*(L*Matrix.diagonal d*Lᴴ)).trace=
      ((Lᴴ*A*L)*Matrix.diagonal d).trace := by
    simp only [← Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [he]
  simp [Matrix.trace,Matrix.mul_diagonal]

/-- A compression by a contraction preserves both positivity and the upper bound I. -/
theorem compression_positive_contraction {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (P : Matrix ι ι ℂ) (L : Matrix ι κ ℂ)
    (hP : P.PosSemidef) (hI : (1-P).PosSemidef) (hL : (1-L*Lᴴ).PosSemidef) :
    (Lᴴ*P*L).PosSemidef ∧ (1-Lᴴ*P*L).PosSemidef := by
  have hsmall : (1-Lᴴ*L).PosSemidef := by
    have hh := APPT.Quantum.one_sub_mul_conjTranspose_posSemidef Lᴴ
      (by simpa only [Matrix.conjTranspose_conjTranspose] using hL)
    simpa only [Matrix.conjTranspose_conjTranspose] using hh
  refine ⟨hP.conjTranspose_mul_mul_same L,?_⟩
  have hh := hsmall.add (hI.conjTranspose_mul_mul_same L)
  convert hh using 1
  simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,Matrix.one_mul,Matrix.mul_assoc]
  abel

/-- A nonnegative diagonal lower bound transfers to the original product space. -/
theorem diagonal_floor_lift {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (L : Matrix ι κ ℂ) (d : κ → ℝ) (c δ : ℝ)
    (hc : 0≤c) (hL : (1-L*Lᴴ).PosSemidef)
    (hd : ∀ i, 0≤c+δ*d i) :
    (c • (1 : Matrix ι ι ℂ)+δ • (L*Matrix.diagonal (fun i => (d i:ℂ))*Lᴴ)).PosSemidef := by
  have hdiag : (Matrix.diagonal (fun i => ((c+δ*d i:ℝ):ℂ))).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    change (0:ℂ)≤((c+δ*d i:ℝ):ℂ)
    exact_mod_cast hd i
  have he : Matrix.diagonal (fun i => ((c+δ*d i:ℝ):ℂ))=
      c • (1 : Matrix κ κ ℂ)+δ • Matrix.diagonal (fun i => (d i:ℂ)) := by
    ext i j
    by_cases hij : i=j <;> simp [Matrix.diagonal_apply,Matrix.one_apply,hij,Complex.real_smul]
  rw [he] at hdiag
  have hsum := (hdiag.mul_mul_conjTranspose_same L).add (hL.smul hc)
  convert hsum using 1
  simp only [Matrix.mul_add,Matrix.add_mul,Matrix.smul_mul,Matrix.mul_smul,Matrix.mul_one,smul_sub]
  module

end APPTReview
