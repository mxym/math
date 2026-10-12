import APPT.Quantum.Permutation
set_option maxHeartbeats 5000000
open scoped BigOperators ComplexOrder
open Matrix
namespace APPT.Quantum

noncomputable def halfRoot : ℂ := (Real.sqrt ((1 : ℝ)/2) : ℂ)
@[simp] theorem halfRoot_star : star halfRoot = halfRoot := by simp [halfRoot]
@[simp] theorem halfRoot_sq : halfRoot^2 = (1/2 : ℂ) := by
  norm_cast
  norm_num [halfRoot, ← Complex.ofReal_pow, Real.sq_sqrt]

@[simp] theorem halfRoot_conj : (starRingEnd ℂ) halfRoot = halfRoot := halfRoot_star

/-- Three disjoint symmetric/antisymmetric two-plane rotations. -/
noncomputable def cornerHadamard : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  fun i j => if i.1=i.2 then (if i=j then 1 else 0)
    else if i=j then (if i.1 < i.2 then halfRoot else -halfRoot)
    else if (i.2,i.1)=j then halfRoot else 0

theorem cornerHadamard_conjTranspose : cornerHadamardᴴ = cornerHadamard := by
  ext ⟨a,b⟩ ⟨c,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [cornerHadamard, Matrix.conjTranspose_apply]

theorem cornerHadamard_sq : cornerHadamard*cornerHadamard=1 := by
  ext ⟨a,b⟩ ⟨c,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_three,
      cornerHadamard, Matrix.one_apply] <;> ring_nf <;> norm_num

noncomputable def cornerUnitary : Matrix.unitaryGroup (Fin 3 × Fin 3) ℂ :=
  ⟨cornerHadamard, by
    constructor <;> simpa only [Matrix.star_eq_conjTranspose,
      cornerHadamard_conjTranspose] using cornerHadamard_sq⟩

/-- Which of the nine distinguished eigenvalues occupies each corner basis position. -/
def slotA (i : Fin 3 × Fin 3) : Fin 9 :=
  (!![8,7,5;0,6,4;1,2,3] : Matrix (Fin 3) (Fin 3) (Fin 9)) i.1 i.2

def slotB (i : Fin 3 × Fin 3) : Fin 9 :=
  (!![8,7,6;0,5,4;1,2,3] : Matrix (Fin 3) (Fin 3) (Fin 9)) i.1 i.2

theorem slotA_bijective : Function.Bijective slotA := by decide +kernel

theorem slotB_bijective : Function.Bijective slotB := by decide +kernel

noncomputable def cornerDiagonal (slot : Fin 3 × Fin 3 → Fin 9) (y : Fin 9 → ℝ) :
    Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ := Matrix.diagonal (fun i => (y (slot i) : ℂ))

theorem corner_A_entry (y : Fin 9 → ℝ) (i j : Fin 3) :
    (2 : ℂ) * (cornerHadamard*cornerDiagonal slotA y*cornerHadamardᴴ) (j,i) (i,j) =
    (matA y i j : ℂ) := by
  fin_cases i <;> fin_cases j <;>
    simp [cornerDiagonal, slotA, cornerHadamard, matA, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.diagonal_apply,
      Fintype.sum_prod_type, Fin.sum_univ_three]
  all_goals push_cast; try simp only [halfRoot_conj]
  all_goals ring_nf; norm_num <;> ring

theorem corner_B_entry (y : Fin 9 → ℝ) (i j : Fin 3) :
    (2 : ℂ) * (cornerHadamard*cornerDiagonal slotB y*cornerHadamardᴴ) (j,i) (i,j) =
    (matB y i j : ℂ) := by
  fin_cases i <;> fin_cases j <;>
    simp [cornerDiagonal, slotB, cornerHadamard, matB, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.diagonal_apply,
      Fintype.sum_prod_type, Fin.sum_univ_three]
  all_goals push_cast; try simp only [halfRoot_conj]
  all_goals ring_nf; norm_num <;> ring

end APPT.Quantum
