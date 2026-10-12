import APPT.Quantum.RectangularContraction
import APPT.Quantum.Contractions
open scoped BigOperators ComplexOrder
open Matrix
namespace APPT.Quantum
variable {b : Type*} [Fintype b] [DecidableEq b]

def skewRow (v : Fin 3 × b → ℂ) (x : b) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![v (1,x), v (2,x), 0; -v (0,x), 0, v (2,x); 0, -v (0,x), -v (1,x)]

def complementRow (v : Fin 3 × b → ℂ) (x : b) : Fin 3 → ℂ :=
  ![star (v (2,x)), -star (v (1,x)), star (v (0,x))]

def skewColumns (v : Fin 3 × b → ℂ) : Matrix (Fin 3 × b) (Fin 3) ℂ :=
  fun ix j => skewRow v ix.2 ix.1 j

def complementColumns (v : Fin 3 × b → ℂ) : Matrix b (Fin 3) ℂ :=
  complementRow v

theorem skewRow_gram (v : Fin 3 × b → ℂ) (x : b) (i j : Fin 3) :
    (∑ k : Fin 3, star (skewRow v x k i)*skewRow v x k j) +
      star (complementRow v x i)*complementRow v x j =
    if i=j then ∑ k : Fin 3, star (v (k,x))*v (k,x) else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [skewRow, complementRow, Fin.sum_univ_three] <;> ring

theorem skewColumns_gram (v : Fin 3 × b → ℂ) :
    (skewColumns v)ᴴ * skewColumns v +
      (complementColumns v)ᴴ * complementColumns v =
    Matrix.diagonal (fun _ : Fin 3 => ∑ k : Fin 3 × b, star (v k)*v k) := by
  ext i j
  change (∑ k : Fin 3 × b, star (skewRow v k.2 k.1 i)*skewRow v k.2 k.1 j) +
    (∑ x : b, star (complementRow v x i)*complementRow v x j) =
    if i=j then ∑ k : Fin 3 × b, star (v k)*v k else 0
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  simp_rw [skewRow_gram]
  by_cases hij : i=j
  · subst j
    simp only [ite_true, Fintype.sum_prod_type]
    exact Finset.sum_comm
  · simp [hij]

theorem skewColumns_contraction (v : Fin 3 × b → ℂ)
    (hv : (∑ k, star (v k)*v k) = 1) :
    (1-skewColumns v*(skewColumns v)ᴴ).PosSemidef := by
  apply one_sub_mul_conjTranspose_posSemidef
  have he := skewColumns_gram v
  rw [hv] at he
  have he' : 1 - (skewColumns v)ᴴ*skewColumns v =
      (complementColumns v)ᴴ*complementColumns v := by
    have hd : (Matrix.diagonal (fun _ : Fin 3 => (1 : ℂ))) = 1 := by simp
    rw [hd] at he
    exact sub_eq_iff_eq_add.mpr (by simpa [add_comm] using he.symm)
  rw [he']
  exact Matrix.posSemidef_conjTranspose_mul_self _

end APPT.Quantum
