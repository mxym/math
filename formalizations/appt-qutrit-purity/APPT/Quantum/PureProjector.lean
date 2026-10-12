import APPT.Quantum.PureGram
import APPT.Quantum.Orbit
open scoped BigOperators ComplexOrder
open Matrix
namespace APPT.Quantum
variable {b : Type*} [Fintype b] [DecidableEq b]

/-- Actual rank-one complex outer product. -/
def rankOne (v : Fin 3 × b → ℂ) : Matrix (Fin 3 × b) (Fin 3 × b) ℂ :=
  Matrix.vecMulVec v (star v)

theorem rankOne_posSemidef (v : Fin 3 × b → ℂ) : (rankOne v).PosSemidef := by
  exact Matrix.posSemidef_vecMulVec_self_star _

/-- An exact sum-of-congruences identity for the pure-state partial transpose. -/
theorem pure_partialTranspose_identity (v : Fin 3 × b → ℂ) :
    (2 : ℝ) • partialTranspose (rankOne v) + skewColumns v*(skewColumns v)ᴴ =
    (2 : ℝ) • (sandwich (rankOne v) d0 + sandwich (rankOne v) d1 +
      sandwich (rankOne v) d2) + sandwich (rankOne v) s01 +
        sandwich (rankOne v) s02 + sandwich (rankOne v) s12 := by
  ext ⟨i,x⟩ ⟨j,y⟩
  change (2 : ℂ)*(v (j,x)*star (v (i,y))) +
    (∑ k : Fin 3, skewRow v x i k * star (skewRow v y j k)) = _
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply, Matrix.smul_apply, sandwich_apply,
      rankOne, Matrix.vecMulVec, skewRow, d0, d1, d2, s01, s02, s12,
      Fin.sum_univ_three, Complex.real_smul] <;> ring

/-- The sharp lower bound minus I/2 for a normalized pure-state partial transpose. -/
theorem one_add_twice_pure_partialTranspose_posSemidef
    (v : Fin 3 × b → ℂ) (hv : (∑ k, star (v k)*v k) = 1) :
    (1+(2 : ℝ) • partialTranspose (rankOne v)).PosSemidef := by
  have hW := skewColumns_contraction v hv
  have hp := sandwich_posSemidef (rankOne_posSemidef v)
  have hd := ((hp d0).add (hp d1)).add (hp d2)
  have h := (((hd.smul (by norm_num : (0 : ℝ) ≤ 2)).add (hp s01)).add
    (hp s02)).add (hp s12)
  rw [← pure_partialTranspose_identity] at h
  have hs := hW.add h
  have he : (1-skewColumns v*(skewColumns v)ᴴ) +
      ((2 : ℝ) • partialTranspose (rankOne v)+skewColumns v*(skewColumns v)ᴴ) =
      1+(2 : ℝ) • partialTranspose (rankOne v) := by abel
  rwa [he] at hs

end APPT.Quantum
