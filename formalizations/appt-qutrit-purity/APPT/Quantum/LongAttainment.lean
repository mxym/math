import APPT.Quantum.Contractions
import APPT.Quantum.Orbit
open scoped BigOperators ComplexOrder
open Matrix
namespace APPT.Quantum

/-- Rank-n coordinate projection in the actual qutrit–qudit product basis. -/
def coordinateProjection (n : ℕ) : Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ :=
  Matrix.diagonal (fun i => if i.1=0 then 1 else 0)

theorem coordinateProjection_posSemidef (n : ℕ) :
    (coordinateProjection n).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro i
  dsimp only [Pi.zero_apply]
  split_ifs <;> norm_num

theorem coordinateProjection_complement_posSemidef (n : ℕ) :
    (1-coordinateProjection n).PosSemidef := by
  have he : (1-coordinateProjection n : Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ) =
      Matrix.diagonal (fun i => if i.1=0 then 0 else 1) := by
    ext i j
    by_cases h : i=j <;> by_cases hi : i.1=0 <;>
      simp_all [coordinateProjection, Matrix.diagonal_apply, Matrix.one_apply]
  rw [he]
  apply Matrix.PosSemidef.diagonal
  intro i
  dsimp only [Pi.zero_apply]
  split_ifs <;> norm_num

noncomputable def longState (n : ℕ) : Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ :=
  (1/(4*(n : ℝ))) • (1+coordinateProjection n)

theorem longState_absolutelyPPT (n : ℕ) : AbsolutelyPPT (longState n) := by
  apply absolutelyPPT_smul (absolutelyPPT_one_add_contraction _
    (coordinateProjection_posSemidef n) (coordinateProjection_complement_posSemidef n))
  positivity

theorem coordinateProjection_trace (n : ℕ) :
    (coordinateProjection n).trace = (n : ℂ) := by
  rw [coordinateProjection, Matrix.trace_diagonal, Fintype.sum_prod_type]
  simp [Fin.sum_univ_three]

theorem coordinateProjection_sq (n : ℕ) :
    coordinateProjection n*coordinateProjection n=coordinateProjection n := by
  rw [coordinateProjection, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp

theorem longState_isDensity (n : ℕ) (hn : 0<n) : IsDensity (longState n) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  constructor
  · exact (Matrix.PosSemidef.one.add (coordinateProjection_posSemidef n)).smul
      (by positivity : (0 : ℝ) ≤ 1/(4*(n : ℝ)))
  · simp [longState, Matrix.trace_smul, Matrix.trace_add,
      coordinateProjection_trace, Matrix.trace_one, Complex.real_smul]
    field_simp
    <;> norm_num <;> aesop

theorem longState_purity (n : ℕ) (hn : 0<n) : purity (longState n) = 3/(8*(n : ℝ)) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have he : (1+coordinateProjection n)*(1+coordinateProjection n) =
      1+(3 : ℝ) • coordinateProjection n := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      coordinateProjection_sq]
    module
  unfold purity longState
  rw [Matrix.smul_mul, Matrix.mul_smul, he]
  simp [Matrix.trace_smul, Matrix.trace_add, coordinateProjection_trace,
    Matrix.trace_one, Complex.real_smul]
  field_simp
  <;> ring

end APPT.Quantum
