import APPT.Quantum.BlockMaps
set_option maxHeartbeats 3000000
open scoped BigOperators ComplexOrder
open Matrix
namespace APPT.Quantum
variable {b : Type*} [Fintype b] [DecidableEq b]

noncomputable def d0 : Matrix (Fin 3) (Fin 3) ℂ := !![1,0,0;0,0,0;0,0,0]
noncomputable def d1 : Matrix (Fin 3) (Fin 3) ℂ := !![0,0,0;0,1,0;0,0,0]
noncomputable def d2 : Matrix (Fin 3) (Fin 3) ℂ := !![0,0,0;0,0,0;0,0,1]
noncomputable def s01 : Matrix (Fin 3) (Fin 3) ℂ := !![0,1,0;1,0,0;0,0,0]
noncomputable def s02 : Matrix (Fin 3) (Fin 3) ℂ := !![0,0,1;0,0,0;1,0,0]
noncomputable def s12 : Matrix (Fin 3) (Fin 3) ℂ := !![0,0,0;0,0,1;0,1,0]
noncomputable def a01 : Matrix (Fin 3) (Fin 3) ℂ := !![0,-1,0;1,0,0;0,0,0]
noncomputable def a02 : Matrix (Fin 3) (Fin 3) ℂ := !![0,0,-1;0,0,0;1,0,0]
noncomputable def a12 : Matrix (Fin 3) (Fin 3) ℂ := !![0,0,0;0,0,-1;0,1,0]

/-- Exact positive-map decomposition for every three-by-qudit block matrix. -/
theorem corrected_partialTranspose_identity
    (P : Matrix (Fin 3 × b) (Fin 3 × b) ℂ) :
    partialTranspose P + 1 =
      sandwich P d0 + sandwich P d1 + sandwich P d2 +
        (1/2 : ℝ) • (sandwich P s01 + sandwich (1-P) a01 +
          sandwich P s02 + sandwich (1-P) a02 +
          sandwich P s12 + sandwich (1-P) a12) := by
  ext ⟨i,x⟩ ⟨j,y⟩
  fin_cases i <;> fin_cases j <;> by_cases hxy : x=y <;>
    simp [Matrix.add_apply, Matrix.smul_apply, sandwich_apply, partialTranspose,
      d0, d1, d2, s01, s02, s12, a01, a02, a12,
      Fin.sum_univ_three, Matrix.sub_apply, Matrix.one_apply,
      hxy, Complex.real_smul, smul_eq_mul] <;> ring

/-- A positive contraction has partial transpose bounded below by minus the identity.
No spectral criterion or unproved quantum interface is assumed. -/
theorem partialTranspose_add_one_posSemidef
    (P : Matrix (Fin 3 × b) (Fin 3 × b) ℂ)
    (hP : P.PosSemidef) (hI : (1-P).PosSemidef) :
    (partialTranspose P + 1).PosSemidef := by
  rw [corrected_partialTranspose_identity]
  have hp := sandwich_posSemidef hP
  have hi := sandwich_posSemidef hI
  have hd := ((hp d0).add (hp d1)).add (hp d2)
  have ho := ((((hp s01).add (hi a01)).add (hp s02)).add (hi a02)).add
    (hp s12) |>.add (hi a12)
  exact hd.add (ho.smul (by norm_num : (0 : ℝ) ≤ 1/2))

/-- The whole global unitary orbit of I+P is PPT whenever 0≤P≤I. -/
theorem absolutelyPPT_one_add_contraction
    (P : Matrix (Fin 3 × b) (Fin 3 × b) ℂ)
    (hP : P.PosSemidef) (hI : (1-P).PosSemidef) :
    AbsolutelyPPT (1+P) := by
  intro U
  let Q := (U : Matrix (Fin 3 × b) (Fin 3 × b) ℂ) * P *
    (U : Matrix (Fin 3 × b) (Fin 3 × b) ℂ)ᴴ
  have hQ : Q.PosSemidef := hP.mul_mul_conjTranspose_same (U : Matrix (Fin 3 × b) (Fin 3 × b) ℂ)
  have hQI : (1-Q).PosSemidef := by
    have h := hI.mul_mul_conjTranspose_same (U : Matrix (Fin 3 × b) (Fin 3 × b) ℂ)
    simpa [Q, Matrix.mul_sub, Matrix.sub_mul, ← Matrix.star_eq_conjTranspose,
      Unitary.coe_mul_star_self] using h
  have h := partialTranspose_add_one_posSemidef Q hQ hQI
  simpa [Q, Matrix.mul_add, Matrix.add_mul, ← Matrix.star_eq_conjTranspose,
    Unitary.coe_mul_star_self, add_comm] using h

end APPT.Quantum
