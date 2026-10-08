import PermutationTVIndependent
import MatrixTheorem
import RealLawNorm

namespace ComplexPencilProbability
open ComplexPencilTensor
open ComplexPencilFull
open ComplexPencilReal
open ComplexPencilMain
noncomputable section

def oneColumnMoment (p : Fin 6 → ℝ)
    (f g h : Fin 3 → ℂ) : ℂ :=
  ∑ j : Fin 6, (p j : ℂ) * f (first j) *
     g (second j) * h (third j)

def normalizedEnergy (f : Fin 3 → ℂ) : ℝ :=
  (Complex.normSq (f 0) + Complex.normSq (f 1) +
   Complex.normSq (f 2)) / 3

def oneColumnContractive (p : Fin 6 → ℝ) : Prop :=
  ∀ f g h : Fin 3 → ℂ,
    Complex.normSq (oneColumnMoment p f g h) ≤
      normalizedEnergy f * normalizedEnergy g *
        normalizedEnergy h

theorem moment_weight_eq_law (t : ℝ)
    (f g h : Fin 3 → ℂ) :
    oneColumnMoment (weight t) f g h =
      law t (rowsMatrix (f 0) (f 1) (f 2)
        (g 0) (g 1) (g 2) (h 0) (h 1) (h 2)) := by
  unfold oneColumnMoment law
  rw [permanent_row_expansion, det_row_expansion]
  simp [weight, first, second, third,
    Fin.sum_univ_succ, permanent3, determinant3]
  push_cast
  ring

theorem energy_f_eq_row0 (f g h : Fin 3 → ℂ) :
    normalizedEnergy f =
       normalizedRowSq
         (rowsMatrix (f 0) (f 1) (f 2)
           (g 0) (g 1) (g 2) (h 0) (h 1) (h 2)) 0 := by
  simp [normalizedEnergy,normalizedRowSq,matRowSq_rows0,
    rowSq,normSq_eq_sq]

theorem energy_g_eq_row1 (f g h : Fin 3 → ℂ) :
    normalizedEnergy g =
       normalizedRowSq
         (rowsMatrix (f 0) (f 1) (f 2)
           (g 0) (g 1) (g 2) (h 0) (h 1) (h 2)) 1 := by
  simp [normalizedEnergy,normalizedRowSq,matRowSq_rows1,
    rowSq,normSq_eq_sq]

theorem energy_h_eq_row2 (f g h : Fin 3 → ℂ) :
    normalizedEnergy h =
       normalizedRowSq
         (rowsMatrix (f 0) (f 1) (f 2)
           (g 0) (g 1) (g 2) (h 0) (h 1) (h 2)) 2 := by
  simp [normalizedEnergy,normalizedRowSq,matRowSq_rows2,
    rowSq,normSq_eq_sq]

theorem columnContractive_weight_iff (t : ℝ) :
    oneColumnContractive (weight t) ↔ LawBound t 1 := by
  constructor
  · intro h A
    let f : Fin 3 → ℂ := fun j => A 0 j
    let g : Fin 3 → ℂ := fun j => A 1 j
    let z : Fin 3 → ℂ := fun j => A 2 j
    have hh := h f g z
    rw [moment_weight_eq_law t f g z,
        energy_f_eq_row0 f g z,
        energy_g_eq_row1 f g z,
        energy_h_eq_row2 f g z] at hh
    dsimp only [f, g, z] at hh
    rw [rowsMatrix_surjective A] at hh
    simpa only [one_mul] using hh
  · intro h f g z
    have hh := h (rowsMatrix (f 0) (f 1) (f 2)
        (g 0) (g 1) (g 2) (z 0) (z 1) (z 2))
    rw [←moment_weight_eq_law t f g z,
        ←energy_f_eq_row0 f g z,
        ←energy_g_eq_row1 f g z,
        ←energy_h_eq_row2 f g z] at hh
    simpa only [one_mul] using hh

theorem uniformLaw_L2_contractive_iff_TV
    (p : Fin 6 → ℝ)
    (hm : uniformMarginals p) :
    oneColumnContractive p ↔ parityTV p ≤ tvThreshold := by
  obtain ⟨t, ht⟩ := (uniformMarginals_iff_parity p).mp hm
  subst p
  rw [columnContractive_weight_iff,sharp_tv_parameter_iff]

#print axioms ComplexPencilProbability.uniformLaw_L2_contractive_iff_TV

end
end ComplexPencilProbability
