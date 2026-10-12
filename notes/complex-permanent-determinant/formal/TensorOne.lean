import TensorDefs

open scoped ComplexConjugate
namespace ComplexPencilTensor
open ComplexPencilReal
open ComplexPencilFull
open ComplexPencilMain

noncomputable section

def realWeighted (t : ℝ) (f g h : Fin 3 → ℝ) : ℝ :=
  ∑ j : Fin 6, weight t j * f (first j) * g (second j) *
    h (third j)

theorem realWeighted_explicit (t : ℝ) (f g h : Fin 3 → ℝ) :
    realWeighted t f g h =
      (1/6+t)*(f 0*g 1*h 2+f 1*g 2*h 0+f 2*g 0*h 1) +
      (1/6-t)*(f 0*g 2*h 1+f 1*g 0*h 2+f 2*g 1*h 0) := by
  simp [realWeighted,weight,first,second,third,
    Fin.sum_univ_succ]
  ring

def realRows (f g h : Fin 3 → ℝ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  rowsMatrix (f 0:ℂ) (f 1:ℂ) (f 2:ℂ)
    (g 0:ℂ) (g 1:ℂ) (g 2:ℂ)
    (h 0:ℂ) (h 1:ℂ) (h 2:ℂ)

def realEnergy (f : Fin 3 → ℝ) : ℝ :=
   (f 0^2+f 1^2+f 2^2)/3

theorem realEnergy_nonneg (f : Fin 3 → ℝ) :
    0≤realEnergy f := by
  unfold realEnergy
  positivity

theorem realRows_norm0 (f g h : Fin 3 → ℝ) :
    normalizedRowSq (realRows f g h) 0 = realEnergy f := by
  unfold normalizedRowSq realRows realEnergy
  rw [matRowSq_rows0]
  simp [ComplexPencilMain.rowSq,ComplexPencilLink.sq]
  ring

theorem realRows_norm1 (f g h : Fin 3 → ℝ) :
    normalizedRowSq (realRows f g h) 1 = realEnergy g := by
  unfold normalizedRowSq realRows realEnergy
  rw [matRowSq_rows1]
  simp [ComplexPencilMain.rowSq,ComplexPencilLink.sq]
  ring

theorem realRows_norm2 (f g h : Fin 3 → ℝ) :
    normalizedRowSq (realRows f g h) 2 = realEnergy h := by
  unfold normalizedRowSq realRows realEnergy
  rw [matRowSq_rows2]
  simp [ComplexPencilMain.rowSq,ComplexPencilLink.sq]
  ring

theorem realWeighted_law (t : ℝ) (f g h : Fin 3 → ℝ) :
    law t (realRows f g h) =
       ((realWeighted t f g h : ℝ):ℂ) := by
  unfold law realRows
  rw [permanent_row_expansion,det_row_expansion]
  rw [realWeighted_explicit]
  simp only [ComplexPencilMain.permanent3,
      ComplexPencilMain.determinant3]
  push_cast
  ring

theorem realWeighted_nonneg (t : ℝ) (ht : |t|≤(1/6:ℝ))
    (f g h : Fin 3 → ℝ)
    (hf : ∀ j, 0≤f j) (hg : ∀ j,0≤g j)
    (hh : ∀ j,0≤h j) :
    0≤realWeighted t f g h := by
  unfold realWeighted
  apply Finset.sum_nonneg
  intro j hj
  have hw := weight_nonneg t ht j
  have h0:=hf (first j)
  have h1:=hg (second j)
  have h2:=hh (third j)
  positivity

theorem realWeighted_sq_upper (t : ℝ) (f g h : Fin 3 → ℝ) :
    (realWeighted t f g h)^2 ≤
       kappaSq t * realEnergy f * realEnergy g *
        realEnergy h := by
  have hh := (law_bound_exact t (kappaSq t)).2 (le_refl _)
       (realRows f g h)
  rw [realWeighted_law] at hh
  rw [Complex.normSq_ofReal,
      realRows_norm0,realRows_norm1,realRows_norm2] at hh
  simpa [pow_two] using hh

theorem realWeighted_root_bound
    (t : ℝ) (ht : |t|≤(1/6:ℝ))
    (f g h : Fin 3 → ℝ)
    (hf : ∀ j, 0≤f j) (hg : ∀ j,0≤g j)
    (hh : ∀ j,0≤h j) :
    realWeighted t f g h ≤
     kappa t * Real.sqrt (realEnergy f) *
      Real.sqrt (realEnergy g) *
      Real.sqrt (realEnergy h) := by
  have hw := realWeighted_nonneg t ht f g h hf hg hh
  have hs := realWeighted_sq_upper t f g h
  have hfE:=realEnergy_nonneg f
  have hgE:=realEnergy_nonneg g
  have hhE:=realEnergy_nonneg h
  have hbound : 0≤kappa t*Real.sqrt (realEnergy f)*
        Real.sqrt (realEnergy g)*Real.sqrt (realEnergy h) := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (kappa_nonneg t) (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)
  have hbound_sq :
      (kappa t*Real.sqrt (realEnergy f)*
          Real.sqrt (realEnergy g)*Real.sqrt (realEnergy h))^2 =
          kappaSq t*realEnergy f*realEnergy g*realEnergy h := by
    rw [mul_pow,mul_pow,mul_pow,
        kappa_sq,Real.sq_sqrt hfE,
        Real.sq_sqrt hgE,Real.sq_sqrt hhE] <;> ring
  rw [←hbound_sq] at hs
  nlinarith

end
end ComplexPencilTensor
