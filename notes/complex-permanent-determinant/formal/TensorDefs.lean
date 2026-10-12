import RealLawNorm
import Mathlib.Analysis.Complex.Basic

open scoped ComplexConjugate
namespace ComplexPencilTensor
open ComplexPencilReal

noncomputable section

def first : Fin 6 → Fin 3 := ![0,1,2,0,1,2]
def second : Fin 6 → Fin 3 := ![1,2,0,2,0,1]
def third : Fin 6 → Fin 3 := ![2,0,1,1,2,0]
def weight (t : ℝ) : Fin 6 → ℝ :=
  ![(1/6+t),(1/6+t),(1/6+t),(1/6-t),(1/6-t),(1/6-t)]

theorem weight_nonneg (t : ℝ) (ht : |t|≤(1/6:ℝ)) (j : Fin 6) :
  0≤weight t j := by
  have hlow : -t≤(1/6:ℝ) := (neg_le_abs t).trans ht
  have hhigh : t≤(1/6:ℝ) := (le_abs_self t).trans ht
  have hp : 0≤(1/6:ℝ)+t := by linarith
  have hm : 0≤(1/6:ℝ)-t := by linarith
  fin_cases j <;> simp [weight,hp,hm] <;> linarith

def weightedSix (t : ℝ) (z : Fin 6 → ℂ) : ℂ :=
  ∑ j : Fin 6, ((weight t j:ℝ):ℂ)*z j

theorem weightedSix_explicit (t : ℝ) (z : Fin 6 → ℂ) :
 weightedSix t z =
   (((1/6+t:ℝ):ℂ)*(z 0+z 1+z 2) +
    ((1/6-t:ℝ):ℂ)*(z 3+z 4+z 5)) := by
  simp [weightedSix, weight, Fin.sum_univ_succ]
  ring

def slice (f : List (Fin 3) → ℂ) (j : Fin 3) :
    List (Fin 3) → ℂ := fun xs => f (j::xs)

def energy : (ts : List ℝ) → (List (Fin 3) → ℂ) → ℝ
| [], f => Complex.normSq (f [])
| _::ts, f =>
   (energy ts (slice f 0)+energy ts (slice f 1)+
      energy ts (slice f 2))/3

def tensor : (ts : List ℝ) →
  (List (Fin 3) → ℂ) → (List (Fin 3) → ℂ) →
  (List (Fin 3) → ℂ) → ℂ
| [],f,g,h => f []*g []*h []
| t::ts,f,g,h =>
    weightedSix t (fun j =>
      tensor ts (slice f (first j))
        (slice g (second j)) (slice h (third j)))

def kappaSq (t : ℝ) : ℝ :=
   max (1:ℝ) ((3/4)*(1+|6*t|)^2)

def kappa (t : ℝ) : ℝ := Real.sqrt (kappaSq t)

def productK : List ℝ → ℝ
| [] => 1
| t::ts => kappa t*productK ts

theorem energy_nonneg (ts : List ℝ) (f : List (Fin 3) → ℂ) :
    0 ≤ energy ts f := by
  induction ts generalizing f with
  | nil =>
    simp [energy,Complex.normSq_nonneg]
  | cons t ts ih =>
    change 0≤(energy ts (slice f 0)+energy ts (slice f 1)+
      energy ts (slice f 2))/3
    exact div_nonneg
     (by have h0:=ih (slice f 0)
         have h1:=ih (slice f 1)
         have h2:=ih (slice f 2)
         linarith) (by norm_num)

theorem kappa_nonneg (t : ℝ) : 0≤kappa t := Real.sqrt_nonneg _

theorem kappa_sq (t : ℝ) : (kappa t)^2=kappaSq t :=
  Real.sq_sqrt (le_trans (by norm_num : (0:ℝ)≤1) (le_max_left _ _))

theorem productK_nonneg (ts : List ℝ) : 0≤productK ts := by
  induction ts with
  | nil => simp [productK]
  | cons t ts ih =>
      exact mul_nonneg (kappa_nonneg t) ih

theorem weightedSix_norm_le (t : ℝ) (ht : |t|≤(1/6:ℝ))
     (z : Fin 6 → ℂ) :
     ‖weightedSix t z‖ ≤
      ∑ j : Fin 6, weight t j * ‖z j‖ := by
  unfold weightedSix
  calc
    _ ≤ ∑ j : Fin 6, ‖((weight t j : ℝ):ℂ)*z j‖ :=
        norm_sum_le _ _
    _ = ∑ j : Fin 6, weight t j * ‖z j‖ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [norm_mul,Complex.norm_real]
      rw [Real.norm_eq_abs,abs_of_nonneg (weight_nonneg t ht j)]

end
end ComplexPencilTensor
