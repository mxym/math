import Mathlib.LinearAlgebra.UnitaryGroup
import Extraction.ProductCompletion
import Extraction.SubspacePacking

open scoped BigOperators Kronecker
open Matrix
namespace CircuitCompletion

abbrev Bits (n : ℕ) := Fin n → Bool

def wireCoordinates {n : ℕ} (i : Fin n) :
    Bits n ≃ Bool×({j : Fin n // j≠i} → Bool) where
  toFun w := (w i,fun j => w j.1)
  invFun p j := if h : j=i then p.1 else p.2 ⟨j,h⟩
  left_inv w := by funext j;by_cases h : j=i <;> simp [h]
  right_inv p := by
    apply Prod.ext
    · simp
    · funext j;simp [j.property]

noncomputable def reindexUnitary {ι ο : Type*} [Fintype ι] [Fintype ο]
    [DecidableEq ι] [DecidableEq ο] (e : ι ≃ ο) (U : Matrix.unitaryGroup ι ℂ) :
    Matrix.unitaryGroup ο ℂ := by
  let T := Matrix.reindexAlgEquiv ℂ ℂ e
  refine ⟨T U,Matrix.mem_unitaryGroup_iff'.mpr ?_⟩
  have hs : (T U)ᴴ=T (U : Matrix ι ι ℂ)ᴴ := by ext i j;rfl
  change (T U)ᴴ*T U=1
  rw [hs,← map_mul]
  have hU : (U : Matrix ι ι ℂ)ᴴ*U=1 := by
    simpa only [Unitary.coe_star,Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U
  rw [hU,map_one]

noncomputable def permutationUnitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Equiv.Perm ι) : Matrix.unitaryGroup ι ℂ :=
  ⟨Extraction.coordinateIsometry e.toEmbedding,Matrix.mem_unitaryGroup_iff'.mpr
    (Extraction.coordinateIsometry_isometry e.toEmbedding)⟩

theorem permutationUnitary_action {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Equiv.Perm ι) (v : ι → ℂ) :
    (permutationUnitary e : Matrix ι ι ℂ)*ᵥv=fun i => v (e.symm i) := by
  ext i
  simp [permutationUnitary,Extraction.coordinateIsometry,Matrix.mulVec,dotProduct,
    ← e.symm_apply_eq]

/-- A single-qubit gate acts on one existing wire; every other original wire
is a spectator. No preparation or additional wire is part of this syntax. -/
noncomputable def singleWire {n : ℕ} (i : Fin n) (U : Matrix.unitaryGroup Bool ℂ) :
    Matrix.unitaryGroup (Bits n) ℂ :=
  reindexUnitary (wireCoordinates i).symm
    ⟨(U : Matrix Bool Bool ℂ) ⊗ₖ (1 : Matrix ({j : Fin n // j≠i} → Bool)
      ({j : Fin n // j≠i} → Bool) ℂ),Matrix.kronecker_mem_unitary U.property (1 : unitary _).property⟩

def cnotFunction {n : ℕ} (c t : Fin n) (w : Bits n) : Bits n :=
  Function.update w t (Bool.xor (w t) (w c))

theorem cnotFunction_involutive {n : ℕ} (c t : Fin n) (hct : c≠t) :
    Function.Involutive (cnotFunction c t) := by
  intro w
  funext j
  by_cases hj : j=t
  · subst j
    simp [cnotFunction,Function.update_of_ne hct]
  · simp [cnotFunction,hj]

def cnotEquiv {n : ℕ} (c t : Fin n) (hct : c≠t) : Equiv.Perm (Bits n) :=
  (cnotFunction_involutive c t hct).toPerm (cnotFunction c t)

/-- The primitive gate alphabet is literally CNOT and arbitrary one-qubit
unitaries on the original register. A global unitary is not a primitive. -/
inductive Gate (n : ℕ) where
  | single (i : Fin n) (U : Matrix.unitaryGroup Bool ℂ)
  | cnot (c t : Fin n) (hct : c≠t)

noncomputable def Gate.denote {n : ℕ} : Gate n → Matrix.unitaryGroup (Bits n) ℂ
  | .single i U => singleWire i U
  | .cnot c t h => permutationUnitary (cnotEquiv c t h)

abbrev Circuit (n : ℕ) := List (Gate n)

/-- Leftmost list element is executed first. Every list has actual unitary
matrix semantics, while its elementary gate count is its actual list length. -/
noncomputable def denote {n : ℕ} : Circuit n → Matrix.unitaryGroup (Bits n) ℂ
  | [] => 1
  | g::gs => denote gs*g.denote

theorem denote_nil (n : ℕ) : denote ([] : Circuit n)=1 := rfl

theorem denote_cons {n : ℕ} (g : Gate n) (gs : Circuit n) :
    denote (g::gs)=denote gs*g.denote := rfl

theorem denote_append {n : ℕ} (a b : Circuit n) : denote (a++b)=denote b*denote a := by
  induction a with
  | nil => simp [denote]
  | cons g gs ih => simp only [List.cons_append,denote,ih,mul_assoc]

noncomputable def run {n : ℕ} (a : Circuit n) (v : Bits n → ℂ) : Bits n → ℂ :=
  (denote a : Matrix (Bits n) (Bits n) ℂ)*ᵥv

theorem run_append {n : ℕ} (a b : Circuit n) (v : Bits n → ℂ) :
    run (a++b) v=run b (run a v) := by
  simp only [run,denote_append,Matrix.UnitaryGroup.mul_val,← Matrix.mulVec_mulVec]

theorem cnot_action {n : ℕ} (c t : Fin n) (hct : c≠t) (v : Bits n → ℂ) :
    ((Gate.cnot c t hct).denote : Matrix (Bits n) (Bits n) ℂ)*ᵥv=
      fun w => v (cnotFunction c t w) := by
  change (permutationUnitary (cnotEquiv c t hct) : Matrix (Bits n) (Bits n) ℂ)*ᵥv=_
  rw [permutationUnitary_action]
  rfl

end CircuitCompletion
