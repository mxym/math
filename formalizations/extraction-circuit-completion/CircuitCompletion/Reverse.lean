import CircuitCompletion.ParityPhase

open scoped BigOperators Kronecker
open Matrix
namespace CircuitCompletion

noncomputable def Gate.inverse {n : ℕ} : Gate n → Gate n
  | .single i U => .single i (star U)
  | .cnot c t h => .cnot c t h

theorem singleWire_star {n : ℕ} (i : Fin n) (U : Matrix.unitaryGroup Bool ℂ) :
    singleWire i (star U)=star (singleWire i U) := by
  apply Subtype.ext
  ext w v
  change (star (U : Matrix Bool Bool ℂ) ⊗ₖ (1 : Matrix ({j : Fin n // j≠i}→Bool)
    ({j : Fin n // j≠i}→Bool) ℂ)) ((wireCoordinates i) w) ((wireCoordinates i) v)=_
  by_cases h : ((wireCoordinates i) w).2=((wireCoordinates i) v).2
  all_goals simp [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,Matrix.kronecker_apply,
    singleWire,reindexUnitary,Matrix.reindexAlgEquiv_apply,Matrix.reindex_apply,
    Matrix.one_apply,h,Ne.symm,eq_comm]

theorem cnot_denote_star {n : ℕ} (c t : Fin n) (hct : c≠t) :
    star ((Gate.cnot c t hct).denote)=(Gate.cnot c t hct).denote := by
  apply Subtype.ext
  ext w v
  change star (if v=cnotFunction c t w then (1 : ℂ) else 0)=
    (if w=cnotFunction c t v then 1 else 0)
  have heq : v=cnotFunction c t w ↔ w=cnotFunction c t v := by
    constructor
    · intro h
      rw [h,cnotFunction_involutive c t hct w]
    · intro h
      rw [h,cnotFunction_involutive c t hct v]
  simp only [heq]
  split_ifs <;> simp

theorem Gate.inverse_denote {n : ℕ} (g : Gate n) : g.inverse.denote=star g.denote := by
  cases g with
  | single i U => exact singleWire_star i U
  | cnot c t h => exact (cnot_denote_star c t h).symm

noncomputable def reverseCircuit {n : ℕ} (a : Circuit n) : Circuit n :=
  (a.reverse.map Gate.inverse)

theorem denote_reverseCircuit {n : ℕ} (a : Circuit n) :
    denote (reverseCircuit a)=star (denote a) := by
  induction a with
  | nil => simp [reverseCircuit,denote]
  | cons g gs ih =>
    simp only [reverseCircuit,List.reverse_cons,List.map_append,List.map_cons,List.map_nil,
      denote_append,denote,one_mul,Gate.inverse_denote]
    rw [← reverseCircuit,ih,star_mul]

theorem run_reverseCircuit {n : ℕ} (a : Circuit n) (v : Bits n → ℂ) :
    run (reverseCircuit a) (run a v)=v := by
  simp only [run,denote_reverseCircuit,Unitary.coe_star,Matrix.star_eq_conjTranspose,
    Matrix.mulVec_mulVec]
  have h := Unitary.coe_star_mul_self (denote a)
  simp only [Unitary.coe_star,Matrix.star_eq_conjTranspose] at h
  rw [h,Matrix.one_mulVec]

theorem reverseCircuit_length {n : ℕ} (a : Circuit n) :
    (reverseCircuit a).length=a.length := by simp [reverseCircuit]

end CircuitCompletion
