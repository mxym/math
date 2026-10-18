import CircuitRecursion.PureInput

open scoped BigOperators
open Matrix CircuitCompletion SymmetricSupport
namespace CircuitRecursion

set_option maxHeartbeats 800000

noncomputable def bellPairsWord : (h : ℕ) → Circuit (originalWireCount h)
  | 0 => []
  | h+1 => (show Circuit (originalWireCount (h+1)) from
      liftCircuit (originalWireCount h) bellPreparationWord)++
      (show Circuit (originalWireCount (h+1)) from shiftCircuit 2 (bellPairsWord h))

noncomputable def bellPairsVector : (h : ℕ) → Bits (originalWireCount h) → ℂ
  | 0 => fun _ => 1
  | h+1 => fun w => Extraction.bellVector (d := Bool) (invSqrtTwo : ℂ)
      ((prefixBits w) 0,(prefixBits w) 1)*bellPairsVector h (suffixBits w)

theorem zeroBits_append (q r : ℕ) :
    Fin.append (zeroBits q) (zeroBits r)=zeroBits (q+r) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [zeroBits]

/-- A literal H/CNOT pair for each of h existing zero pairs, coherently and
without a reset, preparation primitive, or extra wire. -/
theorem bellPairsWord_action (h : ℕ) :
    run (bellPairsWord h) (Pi.single (zeroBits (originalWireCount h)) 1)=
      bellPairsVector h := by
  induction h with
  | zero =>
    ext w
    have hw : zeroBits (originalWireCount 0)=w := by funext i; exact Fin.elim0 i
    simp [bellPairsWord,run,denote,bellPairsVector,hw]
  | succ h ih =>
    rw [bellPairsWord,run_append]
    have hz : (Pi.single (zeroBits (originalWireCount (h+1))) 1 :
        Bits (originalWireCount (h+1)) → ℂ)=fun w =>
        (Pi.single (zeroBits 2) 1 : Bits 2 → ℂ) (prefixBits w)*
        (Pi.single (zeroBits (originalWireCount h)) 1 :
          Bits (originalWireCount h) → ℂ) (suffixBits w) := by
      have he := single_append (zeroBits 2) (zeroBits (originalWireCount h))
      rw [zeroBits_append] at he
      exact he
    rw [hz]
    erw [run_liftCircuit,bellPreparationWord_action]
    have he := run_shiftCircuit (bellPairsWord h)
      (Pi.single (zeroBits (originalWireCount h)) 1)
      (fun a : Bits 2 => Extraction.bellVector (d := Bool) (invSqrtTwo : ℂ) (a 0,a 1))
    rw [ih] at he
    exact he

theorem bellPairsWord_length (h : ℕ) : (bellPairsWord h).length=2*h := by
  induction h with
  | zero => rfl
  | succ h ih =>
    rw [bellPairsWord]
    erw [List.length_append,liftCircuit_length,shiftCircuit_length,bellPreparationWord_length,ih]
    omega

def pairwiseCoordinates (h : ℕ) : Bits (originalWireCount h) ≃ Bits h×Bits h :=
  (originalBitCoordinates h).symm.trans
    ((Equiv.piCongrRight (fun _ => letterBits.trans bitPair)).trans
      ((splitCopies Bool Bool h).trans (Equiv.prodComm _ _)))

theorem pairwiseCoordinates_append (h : ℕ) (a : Bits 2) (b : Bits (originalWireCount h)) :
    pairwiseCoordinates (h+1) (Fin.append a b)=
      (Fin.cons (a 1) (pairwiseCoordinates h b).1,
        Fin.cons (a 0) (pairwiseCoordinates h b).2) := by
  obtain ⟨i,rfl⟩ := letterBits.surjective a
  change ((fun j => (letterBits ((originalBitCoordinates (h+1)).symm
    (Fin.append (letterBits i) b) j)) 1),
      (fun j => (letterBits ((originalBitCoordinates (h+1)).symm
    (Fin.append (letterBits i) b) j)) 0))=_
  rw [originalBitCoordinates_cons_symm]
  apply Prod.ext <;> funext j <;> refine Fin.cases ?_ (fun t => ?_) j <;> rfl

theorem cons_eq_iff {α : Type*} {h : ℕ} (a b : α) (x y : Fin h → α) :
    (Fin.cons a x : Fin (h+1) → α)=(Fin.cons b y : Fin (h+1) → α) ↔ a=b ∧ x=y := by
  constructor
  · intro he
    exact ⟨congrFun he 0,funext (fun j => congrFun he j.succ)⟩
  · rintro ⟨rfl,rfl⟩; rfl

theorem bellPairsVector_coordinates (h : ℕ) (w : Bits (originalWireCount h)) :
    bellPairsVector h w=Extraction.bellVector (d := Bits h)
      ((invSqrtTwo : ℂ)^h) (pairwiseCoordinates h w) := by
  induction h with
  | zero =>
    have he : (pairwiseCoordinates 0 w).1=(pairwiseCoordinates 0 w).2 := Subsingleton.elim _ _
    simp [bellPairsVector,Extraction.bellVector,he]
  | succ h ih =>
    obtain ⟨⟨a,b⟩,rfl⟩ := (splitRegister 2 (originalWireCount h)).symm.surjective w
    change bellPairsVector (h+1) (Fin.append a b)=Extraction.bellVector (d := Bits (h+1))
      ((invSqrtTwo : ℂ)^(h+1)) (pairwiseCoordinates (h+1) (Fin.append a b))
    rw [bellPairsVector]
    simp only [prefix_append,suffix_append]
    rw [ih]
    erw [pairwiseCoordinates_append]
    simp only [Extraction.bellVector,cons_eq_iff]
    by_cases ha : a 0=a 1 <;>
      by_cases hb : (pairwiseCoordinates h b).1=(pairwiseCoordinates h b).2 <;>
        simp [ha,hb,pow_succ,mul_comm,eq_comm]

theorem sqrt_two_pow (h : ℕ) : Real.sqrt ((2 : ℝ)^h)=(Real.sqrt 2)^h := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [pow_succ,Real.sqrt_mul (pow_nonneg (by norm_num) h),ih,pow_succ]

theorem bellPairs_coefficient (h : ℕ) :
    (invSqrtTwo : ℂ)^h=Extraction.bellCoeff (Bits h) := by
  rw [invSqrtTwo_bellCoeff]
  simp [Extraction.bellCoeff,Bits,sqrt_two_pow,div_pow]

theorem bellPairsVector_standard (h : ℕ) (w : Bits (originalWireCount h)) :
    bellPairsVector h w=Extraction.bellVector (Extraction.bellCoeff (Bits h))
      (pairwiseCoordinates h w) := by
  rw [bellPairsVector_coordinates,bellPairs_coefficient]

theorem letterBits_physical (i : Fin 4) :
    letterBits i 1=finTwoEquiv ((finProdFinEquiv : Fin 2×Fin 2 ≃ Fin 4).symm i).1 ∧
      letterBits i 0=finTwoEquiv ((finProdFinEquiv : Fin 2×Fin 2 ≃ Fin 4).symm i).2 := by
  fin_cases i <;> decide

end CircuitRecursion
