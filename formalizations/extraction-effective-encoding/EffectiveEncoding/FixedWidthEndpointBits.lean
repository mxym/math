import EffectiveEncoding.UnaryWordEncoding
import EffectiveEncoding.CarriedOccupationRank

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

/-- The actual branch taken at each fixed-width output digit. -/
inductive EndpointBitTrace where
  | done
  | zeroPad : EndpointBitTrace → EndpointBitTrace
  | copied : Bool → EndpointBitTrace → EndpointBitTrace

structure EndpointBitsResult (n : ℕ) where
  bits : List.Vector Bool n
  trace : EndpointBitTrace

/-- One structural pass over at most n input digits, emitting exactly n
output cons cells. It neither divides a Nat nor calls Nat.testBit/Nat.bits. -/
def endpointBitsProgram : (n : ℕ) → List Bool → EndpointBitsResult n
  | 0,_ => ⟨List.Vector.nil,.done⟩
  | n+1,[] =>
    let tail:=endpointBitsProgram n []
    ⟨List.Vector.cons false tail.bits,.zeroPad tail.trace⟩
  | n+1,b::bs =>
    let tail:=endpointBitsProgram n bs
    ⟨List.Vector.cons b tail.bits,.copied b tail.trace⟩


theorem endpointBitsProgram_get (n : ℕ) (bs : List Bool) (i : Fin n) :
    (endpointBitsProgram n bs).bits.get i=bs.getD i.val false := by
  induction n generalizing bs with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    cases bs with
    | nil =>
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · simpa only [endpointBitsProgram,List.Vector.get_cons_succ,List.getD_nil] using ih [] j
    | cons b bs =>
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · change (endpointBitsProgram n bs).bits.get j=bs.getD j.val false
        exact ih bs j

/-- Proof bridge only; endpointBitsProgram does not execute this Nat view. -/
theorem binaryWordValue_testBit_getD (bs : List Bool) (j : ℕ) :
    (binaryWordValue bs).testBit j=bs.getD j false := by
  induction bs generalizing j with
  | nil => simp [binaryWordValue]
  | cons b bs ih =>
    cases j with
    | zero => cases b <;> simp [binaryWordValue,binaryBitValue,Nat.testBit_zero,Nat.add_mod]
    | succ j =>
      rw [Nat.testBit_succ]
      cases b <;> simpa [binaryWordValue,binaryBitValue,Nat.add_mul_div_left] using ih j

/-- Specified output-list primitives: terminal test, zero-test/cons for a
padding digit, or read/cons for a copied digit. Nat recursion/control and trace
record bookkeeping remain separate from this counter. -/
def EndpointBitTrace.listActions : EndpointBitTrace → ℕ
  | .done => 1
  | .zeroPad t => t.listActions+2
  | .copied _ t => t.listActions+3


theorem endpointBitsProgram_listActions (n : ℕ) (bs : List Bool) :
    (endpointBitsProgram n bs).trace.listActions≤3*n+1 := by
  induction n generalizing bs with
  | zero => exact le_rfl
  | succ n ih =>
    cases bs with
    | nil =>
      have h:=ih []
      change (endpointBitsProgram n []).trace.listActions+2≤3*(n+1)+1
      omega
    | cons b bs =>
      have h:=ih bs
      change (endpointBitsProgram n bs).trace.listActions+3≤3*(n+1)+1
      omega

end EffectiveEncoding
