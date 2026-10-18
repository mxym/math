import CircuitNumerical.FiniteBinaryCounter

namespace CircuitRecursion.BinaryCounterMachine

set_option maxHeartbeats 1500000

theorem drain_iterate (v : Option Bool) (as bs ws : List Bool) :
    advance^[as.length+1] (some (configuration (.some .drain) v as bs ws))=
      some (configuration (.some .restore) none [] (as.reverse++bs) ws) := by
  induction as generalizing v bs with
  | nil => change Turing.TM2.step program (configuration (.some .drain) v [] bs ws)=_;exact drain_nil v bs ws
  | cons a as ih =>
    rw [List.length_cons,Function.iterate_succ_apply]
    change advance^[as.length+1] (Turing.TM2.step program (configuration (.some .drain) v (a::as) bs ws))=_
    rw [drain_cons,ih]
    simp only [List.reverse_cons,List.append_assoc,List.cons_append,List.nil_append]

theorem restore_iterate (v : Option Bool) (as bs ws : List Bool) :
    advance^[bs.length+1] (some (configuration (.some .restore) v as bs ws))=
      some (configuration none none (bs.reverse++as) [] ws) := by
  induction bs generalizing v as with
  | nil => change Turing.TM2.step program (configuration (.some .restore) v as [] ws)=_;exact restore_nil v as ws
  | cons b bs ih =>
    rw [List.length_cons,Function.iterate_succ_apply]
    change advance^[bs.length+1] (Turing.TM2.step program (configuration (.some .restore) v as (b::bs) ws))=_
    rw [restore_cons,ih]
    simp only [List.reverse_cons,List.append_assoc,List.cons_append,List.nil_append]

theorem clear_iterate (v : Option Bool) (as bs ws : List Bool) :
    advance^[bs.length+1] (some (configuration (.some .clear) v as bs ws))=
      some (configuration none none as [] ws) := by
  induction bs generalizing v with
  | nil => change Turing.TM2.step program (configuration (.some .clear) v as [] ws)=_;exact clear_nil v as ws
  | cons b bs ih =>
    rw [List.length_cons,Function.iterate_succ_apply]
    change advance^[bs.length+1] (Turing.TM2.step program (configuration (.some .clear) v as (b::bs) ws))=_
    rw [clear_cons,ih]

/-- This recursively defined number is only an external mathematical time
index. The machine never constructs or inspects it. -/
def borrowTime : List Bool → ℕ → ℕ
  | [],b => b+2
  | false::as,b => borrowTime as (b+1)+1
  | true::[],b => b+2
  | true::a::as,b => 2*(a::as).length+b+4

theorem borrowTime_bound (as : List Bool) (b : ℕ) : borrowTime as b≤2*as.length+b+2 := by
  induction as generalizing b with
  | nil => simp only [borrowTime,List.length_nil,Nat.mul_zero,Nat.zero_add,le_refl]
  | cons a as ih =>
    cases a with
    | false => simp only [borrowTime,List.length_cons];have h:=ih (b+1);omega
    | true =>
      cases as with
      | nil => simp only [borrowTime,List.length_nil,List.length_cons];omega
      | cons c cs => simp only [borrowTime,List.length_cons];omega

/-- All inputs in this lemma are represented counter words; canonicality is
a data invariant, not a time or final-result certificate. -/
theorem borrow_iterate_positive (as : List Bool) (h : BinaryWordCanonical as) (hne : as≠[])
    (v : Option Bool) (bs ws : List Bool) :
    advance^[borrowTime as bs.length] (some (configuration (.some .borrow) v as bs ws))=
      some (configuration none none (bs.reverse++binaryPredecessorBits as) [] ws) := by
  induction h generalizing v bs with
  | nil => exact (hne rfl).elim
  | one =>
    rw [borrowTime,show bs.length+2=(bs.length+1)+1 by omega,Function.iterate_succ_apply]
    change advance^[bs.length+1] (Turing.TM2.step program (configuration (.some .borrow) v [true] bs ws))=_
    rw [borrow_true_nil,restore_iterate]
    simp only [binaryPredecessorBits,List.append_nil]
  | prepend b c cs hc ih =>
    cases b with
    | false =>
      rw [borrowTime,Function.iterate_succ_apply]
      change advance^[borrowTime (c::cs) (bs.length+1)]
        (Turing.TM2.step program (configuration (.some .borrow) v (false::c::cs) bs ws))=_
      rw [borrow_false]
      have hit:=ih (by simp) (some false) (true::bs)
      rw [show (true::bs).length=bs.length+1 by rfl] at hit
      rw [hit]
      simp only [List.reverse_cons,List.append_assoc,List.cons_append,List.nil_append,binaryPredecessorBits]
    | true =>
      let rest:=c::cs
      let reversed:=rest.reverse++false::bs
      have ht : borrowTime (true::c::cs) bs.length=(reversed.length+1)+(rest.length+1)+1 := by
        dsimp only [borrowTime,reversed,rest]
        simp only [List.length_append,List.length_reverse,List.length_cons]
        omega
      rw [ht,Function.iterate_succ_apply]
      change advance^[(reversed.length+1)+(rest.length+1)]
        (Turing.TM2.step program (configuration (.some .borrow) v (true::c::cs) bs ws))=_
      rw [borrow_true_cons,Function.iterate_add_apply,drain_iterate]
      change advance^[reversed.length+1]
        (some (configuration (.some .restore) none [] reversed ws))=_
      rw [restore_iterate]
      simp only [reversed,rest,List.reverse_append,List.reverse_cons,List.reverse_reverse,
        List.append_assoc,List.cons_append,List.nil_append,List.append_nil,binaryPredecessorBits]

theorem counter_iterate (as : List Bool) (h : BinaryWordCanonical as) (ws : List Bool) :
    advance^[borrowTime as 0] (some (configuration (.some .borrow) none as [] ws))=
      some (configuration none none (binaryPredecessorBits as) [] ws) := by
  cases as with
  | nil =>
    change advance^[1+1] (some (configuration (.some .borrow) none [] [] ws))=_
    rw [Function.iterate_succ_apply]
    change advance^[1] (Turing.TM2.step program (configuration (.some .borrow) none [] [] ws))=_
    rw [borrow_nil]
    exact clear_iterate none [] [] ws
  | cons b bs =>
    simpa only [List.length_nil,List.reverse_nil,List.nil_append] using
      borrow_iterate_positive (b::bs) h (by simp) none [] ws

end CircuitRecursion.BinaryCounterMachine
