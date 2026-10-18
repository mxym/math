import CircuitNumerical.FiniteBinaryCounterRuns

namespace CircuitRecursion.BinaryCounterMachine

/-- The real finite counter run. The proof computes its bound from input
representation invariants; no final result or timing certificate is assumed. -/
def counterRun (as : List Bool) (h : BinaryWordCanonical as) (ws : List Bool) :
    StateTransition.EvalsToInTime (Turing.TM2.step program)
      (configuration (.some .borrow) none as [] ws)
      (some (configuration none none (binaryPredecessorBits as) [] ws)) (2*as.length+2) :=
  ⟨⟨borrowTime as 0,counter_iterate as h ws⟩,by simpa only [Nat.add_zero] using borrowTime_bound as 0⟩

theorem counterRun_steps (as : List Bool) (h : BinaryWordCanonical as) (ws : List Bool) :
    (counterRun as h ws).steps=borrowTime as 0 := rfl

theorem counterRun_steps_bound (as : List Bool) (h : BinaryWordCanonical as) (ws : List Bool) :
    (counterRun as h ws).steps≤2*as.length+2 := (counterRun as h ws).steps_le_m

def terminal (as ws : List Bool) : Configuration := configuration none none (binaryPredecessorBits as) [] ws

theorem terminal_halts (as ws : List Bool) : Turing.TM2.step program (terminal as ws)=none := rfl

theorem counter_mem_eval (as : List Bool) (h : BinaryWordCanonical as) (ws : List Bool) :
    terminal as ws∈StateTransition.eval (Turing.TM2.step program) (configuration (.some .borrow) none as [] ws) :=
  ListAssemblyMachine.evalsTo_terminal_mem_eval (counterRun as h ws).toEvalsTo (terminal_halts as ws)

theorem terminal_counter_value (as : List Bool) (h : BinaryWordCanonical as) (ws : List Bool) :
    binaryWordValue ((terminal as ws).stk .left)=binaryWordValue as-1 :=
  binaryPredecessorBits_value as h

theorem terminal_counter_canonical (as : List Bool) (h : BinaryWordCanonical as) (ws : List Bool) :
    BinaryWordCanonical ((terminal as ws).stk .left) := binaryPredecessorBits_canonical as h

theorem terminal_counter_length (as : List Bool) (h : BinaryWordCanonical as) (ws : List Bool) :
    ((terminal as ws).stk .left).length≤as.length := binaryPredecessorBits_length as h

theorem terminal_scratch_empty (as ws : List Bool) : (terminal as ws).stk .right=[] := rfl

theorem terminal_preserves_work (as ws : List Bool) : (terminal as ws).stk .work=ws := rfl

theorem terminal_counter_progress (as : List Bool) (h : BinaryWordCanonical as) (hne : as≠[])
    (ws : List Bool) : binaryWordValue ((terminal as ws).stk .left)+1=binaryWordValue as := by
  have hpos : binaryWordValue as≠0 := by
    intro hz
    exact hne ((binaryWordCanonical_zero_iff as h).mp hz)
  rw [terminal_counter_value as h ws]
  omega

/-- A height hypothesis is a property of encoded input data. It bounds the
proved actual counter run by canonicality; it is not a runtime hypothesis. -/
theorem counterRun_steps_height (as : List Bool) (h : BinaryWordCanonical as) (ws : List Bool)
    (B : ℕ) (hv : binaryWordValue as≤2^B) : (counterRun as h ws).steps≤2*B+4 := by
  have hw:=binaryWordCanonical_width as h B hv
  have hs:=counterRun_steps_bound as h ws
  omega

theorem counter_nat_le_two_pow (P : ℕ) : P≤2^P := by
  induction P with
  | zero => decide
  | succ P ih =>
    have hp : 1≤2^P := Nat.one_le_pow _ _ (by decide)
    rw [pow_succ]
    omega

theorem counterRun_steps_index_bound (as : List Bool) (h : BinaryWordCanonical as) (ws : List Bool)
    (P : ℕ) (hv : binaryWordValue as≤P) : (counterRun as h ws).steps≤2*P+4 :=
  counterRun_steps_height as h ws P (hv.trans (counter_nat_le_two_pow P))

end CircuitRecursion.BinaryCounterMachine
