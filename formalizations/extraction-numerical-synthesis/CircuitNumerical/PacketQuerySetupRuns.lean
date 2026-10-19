import CircuitNumerical.PacketQuerySetup

namespace CircuitRecursion.PacketQueryMachine

open Turing PacketFraming

set_option maxHeartbeats 1500000

theorem clear_index_iterate (v : Option Symbol) (i s c m q : List Symbol) :
    advance^[i.length+1] (some (configuration (some (.inl .clearIndex)) v i s c m q))=
      some (configuration (some (.inl .clearScratch)) none [] s c m q) := by
  induction i generalizing v with
  | nil => exact clear_index_nil v s c m q
  | cons a i ih =>
    rw [List.length_cons,Function.iterate_succ_apply]
    change advance^[i.length+1] (TM2.step program
      (configuration (some (.inl .clearIndex)) v (a::i) s c m q))=_
    rw [clear_index_cons,ih]

theorem clear_scratch_iterate (v : Option Symbol) (i s c m q : List Symbol) :
    advance^[s.length+1] (some (configuration (some (.inl .clearScratch)) v i s c m q))=
      some (configuration (some (.inl .clearCache)) none i [] c m q) := by
  induction s generalizing v with
  | nil => exact clear_scratch_nil v i c m q
  | cons a s ih =>
    rw [List.length_cons,Function.iterate_succ_apply]
    change advance^[s.length+1] (TM2.step program
      (configuration (some (.inl .clearScratch)) v i (a::s) c m q))=_
    rw [clear_scratch_cons,ih]

theorem clear_cache_iterate (v : Option Symbol) (i s c m q : List Symbol) :
    advance^[c.length+1] (some (configuration (some (.inl .clearCache)) v i s c m q))=
      some (configuration (some (.inl .load)) none i s [] m q) := by
  induction c generalizing v with
  | nil => exact clear_cache_nil v i s m q
  | cons a c ih =>
    rw [List.length_cons,Function.iterate_succ_apply]
    change advance^[c.length+1] (TM2.step program
      (configuration (some (.inl .clearCache)) v i s (a::c) m q))=_
    rw [clear_cache_cons,ih]

theorem clear_iterate (v : Option Symbol) (i s c m q : List Symbol) :
    advance^[i.length+s.length+c.length+3]
      (some (configuration (some (.inl .clearIndex)) v i s c m q))=
      some (configuration (some (.inl .load)) none [] [] [] m q) := by
  rw [show i.length+s.length+c.length+3=(s.length+c.length+2)+(i.length+1) by omega,
    Function.iterate_add_apply,clear_index_iterate]
  rw [show s.length+c.length+2=(c.length+1)+(s.length+1) by omega,
    Function.iterate_add_apply,clear_scratch_iterate,clear_cache_iterate]

theorem load_iterate (bits : List Bool) (v : Option Symbol) (s m rest : List Symbol) :
    advance^[bits.length+1]
      (some (configuration (some (.inl .load)) v [] s [] m (bits.map Symbol.bit++Symbol.field::rest)))=
      some (configuration (some (.inl .restore)) (some .field) [] ((bits.map Symbol.bit).reverse++s) [] m rest) := by
  induction bits generalizing v s with
  | nil => exact load_boundary v s m rest
  | cons b bits ih =>
    rw [List.length_cons,Function.iterate_succ_apply]
    change advance^[bits.length+1] (TM2.step program
      (configuration (some (.inl .load)) v [] s [] m (.bit b::(bits.map Symbol.bit++Symbol.field::rest))))=_
    rw [load_bit,ih]
    simp only [List.map_cons,List.reverse_cons,List.append_assoc,List.cons_append,List.nil_append]

theorem restore_iterate (v : Option Symbol) (i s m q : List Symbol) :
    advance^[s.length+1] (some (configuration (some (.inl .restore)) v i s [] m q))=
      some (configuration (some (.inr (.inl .move))) none (s.reverse++i) [] [] m q) := by
  induction s generalizing v i with
  | nil => exact restore_nil v i m q
  | cons a s ih =>
    rw [List.length_cons,Function.iterate_succ_apply]
    change advance^[s.length+1] (TM2.step program
      (configuration (some (.inl .restore)) v i (a::s) [] m q))=_
    rw [restore_cons,ih]
    simp only [List.reverse_cons,List.append_assoc,List.cons_append,List.nil_append]

theorem install_iterate (bits : List Bool) (m rest : List Symbol) :
    advance^[2*bits.length+2]
      (some (configuration (some (.inl .load)) none [] [] [] m (queryCode bits++rest)))=
      some (configuration (some (.inr (.inl .move))) none (bits.map Symbol.bit) [] [] m rest) := by
  rw [show 2*bits.length+2=((bits.map Symbol.bit).reverse.length+1)+(bits.length+1) by
    simp only [List.length_reverse,List.length_map];omega,Function.iterate_add_apply]
  simp only [queryCode,List.append_assoc,List.singleton_append]
  rw [load_iterate]
  simp only [List.append_nil]
  rw [restore_iterate]
  simp only [List.reverse_reverse,List.append_nil]

theorem setup_iterate (v : Option Symbol) (i s c m : List Symbol) (bits : List Bool) (rest : List Symbol) :
    advance^[i.length+s.length+c.length+2*bits.length+5]
      (some (configuration (some (.inl .clearIndex)) v i s c m (queryCode bits++rest)))=
      some (configuration (some (.inr (.inl .move))) none (bits.map Symbol.bit) [] [] m rest) := by
  rw [show i.length+s.length+c.length+2*bits.length+5=
    (2*bits.length+2)+(i.length+s.length+c.length+3) by omega,
    Function.iterate_add_apply,clear_iterate,install_iterate]

/-- Exact real cleanup and request-stream installation. No input-stack
release/reset, stream copy, traversal or reversal is assigned zero cost. -/
def setupRun (v : Option Symbol) (i s c m : List Symbol) (bits : List Bool) (rest : List Symbol) :
    StateTransition.EvalsToInTime (TM2.step program)
      (configuration (some (.inl .clearIndex)) v i s c m (queryCode bits++rest))
      (some (configuration (some (.inr (.inl .move))) none (bits.map Symbol.bit) [] [] m rest))
      (i.length+s.length+c.length+2*bits.length+5) :=
  ⟨⟨i.length+s.length+c.length+2*bits.length+5,setup_iterate v i s c m bits rest⟩,le_rfl⟩

theorem setupRun_steps (v : Option Symbol) (i s c m : List Symbol) (bits : List Bool) (rest : List Symbol) :
    (setupRun v i s c m bits rest).steps=i.length+s.length+c.length+2*bits.length+5 := rfl

/-- An exhausted request stream is detected by a real pop after all cleanup. -/
def eofRun (v : Option Symbol) (i s c m : List Symbol) :
    StateTransition.EvalsToInTime (TM2.step program)
      (configuration (some (.inl .clearIndex)) v i s c m [])
      (some (configuration none none [] [] [] m [])) (i.length+s.length+c.length+4) :=
  ⟨⟨i.length+s.length+c.length+4,by
    change advance^[i.length+s.length+c.length+4] (some (configuration (some (.inl .clearIndex)) v i s c m []))=_
    rw [show i.length+s.length+c.length+4=1+(i.length+s.length+c.length+3) by omega,
      Function.iterate_add_apply,clear_iterate]
    exact load_eof none m⟩,le_rfl⟩

end CircuitRecursion.PacketQueryMachine
