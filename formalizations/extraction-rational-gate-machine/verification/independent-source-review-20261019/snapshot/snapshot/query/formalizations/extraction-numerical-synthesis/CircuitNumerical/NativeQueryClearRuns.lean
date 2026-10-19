import CircuitNumerical.NativeQueryController

namespace CircuitRecursion.NativeQueryMachine

open Turing PacketFraming

set_option maxHeartbeats 1500000

theorem clearAll_iterate (m : Memory) (S : PacketQueryMachine.Stack → List Symbol) (words : WordStack → List Bool) :
    advance^[wordVolume words+6] (some (configuration (some (.inl .scratch)) m S words))=
      some (configuration (some (readerEmbed (.inl .clearIndex))) resetMemory S emptyWords) := by
  let ws1:=Function.update words .scratch []
  let ws2:=Function.update ws1 (.numerator .n0) []
  let ws3:=Function.update ws2 (.numerator .n1) []
  let ws4:=Function.update ws3 (.numerator .n2) []
  let ws5:=Function.update ws4 (.numerator .n3) []
  let ws6:=Function.update ws5 .denominator []
  rw [show wordVolume words+6=((words (.numerator .n0)).length+(words (.numerator .n1)).length+(words (.numerator .n2)).length+(words (.numerator .n3)).length+(words .denominator).length+5)+((words .scratch).length+1) by unfold wordVolume;omega,
    Function.iterate_add_apply]
  rw [clearWord_iterate]
  simp only [clearNext,clearFinishMemory]
  rw [show (words (.numerator .n0)).length+(words (.numerator .n1)).length+(words (.numerator .n2)).length+(words (.numerator .n3)).length+(words .denominator).length+5=((words (.numerator .n1)).length+(words (.numerator .n2)).length+(words (.numerator .n3)).length+(words .denominator).length+4)+((words (.numerator .n0)).length+1) by omega,
    Function.iterate_add_apply]
  rw [show (words (.numerator .n0)).length+1=(ws1 (.numerator .n0)).length+1 by rfl]
  rw [clearWord_iterate]
  simp only [clearNext,clearFinishMemory]
  rw [show (words (.numerator .n1)).length+(words (.numerator .n2)).length+(words (.numerator .n3)).length+(words .denominator).length+4=((words (.numerator .n2)).length+(words (.numerator .n3)).length+(words .denominator).length+3)+((words (.numerator .n1)).length+1) by omega,
    Function.iterate_add_apply]
  rw [show (words (.numerator .n1)).length+1=(ws2 (.numerator .n1)).length+1 by rfl]
  rw [clearWord_iterate]
  simp only [clearNext,clearFinishMemory]
  rw [show (words (.numerator .n2)).length+(words (.numerator .n3)).length+(words .denominator).length+3=((words (.numerator .n3)).length+(words .denominator).length+2)+((words (.numerator .n2)).length+1) by omega,
    Function.iterate_add_apply]
  rw [show (words (.numerator .n2)).length+1=(ws3 (.numerator .n2)).length+1 by rfl]
  rw [clearWord_iterate]
  simp only [clearNext,clearFinishMemory]
  rw [show (words (.numerator .n3)).length+(words .denominator).length+2=((words .denominator).length+1)+((words (.numerator .n3)).length+1) by omega,
    Function.iterate_add_apply]
  rw [show (words (.numerator .n3)).length+1=(ws4 (.numerator .n3)).length+1 by rfl]
  rw [clearWord_iterate]
  simp only [clearNext,clearFinishMemory]
  rw [show (words .denominator).length+1=(ws5 .denominator).length+1 by rfl]
  rw [clearWord_iterate]
  simp only [clearNext,clearFinishMemory]
  apply congrArg some
  unfold configuration
  congr 1
  funext k
  cases k with
  | inl k => rfl
  | inr k => cases k with
    | scratch | denominator => rfl
    | numerator q => cases q <;> rfl

/-- All six previous native-word stacks are popped, including explicit EOF
checks; finite control is actually reset before the query entry goto. -/
def clearRun (m : Memory) (S : PacketQueryMachine.Stack → List Symbol) (words : WordStack → List Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      (configuration (some (.inl .scratch)) m S words)
      (some (configuration (some (readerEmbed (.inl .clearIndex))) resetMemory S emptyWords)) (wordVolume words+6) :=
  ⟨⟨wordVolume words+6,clearAll_iterate m S words⟩,le_rfl⟩

theorem clearRun_steps (m : Memory) (S : PacketQueryMachine.Stack → List Symbol) (words : WordStack → List Bool) :
    (clearRun m S words).steps=wordVolume words+6 := rfl

end CircuitRecursion.NativeQueryMachine
