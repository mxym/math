import CircuitNumerical.PacketStackPermutation

namespace CircuitRecursion.PacketRecordMachine

open Turing ListAssemblyMachine PacketFraming

abbrev Configuration (Λ : Type*) := TM2.Cfg (fun _ : Stack => Symbol) Λ (Option Symbol)
abbrev configuration {Λ : Type*} (l : Option Λ) (v : Option Symbol) (index scratch cache : List Symbol) : Configuration Λ :=
  PacketStackPermutation.configuration l v index scratch cache

def skipProgram (q : Unit) : TM2.Stmt (fun _ : Stack => Symbol) Unit (Option Symbol) :=
  PacketStackPermutation.compile PacketStackPermutation.frameRoles (PacketFrameMachine.skipProgram q)

def copyProgram (q : PacketFrameMachine.CopyLabel) :
    TM2.Stmt (fun _ : Stack => Symbol) PacketFrameMachine.CopyLabel (Option Symbol) :=
  PacketStackPermutation.compile PacketStackPermutation.frameRoles (PacketFrameMachine.copyProgram q)

/-- Actual frame scan with counter data retained on left, scratch on right,
and the variable packet cache on work. This is compiled syntax, not a stack
relocation pass performed by the value program. -/
def skipRecordRun (p : WordIntegerPacket) (rest index scratch : List Symbol) :
    StateTransition.EvalsToInTime (TM2.step skipProgram)
      (configuration (some ()) none index scratch (encodePacket p++rest))
      (some (configuration none (some .endPacket) index scratch rest)) (encodePacket p).length :=
  ⟨⟨(encodePacket p).length,by
    let run:=PacketStackPermutation.mapRun PacketStackPermutation.frameRoles PacketFrameMachine.skipProgram
      (PacketFrameMachine.skipPacketRun p rest index scratch)
    have hx:=run.evals_in_steps
    have hs : run.steps=(encodePacket p).length :=
      (PacketStackPermutation.mapRun_steps _ _ _).trans (PacketFrameMachine.skipPacketRun_steps p rest index scratch)
    rw [hs] at hx
    simp only [PacketStackPermutation.skip_roles] at hx
    exact hx⟩,le_refl _⟩

/-- Packet output is placed on left, cache tail remains on work, and right
scratch is cleared. The same Symbol-valued local memory fits the counter. -/
def copyRecordRun (p : WordIntegerPacket) (rest output : List Symbol) :
    StateTransition.EvalsToInTime (TM2.step copyProgram)
      (configuration (some .scan) none output [] (encodePacket p++rest))
      (some (configuration none none (encodePacket p++output) [] rest)) (2*(encodePacket p).length+1) :=
  ⟨⟨2*(encodePacket p).length+1,by
    let run:=PacketStackPermutation.mapRun PacketStackPermutation.frameRoles PacketFrameMachine.copyProgram
      (PacketFrameMachine.copyPacketRun p rest output)
    have hx:=run.evals_in_steps
    have hs : run.steps=2*(encodePacket p).length+1 :=
      (PacketStackPermutation.mapRun_steps _ _ _).trans (PacketFrameMachine.copyPacketRun_steps p rest output)
    rw [hs] at hx
    simp only [PacketStackPermutation.copy_roles] at hx
    exact hx⟩,le_refl _⟩

theorem skipRecordRun_steps (p : WordIntegerPacket) (rest index scratch : List Symbol) :
    (skipRecordRun p rest index scratch).steps=(encodePacket p).length := rfl

theorem copyRecordRun_steps (p : WordIntegerPacket) (rest output : List Symbol) :
    (copyRecordRun p rest output).steps=2*(encodePacket p).length+1 := rfl

theorem skip_statement_depth (q : Unit) : statementDepth (skipProgram q)=3 := by
  rw [skipProgram,PacketStackPermutation.compile_statementDepth]
  exact PacketFrameMachine.skip_statement_depth q

theorem copy_statement_depth (q : PacketFrameMachine.CopyLabel) : statementDepth (copyProgram q)≤5 := by
  rw [copyProgram,PacketStackPermutation.compile_statementDepth]
  exact PacketFrameMachine.copy_statement_depth q

end CircuitRecursion.PacketRecordMachine
