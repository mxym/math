import CircuitNumerical.PacketFrameDecoder

namespace CircuitRecursion.PacketFrameMachine

open Turing ListAssemblyMachine PacketFraming

abbrev SkipConfiguration := TM2.Cfg (fun _ : Stack => Symbol) Unit (Option Symbol)

def skipConfiguration (l : Option Unit) (v : Option Symbol) (input output work : List Symbol) : SkipConfiguration :=
  ⟨l,v,stackData input output work⟩

def stopped : Option Symbol → Bool
  | none | some .endPacket => true
  | _ => false

/-- A finite frame skipper. End-of-frame and EOF are tested by finite symbol
matching, not by a precomputed length or a natural-number loop counter. -/
def skipProgram : Unit → TM2.Stmt (fun _ : Stack => Symbol) Unit (Option Symbol) := fun _ =>
  .pop .left (fun _ x => x) (.branch stopped .halt (.goto (fun _ => ())))

def skipAdvance : Option SkipConfiguration → Option SkipConfiguration := fun c => c.bind (TM2.step skipProgram)

theorem skip_end (v : Option Symbol) (rest output work : List Symbol) :
    TM2.step skipProgram (skipConfiguration (some ()) v (.endPacket::rest) output work)=
      some (skipConfiguration none (some .endPacket) rest output work) := by
  simp only [skipConfiguration,TM2.step,skipProgram,TM2.stepAux,stackData_left,List.head?_cons,List.tail_cons,
    stopped,Bool.cond_true,update_stackData_left]

theorem skip_payload (v : Option Symbol) (a : Symbol) (ha : a≠.endPacket) (rest output work : List Symbol) :
    TM2.step skipProgram (skipConfiguration (some ()) v (a::rest) output work)=
      some (skipConfiguration (some ()) (some a) rest output work) := by
  cases a with
  | bit b => simp only [skipConfiguration,TM2.step,skipProgram,TM2.stepAux,stackData_left,List.head?_cons,List.tail_cons,
      stopped,Bool.cond_false,update_stackData_left]
  | field => simp only [skipConfiguration,TM2.step,skipProgram,TM2.stepAux,stackData_left,List.head?_cons,List.tail_cons,
      stopped,Bool.cond_false,update_stackData_left]
  | endPacket => exact (ha rfl).elim

theorem skip_halt (v : Option Symbol) (input output work : List Symbol) :
    TM2.step skipProgram (skipConfiguration none v input output work)=none := rfl

inductive CopyLabel where
  | scan | restore
  deriving DecidableEq
instance : Fintype CopyLabel := ⟨{.scan,.restore},by intro x;cases x <;> simp⟩
instance : Inhabited CopyLabel := ⟨.scan⟩

abbrev CopyConfiguration := TM2.Cfg (fun _ : Stack => Symbol) CopyLabel (Option Symbol)

def copyConfiguration (l : Option CopyLabel) (v : Option Symbol) (input output work : List Symbol) : CopyConfiguration :=
  ⟨l,v,stackData input output work⟩

/-- The scan copies each concrete symbol onto scratch, including endPacket;
restore reverses scratch onto the output. Each symbol is stored once per pass. -/
def copyProgram : CopyLabel → TM2.Stmt (fun _ : Stack => Symbol) CopyLabel (Option Symbol)
  | .scan => .pop .left (fun _ x => x)
      (.branch Option.isSome
        (.push .work (fun x => x.getD default)
          (.branch stopped (.goto (fun _ => .restore)) (.goto (fun _ => .scan))))
        .halt)
  | .restore => .pop .work (fun _ x => x)
      (.branch Option.isSome
        (.push .right (fun x => x.getD default) (.goto (fun _ => .restore)))
        .halt)

def copyAdvance : Option CopyConfiguration → Option CopyConfiguration := fun c => c.bind (TM2.step copyProgram)

theorem copy_end (v : Option Symbol) (rest output work : List Symbol) :
    TM2.step copyProgram (copyConfiguration (some .scan) v (.endPacket::rest) output work)=
      some (copyConfiguration (some .restore) (some .endPacket) rest output (.endPacket::work)) := by
  simp only [copyConfiguration,TM2.step,copyProgram,TM2.stepAux,stackData_left,stackData_work,List.head?_cons,List.tail_cons,
    Option.isSome_some,Option.getD_some,stopped,Bool.cond_true,update_stackData_left,update_stackData_work]

theorem copy_payload (v : Option Symbol) (a : Symbol) (ha : a≠.endPacket) (rest output work : List Symbol) :
    TM2.step copyProgram (copyConfiguration (some .scan) v (a::rest) output work)=
      some (copyConfiguration (some .scan) (some a) rest output (a::work)) := by
  cases a with
  | bit b => simp only [copyConfiguration,TM2.step,copyProgram,TM2.stepAux,stackData_left,stackData_work,
      List.head?_cons,List.tail_cons,Option.isSome_some,Option.getD_some,stopped,Bool.cond_true,Bool.cond_false,
      update_stackData_left,update_stackData_work]
  | field => simp only [copyConfiguration,TM2.step,copyProgram,TM2.stepAux,stackData_left,stackData_work,
      List.head?_cons,List.tail_cons,Option.isSome_some,Option.getD_some,stopped,Bool.cond_true,Bool.cond_false,
      update_stackData_left,update_stackData_work]
  | endPacket => exact (ha rfl).elim

theorem copy_restore_nil (v : Option Symbol) (input output : List Symbol) :
    TM2.step copyProgram (copyConfiguration (some .restore) v input output [])=
      some (copyConfiguration none none input output []) := by
  simp only [copyConfiguration,TM2.step,copyProgram,TM2.stepAux,stackData_work,List.head?_nil,List.tail_nil,
    Option.isSome_none,Bool.cond_false,update_stackData_work]

theorem copy_restore_cons (v : Option Symbol) (a : Symbol) (input output work : List Symbol) :
    TM2.step copyProgram (copyConfiguration (some .restore) v input output (a::work))=
      some (copyConfiguration (some .restore) (some a) input (a::output) work) := by
  simp only [copyConfiguration,TM2.step,copyProgram,TM2.stepAux,stackData_work,stackData_right,List.head?_cons,List.tail_cons,
    Option.isSome_some,Option.getD_some,Bool.cond_true,update_stackData_work,update_stackData_right]

theorem copy_halt (v : Option Symbol) (input output work : List Symbol) :
    TM2.step copyProgram (copyConfiguration none v input output work)=none := rfl

theorem skip_supports : TM2.Supports skipProgram Finset.univ :=
  ⟨Finset.mem_univ _,fun _ _ => TM2Subroutine.supportsStmt_univ _⟩

theorem copy_supports : TM2.Supports copyProgram Finset.univ :=
  ⟨Finset.mem_univ _,fun _ _ => TM2Subroutine.supportsStmt_univ _⟩

theorem skip_running_control_card : Fintype.card (Unit×Option Symbol)=5 := by decide
theorem copy_running_control_card : Fintype.card (CopyLabel×Option Symbol)=10 := by decide

theorem skip_statement_depth (q : Unit) : statementDepth (skipProgram q)=3 := rfl

theorem copy_statement_depth (q : CopyLabel) : statementDepth (copyProgram q)≤5 := by
  cases q <;> simp only [copyProgram,statementDepth] <;> omega

end CircuitRecursion.PacketFrameMachine
