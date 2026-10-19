import CircuitNumerical.PacketFrameRuns

namespace CircuitRecursion.PacketCounterLift

open Turing ListAssemblyMachine PacketFraming

def liftMemory (v : Option Bool) : Option Symbol := v.map Symbol.bit

def lowerMemory : Option Symbol → Option Bool
  | some (.bit b) => some b
  | _ => none

theorem lower_lift_memory (v : Option Bool) : lowerMemory (liftMemory v)=v := by
  cases v <;> rfl

/-- The packet stream lives on work. Only the two binary-counter stacks are
encoded through bit; the untouched packet stream may contain separators. -/
def liftStacks (S : Stack → List Bool) (frame : List Symbol) : Stack → List Symbol
  | .left => (S .left).map Symbol.bit
  | .right => (S .right).map Symbol.bit
  | .work => frame

def liftConfiguration {Λ : Type*} (c : TM2.Cfg (fun _ : Stack => Bool) Λ (Option Bool))
    (frame : List Symbol) : TM2.Cfg (fun _ : Stack => Symbol) Λ (Option Symbol) :=
  ⟨c.l,liftMemory c.var,liftStacks c.stk frame⟩

def WorkFree {Λ : Type*} : TM2.Stmt (fun _ : Stack => Bool) Λ (Option Bool) → Prop
  | .push k _ q | .peek k _ q | .pop k _ q => k≠.work ∧ WorkFree q
  | .load _ q => WorkFree q
  | .branch _ q r => WorkFree q ∧ WorkFree r
  | .goto _ | .halt => True

/-- A concrete syntax compiler. The counter's local bit values are embedded
in the finite packet alphabet; its frame stack is never inspected. -/
def compile {Λ : Type*} : TM2.Stmt (fun _ : Stack => Bool) Λ (Option Bool) →
    TM2.Stmt (fun _ : Stack => Symbol) Λ (Option Symbol)
  | .push k f q => .push k (fun v => .bit (f (lowerMemory v))) (compile q)
  | .peek k f q => .peek k (fun v x => liftMemory (f (lowerMemory v) (lowerMemory x))) (compile q)
  | .pop k f q => .pop k (fun v x => liftMemory (f (lowerMemory v) (lowerMemory x))) (compile q)
  | .load f q => .load (fun v => liftMemory (f (lowerMemory v))) (compile q)
  | .branch f q r => .branch (fun v => f (lowerMemory v)) (compile q) (compile r)
  | .goto f => .goto (fun v => f (lowerMemory v))
  | .halt => .halt

theorem liftStacks_active (S : Stack → List Bool) (frame : List Symbol) (k : Stack) (h : k≠.work) :
    liftStacks S frame k=(S k).map Symbol.bit := by
  cases k with
  | left => rfl
  | right => rfl
  | work => exact (h rfl).elim

theorem liftStacks_update (S : Stack → List Bool) (frame : List Symbol) (k : Stack) (h : k≠.work)
    (bs : List Bool) :
    liftStacks (Function.update S k bs) frame=Function.update (liftStacks S frame) k (bs.map Symbol.bit) := by
  funext j
  cases k with
  | left => cases j <;> rfl
  | right => cases j <;> rfl
  | work => exact (h rfl).elim

theorem lower_head_map (bs : List Bool) : lowerMemory ((bs.map Symbol.bit).head?)=bs.head? := by
  cases bs <;> rfl

theorem tail_map (bs : List Bool) : (bs.map Symbol.bit).tail=bs.tail.map Symbol.bit := by
  cases bs <;> rfl

theorem compile_stepAux {Λ : Type*} (q : TM2.Stmt (fun _ : Stack => Bool) Λ (Option Bool))
    (hq : WorkFree q) (v : Option Bool) (S : Stack → List Bool) (frame : List Symbol) :
    TM2.stepAux (compile q) (liftMemory v) (liftStacks S frame)=
      liftConfiguration (TM2.stepAux q v S) frame := by
  induction q generalizing v S with
  | push k f q ih =>
    rcases hq with ⟨hk,hq⟩
    simp only [compile,TM2.stepAux,lower_lift_memory,liftStacks_active S frame k hk]
    rw [←List.map_cons,←liftStacks_update S frame k hk]
    exact ih hq v _
  | peek k f q ih =>
    rcases hq with ⟨hk,hq⟩
    simp only [compile,TM2.stepAux,lower_lift_memory,liftStacks_active S frame k hk,lower_head_map]
    exact ih hq _ S
  | pop k f q ih =>
    rcases hq with ⟨hk,hq⟩
    simp only [compile,TM2.stepAux,lower_lift_memory,liftStacks_active S frame k hk,lower_head_map,tail_map]
    rw [←liftStacks_update S frame k hk]
    exact ih hq _ _
  | load f q ih =>
    simp only [compile,TM2.stepAux,lower_lift_memory]
    exact ih hq _ S
  | branch f q r iq ir =>
    rcases hq with ⟨hq,hr⟩
    simp only [compile,TM2.stepAux,lower_lift_memory]
    cases f v <;> simp only [Bool.cond_false,Bool.cond_true] <;> first | exact iq hq v S | exact ir hr v S
  | goto f => simp only [compile,TM2.stepAux,lower_lift_memory,liftConfiguration]
  | halt => rfl

theorem compile_statementDepth {Λ : Type*} (q : TM2.Stmt (fun _ : Stack => Bool) Λ (Option Bool)) :
    statementDepth (compile q)=statementDepth q := by
  induction q with
  | push k f q ih | peek k f q ih | pop k f q ih | load f q ih => simp only [compile,statementDepth,ih]
  | branch f q r iq ir => simp only [compile,statementDepth,iq,ir]
  | goto f => rfl
  | halt => rfl

end CircuitRecursion.PacketCounterLift
