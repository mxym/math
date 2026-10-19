import CircuitNumerical.TM2ExtraStack

namespace CircuitRecursion.PacketQueryMachine

open Turing PacketFraming

/-- A fifth physical stack carries the next framed binary requests. The
existing four-stack master-cache reader remains intact. -/
abbrev Stack := PacketMasterMachine.Stack ⊕ Unit
abbrev Configuration (Λ : Type*) := TM2.Cfg (fun _ : Stack => Symbol) Λ (Option Symbol)

def stackData (index scratch cache master queries : List Symbol) : Stack → List Symbol
  | .inl k => PacketMasterMachine.stackData index scratch cache master k
  | .inr _ => queries

def configuration {Λ : Type*} (l : Option Λ) (v : Option Symbol)
    (index scratch cache master queries : List Symbol) : Configuration Λ :=
  ⟨l,v,stackData index scratch cache master queries⟩

theorem update_index (i s c m q xs : List Symbol) :
    Function.update (stackData i s c m q) (.inl (.inl .left)) xs=stackData xs s c m q := by
  funext k
  cases k with
  | inl k => cases k with
    | inl k => cases k <;> simp [stackData,PacketMasterMachine.stackData,Function.update]
    | inr k => simp [stackData,PacketMasterMachine.stackData,Function.update]
  | inr k => simp [stackData,Function.update]

theorem update_scratch (i s c m q xs : List Symbol) :
    Function.update (stackData i s c m q) (.inl (.inl .right)) xs=stackData i xs c m q := by
  funext k
  cases k with
  | inl k => cases k with
    | inl k => cases k <;> simp [stackData,PacketMasterMachine.stackData,Function.update]
    | inr k => simp [stackData,PacketMasterMachine.stackData,Function.update]
  | inr k => simp [stackData,Function.update]

theorem update_cache (i s c m q xs : List Symbol) :
    Function.update (stackData i s c m q) (.inl (.inl .work)) xs=stackData i s xs m q := by
  funext k
  cases k with
  | inl k => cases k with
    | inl k => cases k <;> simp [stackData,PacketMasterMachine.stackData,Function.update]
    | inr k => simp [stackData,PacketMasterMachine.stackData,Function.update]
  | inr k => simp [stackData,Function.update]

theorem update_queries (i s c m q xs : List Symbol) :
    Function.update (stackData i s c m q) (.inr ()) xs=stackData i s c m xs := by
  funext k
  cases k with
  | inl k => cases k with
    | inl k => cases k <;> simp [stackData,PacketMasterMachine.stackData,Function.update]
    | inr k => simp [stackData,PacketMasterMachine.stackData,Function.update]
  | inr k => cases k;simp [stackData,Function.update]

inductive SetupLabel where
  | clearIndex | clearScratch | clearCache | load | restore
  deriving DecidableEq
instance : Fintype SetupLabel := ⟨{.clearIndex,.clearScratch,.clearCache,.load,.restore},by intro x;cases x <;> simp⟩
instance : Inhabited SetupLabel := ⟨.clearIndex⟩

abbrev Label := SetupLabel ⊕ PacketMasterMachine.Label

def isBit : Option Symbol → Bool
  | some (.bit _) => true
  | _ => false

def isBoundary : Option Symbol → Bool
  | some .field => true
  | _ => false

/-- Three explicit clear loops and a two-pass request installer, followed
by the complete finite master-cache reader. No free reset or index adapter. -/
def program : Label → TM2.Stmt (fun _ : Stack => Symbol) Label (Option Symbol)
  | .inl .clearIndex => .pop (.inl (.inl .left)) (fun _ x => x)
      (.branch Option.isSome (.goto (fun _ => .inl .clearIndex)) (.goto (fun _ => .inl .clearScratch)))
  | .inl .clearScratch => .pop (.inl (.inl .right)) (fun _ x => x)
      (.branch Option.isSome (.goto (fun _ => .inl .clearScratch)) (.goto (fun _ => .inl .clearCache)))
  | .inl .clearCache => .pop (.inl (.inl .work)) (fun _ x => x)
      (.branch Option.isSome (.goto (fun _ => .inl .clearCache)) (.goto (fun _ => .inl .load)))
  | .inl .load => .pop (.inr ()) (fun _ x => x)
      (.branch isBit
        (.push (.inl (.inl .right)) (fun x => x.getD default) (.goto (fun _ => .inl .load)))
        (.branch isBoundary (.goto (fun _ => .inl .restore)) .halt))
  | .inl .restore => .pop (.inl (.inl .right)) (fun _ x => x)
      (.branch Option.isSome
        (.push (.inl (.inl .left)) (fun x => x.getD default) (.goto (fun _ => .inl .restore)))
        (.load (fun _ => none) (.goto (fun _ => .inr (.inl .move)))))
  | .inr q => TM2ExtraStack.compile Sum.inr (PacketMasterMachine.program q)

def advance : Option (Configuration Label) → Option (Configuration Label) :=
  fun c => c.bind (TM2.step program)

/-- The stream already contains encoded bits. Forming this source encoding
is not charged as part of the machine that consumes it. -/
def queryCode (bits : List Bool) : List Symbol := bits.map Symbol.bit++[.field]

theorem clear_index_nil (v : Option Symbol) (s c m q : List Symbol) :
    TM2.step program (configuration (some (.inl .clearIndex)) v [] s c m q)=
      some (configuration (some (.inl .clearScratch)) none [] s c m q) := by
  simp only [configuration,TM2.step,program,TM2.stepAux,stackData,PacketMasterMachine.stackData,
    List.head?_nil,List.tail_nil,Option.isSome_none,Bool.cond_false,update_index]

theorem clear_index_cons (v : Option Symbol) (a : Symbol) (i s c m q : List Symbol) :
    TM2.step program (configuration (some (.inl .clearIndex)) v (a::i) s c m q)=
      some (configuration (some (.inl .clearIndex)) (some a) i s c m q) := by
  simp only [configuration,TM2.step,program,TM2.stepAux,stackData,PacketMasterMachine.stackData,
    List.head?_cons,List.tail_cons,Option.isSome_some,Bool.cond_true,update_index]

theorem clear_scratch_nil (v : Option Symbol) (i c m q : List Symbol) :
    TM2.step program (configuration (some (.inl .clearScratch)) v i [] c m q)=
      some (configuration (some (.inl .clearCache)) none i [] c m q) := by
  simp only [configuration,TM2.step,program,TM2.stepAux,stackData,PacketMasterMachine.stackData,
    List.head?_nil,List.tail_nil,Option.isSome_none,Bool.cond_false,update_scratch]

theorem clear_scratch_cons (v : Option Symbol) (a : Symbol) (i s c m q : List Symbol) :
    TM2.step program (configuration (some (.inl .clearScratch)) v i (a::s) c m q)=
      some (configuration (some (.inl .clearScratch)) (some a) i s c m q) := by
  simp only [configuration,TM2.step,program,TM2.stepAux,stackData,PacketMasterMachine.stackData,
    List.head?_cons,List.tail_cons,Option.isSome_some,Bool.cond_true,update_scratch]

theorem clear_cache_nil (v : Option Symbol) (i s m q : List Symbol) :
    TM2.step program (configuration (some (.inl .clearCache)) v i s [] m q)=
      some (configuration (some (.inl .load)) none i s [] m q) := by
  simp only [configuration,TM2.step,program,TM2.stepAux,stackData,PacketMasterMachine.stackData,
    List.head?_nil,List.tail_nil,Option.isSome_none,Bool.cond_false,update_cache]

theorem clear_cache_cons (v : Option Symbol) (a : Symbol) (i s c m q : List Symbol) :
    TM2.step program (configuration (some (.inl .clearCache)) v i s (a::c) m q)=
      some (configuration (some (.inl .clearCache)) (some a) i s c m q) := by
  simp only [configuration,TM2.step,program,TM2.stepAux,stackData,PacketMasterMachine.stackData,
    List.head?_cons,List.tail_cons,Option.isSome_some,Bool.cond_true,update_cache]

theorem load_bit (v : Option Symbol) (b : Bool) (s m q : List Symbol) :
    TM2.step program (configuration (some (.inl .load)) v [] s [] m (.bit b::q))=
      some (configuration (some (.inl .load)) (some (.bit b)) [] (.bit b::s) [] m q) := by
  simp only [configuration,TM2.step,program,TM2.stepAux,stackData,PacketMasterMachine.stackData,
    List.head?_cons,List.tail_cons,isBit,Option.getD_some,Bool.cond_true,update_queries,update_scratch]

theorem load_boundary (v : Option Symbol) (s m q : List Symbol) :
    TM2.step program (configuration (some (.inl .load)) v [] s [] m (.field::q))=
      some (configuration (some (.inl .restore)) (some .field) [] s [] m q) := by
  simp only [configuration,TM2.step,program,TM2.stepAux,stackData,PacketMasterMachine.stackData,
    List.head?_cons,List.tail_cons,isBit,isBoundary,Bool.cond_true,Bool.cond_false,update_queries]

theorem load_eof (v : Option Symbol) (m : List Symbol) :
    TM2.step program (configuration (some (.inl .load)) v [] [] [] m [])=
      some (configuration none none [] [] [] m []) := by
  simp only [configuration,TM2.step,program,TM2.stepAux,stackData,PacketMasterMachine.stackData,
    List.head?_nil,List.tail_nil,isBit,isBoundary,Bool.cond_false,update_queries]

theorem restore_nil (v : Option Symbol) (i m q : List Symbol) :
    TM2.step program (configuration (some (.inl .restore)) v i [] [] m q)=
      some (configuration (some (.inr (.inl .move))) none i [] [] m q) := by
  simp only [configuration,TM2.step,program,TM2.stepAux,stackData,PacketMasterMachine.stackData,
    List.head?_nil,List.tail_nil,Option.isSome_none,Bool.cond_false,update_scratch]

theorem restore_cons (v : Option Symbol) (a : Symbol) (i s m q : List Symbol) :
    TM2.step program (configuration (some (.inl .restore)) v i (a::s) [] m q)=
      some (configuration (some (.inl .restore)) (some a) (a::i) s [] m q) := by
  simp only [configuration,TM2.step,program,TM2.stepAux,stackData,PacketMasterMachine.stackData,
    List.head?_cons,List.tail_cons,Option.isSome_some,Option.getD_some,Bool.cond_true,update_scratch,update_index]

end CircuitRecursion.PacketQueryMachine
