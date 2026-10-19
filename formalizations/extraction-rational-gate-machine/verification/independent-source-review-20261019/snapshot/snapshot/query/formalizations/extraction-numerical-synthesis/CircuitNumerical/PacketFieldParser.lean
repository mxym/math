import CircuitNumerical.PacketQueryTwice

namespace CircuitRecursion.PacketFieldMachine

open Turing PacketFraming

inductive Coordinate where
  | n0 | n1 | n2 | n3
  deriving DecidableEq
instance : Fintype Coordinate := ⟨{.n0,.n1,.n2,.n3},by intro q;cases q <;> simp⟩
instance : Inhabited Coordinate := ⟨.n0⟩

inductive Stack where
  | input | scratch | numerator : Coordinate → Stack
  | denominator
  deriving DecidableEq
instance : Fintype Stack := ⟨{.input,.scratch,.numerator .n0,.numerator .n1,.numerator .n2,.numerator .n3,.denominator},by
  intro k;cases k with
  | input | scratch | denominator => simp
  | numerator q => cases q <;> simp⟩

abbrev Alphabet : Stack → Type
  | .input => Symbol
  | _ => Bool

abbrev Flags := Bool×Bool×Bool×Bool
abbrev Memory := Flags×Option Symbol×Bool

def setSign (q : Coordinate) (f : Flags) (b : Bool) : Flags :=
  match q with
  | .n0 => (b,f.2.1,f.2.2.1,f.2.2.2)
  | .n1 => (f.1,b,f.2.2.1,f.2.2.2)
  | .n2 => (f.1,f.2.1,b,f.2.2.2)
  | .n3 => (f.1,f.2.1,f.2.2.1,b)

def getBit : Option Symbol → Bool
  | some (.bit b) => b
  | _ => false

def withCell (m : Memory) (v : Option Symbol) : Memory := (m.1,v,m.2.2)
def withSign (q : Coordinate) (m : Memory) : Memory := (setSign q m.1 (getBit m.2.1),m.2.1,m.2.2)
def isBit (m : Memory) : Bool := PacketQueryMachine.isBit m.2.1
def isBoundary (m : Memory) : Bool := PacketQueryMachine.isBoundary m.2.1
def isEnd (m : Memory) : Bool := match m.2.1 with | some .endPacket => true | _ => false

def stackData (input : List Symbol) (scratch : List Bool) (fields : Coordinate → List Bool)
    (denominator : List Bool) : ∀ k,List (Alphabet k)
  | .input => input
  | .scratch => scratch
  | .numerator q => fields q
  | .denominator => denominator

inductive Label where
  | sign : Coordinate → Label
  | scan : Coordinate → Label
  | restore : Coordinate → Label
  | denScan | denRestore
  deriving DecidableEq
instance : Fintype Label := ⟨{.sign .n0,.sign .n1,.sign .n2,.sign .n3,
  .scan .n0,.scan .n1,.scan .n2,.scan .n3,.restore .n0,.restore .n1,.restore .n2,.restore .n3,.denScan,.denRestore},by
  intro l;cases l with
  | sign q | scan q | restore q => cases q <;> simp
  | denScan | denRestore => simp⟩
instance : Inhabited Label := ⟨.sign .n0⟩

abbrev Configuration := TM2.Cfg Alphabet Label Memory

def configuration (l : Option Label) (f : Flags) (v : Option Symbol) (accepted : Bool)
    (input : List Symbol) (scratch : List Bool) (fields : Coordinate → List Bool) (denominator : List Bool) : Configuration :=
  ⟨l,(f,v,accepted),stackData input scratch fields denominator⟩

def next : Coordinate → Label
  | .n0 => .sign .n1
  | .n1 => .sign .n2
  | .n2 => .sign .n3
  | .n3 => .denScan

/-- A concrete heterogeneous-alphabet parser. Symbol input is consumed one
cell at a time; all scratch and five output stacks contain native Bool bits.
The four signs and parse status are finite control memory, not Nat values. -/
def program : Label → TM2.Stmt Alphabet Label Memory
  | .sign q => .pop .input withCell
      (.branch isBit (.load (withSign q) (.goto (fun _ => .scan q))) .halt)
  | .scan q => .pop .input withCell
      (.branch isBit (.push .scratch (fun m => getBit m.2.1) (.goto (fun _ => .scan q)))
        (.branch isBoundary (.goto (fun _ => .restore q)) .halt))
  | .restore q => .pop .scratch (fun m x => withCell m (x.map Symbol.bit))
      (.branch (fun m => m.2.1.isSome)
        (.push (.numerator q) (fun m => getBit m.2.1) (.goto (fun _ => .restore q)))
        (.goto (fun _ => next q)))
  | .denScan => .pop .input withCell
      (.branch isBit (.push .scratch (fun m => getBit m.2.1) (.goto (fun _ => .denScan)))
        (.branch isEnd (.goto (fun _ => .denRestore)) .halt))
  | .denRestore => .pop .scratch (fun m x => withCell m (x.map Symbol.bit))
      (.branch (fun m => m.2.1.isSome)
        (.push .denominator (fun m => getBit m.2.1) (.goto (fun _ => .denRestore)))
        (.load (fun m => (m.1,none,true)) .halt))

def advance : Option Configuration → Option Configuration := fun c => c.bind (TM2.step program)

theorem update_input (i : List Symbol) (s : List Bool) (f : Coordinate → List Bool) (d : List Bool) (xs : List Symbol) :
    Function.update (stackData i s f d) .input xs=stackData xs s f d := by
  funext k;cases k <;> simp [stackData,Function.update,Alphabet] <;> rfl

theorem update_scratch (i : List Symbol) (s : List Bool) (f : Coordinate → List Bool) (d xs : List Bool) :
    Function.update (stackData i s f d) .scratch xs=stackData i xs f d := by
  funext k;cases k <;> simp [stackData,Function.update,Alphabet] <;> rfl

theorem update_numerator (i : List Symbol) (s : List Bool) (f : Coordinate → List Bool) (d : List Bool)
    (q : Coordinate) (xs : List Bool) :
    Function.update (stackData i s f d) (.numerator q) xs=stackData i s (Function.update f q xs) d := by
  funext k
  cases k with
  | input | scratch | denominator => simp [stackData,Function.update,Alphabet] <;> rfl
  | numerator j =>
    by_cases hj : j=q
    · subst j;simp [stackData,Function.update,Alphabet] <;> rfl
    · simp [stackData,Function.update,hj,Alphabet] <;> rfl

theorem update_denominator (i : List Symbol) (s : List Bool) (f : Coordinate → List Bool) (d xs : List Bool) :
    Function.update (stackData i s f d) .denominator xs=stackData i s f xs := by
  funext k;cases k <;> simp [stackData,Function.update,Alphabet] <;> rfl

theorem fields_update_twice (f : Coordinate → List Bool) (q : Coordinate) (xs ys : List Bool) :
    Function.update (Function.update f q xs) q ys=Function.update f q ys := by
  funext j
  by_cases hj : j=q
  · subst j;simp only [Function.update_self]
  · simp only [Function.update_of_ne hj]

theorem sign_bit (q : Coordinate) (flags : Flags) (v : Option Symbol) (ok b : Bool)
    (rest : List Symbol) (s : List Bool) (fields : Coordinate → List Bool) (d : List Bool) :
    TM2.step program (configuration (some (.sign q)) flags v ok (.bit b::rest) s fields d)=
      some (configuration (some (.scan q)) (setSign q flags b) (some (.bit b)) ok rest s fields d) := by
  simp only [configuration,TM2.step,program,TM2.stepAux,stackData,List.head?,List.tail,
    withCell,isBit,PacketQueryMachine.isBit,Bool.cond_true,withSign,getBit,update_input]

theorem scan_bit (q : Coordinate) (flags : Flags) (v : Option Symbol) (ok b : Bool)
    (rest : List Symbol) (s : List Bool) (fields : Coordinate → List Bool) (d : List Bool) :
    TM2.step program (configuration (some (.scan q)) flags v ok (.bit b::rest) s fields d)=
      some (configuration (some (.scan q)) flags (some (.bit b)) ok rest (b::s) fields d) := by
  simp only [configuration,TM2.step,program,TM2.stepAux,stackData,List.head?,List.tail,
    withCell,isBit,PacketQueryMachine.isBit,Bool.cond_true,getBit,update_input,update_scratch]

theorem scan_boundary (q : Coordinate) (flags : Flags) (v : Option Symbol) (ok : Bool)
    (rest : List Symbol) (s : List Bool) (fields : Coordinate → List Bool) (d : List Bool) :
    TM2.step program (configuration (some (.scan q)) flags v ok (.field::rest) s fields d)=
      some (configuration (some (.restore q)) flags (some .field) ok rest s fields d) := by
  simp only [configuration,TM2.step,program,TM2.stepAux,stackData,List.head?,List.tail,
    withCell,isBit,PacketQueryMachine.isBit,isBoundary,PacketQueryMachine.isBoundary,Bool.cond_true,Bool.cond_false,update_input]

theorem restore_nil (q : Coordinate) (flags : Flags) (v : Option Symbol) (ok : Bool)
    (rest : List Symbol) (fields : Coordinate → List Bool) (d : List Bool) :
    TM2.step program (configuration (some (.restore q)) flags v ok rest [] fields d)=
      some (configuration (some (next q)) flags none ok rest [] fields d) := by
  simp only [configuration,TM2.step,program,TM2.stepAux,stackData,List.head?,List.tail,
    Option.map_none,withCell,Option.isSome_none,Bool.cond_false,update_scratch]

theorem restore_cons (q : Coordinate) (flags : Flags) (v : Option Symbol) (ok b : Bool)
    (rest : List Symbol) (s : List Bool) (fields : Coordinate → List Bool) (d : List Bool) :
    TM2.step program (configuration (some (.restore q)) flags v ok rest (b::s) fields d)=
      some (configuration (some (.restore q)) flags (some (.bit b)) ok rest s (Function.update fields q (b::fields q)) d) := by
  simp only [configuration,TM2.step,program,TM2.stepAux,stackData,List.head?,List.tail,
    Option.map_some,withCell,Option.isSome_some,Bool.cond_true,getBit,update_scratch,update_numerator]

theorem den_bit (flags : Flags) (v : Option Symbol) (ok b : Bool)
    (rest : List Symbol) (s : List Bool) (fields : Coordinate → List Bool) (d : List Bool) :
    TM2.step program (configuration (some .denScan) flags v ok (.bit b::rest) s fields d)=
      some (configuration (some .denScan) flags (some (.bit b)) ok rest (b::s) fields d) := by
  simp only [configuration,TM2.step,program,TM2.stepAux,stackData,List.head?,List.tail,
    withCell,isBit,PacketQueryMachine.isBit,Bool.cond_true,getBit,update_input,update_scratch]

theorem den_end (flags : Flags) (v : Option Symbol) (ok : Bool)
    (rest : List Symbol) (s : List Bool) (fields : Coordinate → List Bool) (d : List Bool) :
    TM2.step program (configuration (some .denScan) flags v ok (.endPacket::rest) s fields d)=
      some (configuration (some .denRestore) flags (some .endPacket) ok rest s fields d) := by
  simp only [configuration,TM2.step,program,TM2.stepAux,stackData,List.head?,List.tail,
    withCell,isBit,PacketQueryMachine.isBit,isEnd,Bool.cond_true,Bool.cond_false,update_input]

theorem den_restore_nil (flags : Flags) (v : Option Symbol) (ok : Bool)
    (rest : List Symbol) (fields : Coordinate → List Bool) (d : List Bool) :
    TM2.step program (configuration (some .denRestore) flags v ok rest [] fields d)=
      some (configuration none flags none true rest [] fields d) := by
  simp only [configuration,TM2.step,program,TM2.stepAux,stackData,List.head?,List.tail,
    Option.map_none,withCell,Option.isSome_none,Bool.cond_false,update_scratch]

theorem den_restore_cons (flags : Flags) (v : Option Symbol) (ok b : Bool)
    (rest : List Symbol) (s : List Bool) (fields : Coordinate → List Bool) (d : List Bool) :
    TM2.step program (configuration (some .denRestore) flags v ok rest (b::s) fields d)=
      some (configuration (some .denRestore) flags (some (.bit b)) ok rest s fields (b::d)) := by
  simp only [configuration,TM2.step,program,TM2.stepAux,stackData,List.head?,List.tail,
    Option.map_some,withCell,Option.isSome_some,Bool.cond_true,getBit,update_scratch,update_denominator]

end CircuitRecursion.PacketFieldMachine
