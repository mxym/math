import CircuitNumerical.NativeQueryReuse

namespace CircuitRecursion.PacketSerializerMachine

open Turing PacketFraming

abbrev Stack := PacketFieldMachine.Stack
abbrev Alphabet := PacketFieldMachine.Alphabet
abbrev Coordinate := PacketFieldMachine.Coordinate
abbrev Memory := PacketFieldMachine.Memory
abbrev Flags := PacketFieldMachine.Flags

inductive Label where
  | clearScratch | start | denRead | denWrite
  | beginNum : Coordinate → Label
  | readNum : Coordinate → Label
  | writeNum : Coordinate → Label
  | finishNum : Coordinate → Label
  deriving DecidableEq
instance : Fintype Label := ⟨{.clearScratch,.start,.denRead,.denWrite,
  .beginNum .n0,.beginNum .n1,.beginNum .n2,.beginNum .n3,
  .readNum .n0,.readNum .n1,.readNum .n2,.readNum .n3,
  .writeNum .n0,.writeNum .n1,.writeNum .n2,.writeNum .n3,
  .finishNum .n0,.finishNum .n1,.finishNum .n2,.finishNum .n3},by
  intro q;cases q with
  | clearScratch | start | denRead | denWrite => simp
  | beginNum q | readNum q | writeNum q | finishNum q => cases q <;> simp⟩
instance : Inhabited Label := ⟨.clearScratch⟩

abbrev Configuration := TM2.Cfg Alphabet Label Memory

def configuration (l : Option Label) (flags : Flags) (v : Option Symbol) (ok : Bool)
    (output : List Symbol) (scratch : List Bool) (fields : Coordinate → List Bool) (denominator : List Bool) : Configuration :=
  ⟨l,(flags,v,ok),PacketFieldMachine.stackData output scratch fields denominator⟩

def signBit (q : Coordinate) (flags : Flags) : Bool :=
  match q with
  | .n0 => flags.1
  | .n1 => flags.2.1
  | .n2 => flags.2.2.1
  | .n3 => flags.2.2.2

def next : Coordinate → Option Label
  | .n0 => none
  | .n1 => some (.beginNum .n0)
  | .n2 => some (.beginNum .n1)
  | .n3 => some (.beginNum .n2)

def finish (q : Coordinate) : TM2.Stmt Alphabet Label Memory :=
  .push .input (fun m => .bit (signBit q m.1))
    (match q with
      | .n0 => .halt
      | .n1 => .goto (fun _ => .beginNum .n0)
      | .n2 => .goto (fun _ => .beginNum .n1)
      | .n3 => .goto (fun _ => .beginNum .n2))

/-- Real serialization consumes native Bool word stacks, reverses each word
through Bool scratch and pushes concrete framed Symbol cells. Output is a
prefix of the existing Symbol suffix, not an atomic packet append. -/
def program : Label → TM2.Stmt Alphabet Label Memory
  | .clearScratch => .pop .scratch (fun m x => PacketFieldMachine.withCell m (x.map Symbol.bit))
      (.branch (fun m => m.2.1.isSome) (.goto (fun _ => .clearScratch)) (.goto (fun _ => .start)))
  | .start => .push .input (fun _ => .endPacket) (.goto (fun _ => .denRead))
  | .denRead => .pop .denominator (fun m x => PacketFieldMachine.withCell m (x.map Symbol.bit))
      (.branch (fun m => m.2.1.isSome)
        (.push .scratch (fun m => PacketFieldMachine.getBit m.2.1) (.goto (fun _ => .denRead)))
        (.goto (fun _ => .denWrite)))
  | .denWrite => .pop .scratch (fun m x => PacketFieldMachine.withCell m (x.map Symbol.bit))
      (.branch (fun m => m.2.1.isSome)
        (.push .input (fun m => .bit (PacketFieldMachine.getBit m.2.1)) (.goto (fun _ => .denWrite)))
        (.goto (fun _ => .beginNum .n3)))
  | .beginNum q => .push .input (fun _ => .field) (.goto (fun _ => .readNum q))
  | .readNum q => .pop (.numerator q) (fun m x => PacketFieldMachine.withCell m (x.map Symbol.bit))
      (.branch (fun m => m.2.1.isSome)
        (.push .scratch (fun m => PacketFieldMachine.getBit m.2.1) (.goto (fun _ => .readNum q)))
        (.goto (fun _ => .writeNum q)))
  | .writeNum q => .pop .scratch (fun m x => PacketFieldMachine.withCell m (x.map Symbol.bit))
      (.branch (fun m => m.2.1.isSome)
        (.push .input (fun m => .bit (PacketFieldMachine.getBit m.2.1)) (.goto (fun _ => .writeNum q)))
        (.goto (fun _ => .finishNum q)))
  | .finishNum q => finish q

def advance : Option Configuration → Option Configuration := fun c => c.bind (TM2.step program)

theorem clear_nil (flags : Flags) (v : Option Symbol) (ok : Bool) (out : List Symbol)
    (fields : Coordinate → List Bool) (d : List Bool) :
    TM2.step program (configuration (some .clearScratch) flags v ok out [] fields d)=
      some (configuration (some .start) flags none ok out [] fields d) := by
  simp only [configuration,TM2.step,program,TM2.stepAux,PacketFieldMachine.stackData,List.head?_nil,List.tail_nil,
    Option.map_none,PacketFieldMachine.withCell,Option.isSome_none,Bool.cond_false,PacketFieldMachine.update_scratch]

theorem clear_cons (flags : Flags) (v : Option Symbol) (ok b : Bool) (out : List Symbol) (s : List Bool)
    (fields : Coordinate → List Bool) (d : List Bool) :
    TM2.step program (configuration (some .clearScratch) flags v ok out (b::s) fields d)=
      some (configuration (some .clearScratch) flags (some (.bit b)) ok out s fields d) := by
  simp only [configuration,TM2.step,program,TM2.stepAux,PacketFieldMachine.stackData,List.head?_cons,List.tail_cons,
    Option.map_some,PacketFieldMachine.withCell,Option.isSome_some,Bool.cond_true,PacketFieldMachine.update_scratch]

theorem start_step (flags : Flags) (v : Option Symbol) (ok : Bool) (out : List Symbol)
    (fields : Coordinate → List Bool) (d : List Bool) :
    TM2.step program (configuration (some .start) flags v ok out [] fields d)=
      some (configuration (some .denRead) flags v ok (.endPacket::out) [] fields d) := by
  simp only [configuration,TM2.step,program,TM2.stepAux,PacketFieldMachine.stackData,PacketFieldMachine.update_input]

theorem denRead_nil (flags : Flags) (v : Option Symbol) (ok : Bool) (out : List Symbol) (s : List Bool)
    (fields : Coordinate → List Bool) :
    TM2.step program (configuration (some .denRead) flags v ok out s fields [])=
      some (configuration (some .denWrite) flags none ok out s fields []) := by
  simp only [configuration,TM2.step,program,TM2.stepAux,PacketFieldMachine.stackData,List.head?_nil,List.tail_nil,
    Option.map_none,PacketFieldMachine.withCell,Option.isSome_none,Bool.cond_false,PacketFieldMachine.update_denominator]

theorem denRead_cons (flags : Flags) (v : Option Symbol) (ok b : Bool) (out : List Symbol) (s : List Bool)
    (fields : Coordinate → List Bool) (d : List Bool) :
    TM2.step program (configuration (some .denRead) flags v ok out s fields (b::d))=
      some (configuration (some .denRead) flags (some (.bit b)) ok out (b::s) fields d) := by
  simp only [configuration,TM2.step,program,TM2.stepAux,PacketFieldMachine.stackData,List.head?_cons,List.tail_cons,
    Option.map_some,PacketFieldMachine.withCell,Option.isSome_some,Bool.cond_true,PacketFieldMachine.getBit,
    PacketFieldMachine.update_denominator,PacketFieldMachine.update_scratch]

theorem denWrite_nil (flags : Flags) (v : Option Symbol) (ok : Bool) (out : List Symbol)
    (fields : Coordinate → List Bool) (d : List Bool) :
    TM2.step program (configuration (some .denWrite) flags v ok out [] fields d)=
      some (configuration (some (.beginNum .n3)) flags none ok out [] fields d) := by
  simp only [configuration,TM2.step,program,TM2.stepAux,PacketFieldMachine.stackData,List.head?_nil,List.tail_nil,
    Option.map_none,PacketFieldMachine.withCell,Option.isSome_none,Bool.cond_false,PacketFieldMachine.update_scratch]

theorem denWrite_cons (flags : Flags) (v : Option Symbol) (ok b : Bool) (out : List Symbol) (s : List Bool)
    (fields : Coordinate → List Bool) (d : List Bool) :
    TM2.step program (configuration (some .denWrite) flags v ok out (b::s) fields d)=
      some (configuration (some .denWrite) flags (some (.bit b)) ok (.bit b::out) s fields d) := by
  simp only [configuration,TM2.step,program,TM2.stepAux,PacketFieldMachine.stackData,List.head?_cons,List.tail_cons,
    Option.map_some,PacketFieldMachine.withCell,Option.isSome_some,Bool.cond_true,PacketFieldMachine.getBit,
    PacketFieldMachine.update_scratch,PacketFieldMachine.update_input]

theorem beginNum_step (q : Coordinate) (flags : Flags) (v : Option Symbol) (ok : Bool) (out : List Symbol)
    (fields : Coordinate → List Bool) (d : List Bool) :
    TM2.step program (configuration (some (.beginNum q)) flags v ok out [] fields d)=
      some (configuration (some (.readNum q)) flags v ok (.field::out) [] fields d) := by
  simp only [configuration,TM2.step,program,TM2.stepAux,PacketFieldMachine.stackData,PacketFieldMachine.update_input]

theorem readNum_nil (q : Coordinate) (flags : Flags) (v : Option Symbol) (ok : Bool) (out : List Symbol)
    (s : List Bool) (fields : Coordinate → List Bool) (d : List Bool) :
    TM2.step program (configuration (some (.readNum q)) flags v ok out s (Function.update fields q []) d)=
      some (configuration (some (.writeNum q)) flags none ok out s (Function.update fields q []) d) := by
  simp only [configuration,TM2.step,program,TM2.stepAux,PacketFieldMachine.stackData,Function.update_self,
    List.head?_nil,List.tail_nil,Option.map_none,PacketFieldMachine.withCell,Option.isSome_none,Bool.cond_false,
    PacketFieldMachine.update_numerator,PacketFieldMachine.fields_update_twice]

theorem readNum_cons (q : Coordinate) (flags : Flags) (v : Option Symbol) (ok b : Bool) (out : List Symbol)
    (s : List Bool) (fields : Coordinate → List Bool) (d bs : List Bool) :
    TM2.step program (configuration (some (.readNum q)) flags v ok out s (Function.update fields q (b::bs)) d)=
      some (configuration (some (.readNum q)) flags (some (.bit b)) ok out (b::s) (Function.update fields q bs) d) := by
  simp only [configuration,TM2.step,program,TM2.stepAux,PacketFieldMachine.stackData,Function.update_self,
    List.head?_cons,List.tail_cons,Option.map_some,PacketFieldMachine.withCell,Option.isSome_some,Bool.cond_true,
    PacketFieldMachine.getBit,PacketFieldMachine.update_numerator,PacketFieldMachine.fields_update_twice,
    PacketFieldMachine.update_scratch]

theorem writeNum_nil (q : Coordinate) (flags : Flags) (v : Option Symbol) (ok : Bool) (out : List Symbol)
    (fields : Coordinate → List Bool) (d : List Bool) :
    TM2.step program (configuration (some (.writeNum q)) flags v ok out [] fields d)=
      some (configuration (some (.finishNum q)) flags none ok out [] fields d) := by
  simp only [configuration,TM2.step,program,TM2.stepAux,PacketFieldMachine.stackData,List.head?_nil,List.tail_nil,
    Option.map_none,PacketFieldMachine.withCell,Option.isSome_none,Bool.cond_false,PacketFieldMachine.update_scratch]

theorem writeNum_cons (q : Coordinate) (flags : Flags) (v : Option Symbol) (ok b : Bool) (out : List Symbol) (s : List Bool)
    (fields : Coordinate → List Bool) (d : List Bool) :
    TM2.step program (configuration (some (.writeNum q)) flags v ok out (b::s) fields d)=
      some (configuration (some (.writeNum q)) flags (some (.bit b)) ok (.bit b::out) s fields d) := by
  simp only [configuration,TM2.step,program,TM2.stepAux,PacketFieldMachine.stackData,List.head?_cons,List.tail_cons,
    Option.map_some,PacketFieldMachine.withCell,Option.isSome_some,Bool.cond_true,PacketFieldMachine.getBit,
    PacketFieldMachine.update_scratch,PacketFieldMachine.update_input]

theorem finishNum_step (q : Coordinate) (flags : Flags) (v : Option Symbol) (ok : Bool) (out : List Symbol)
    (fields : Coordinate → List Bool) (d : List Bool) :
    TM2.step program (configuration (some (.finishNum q)) flags v ok out [] fields d)=
      some (configuration (next q) flags v ok (.bit (signBit q flags)::out) [] fields d) := by
  cases q <;> simp only [configuration,TM2.step,program,finish,TM2.stepAux,PacketFieldMachine.stackData,
    PacketFieldMachine.update_input,next]

end CircuitRecursion.PacketSerializerMachine
