import CircuitNumerical.PacketFrameMachines

namespace CircuitRecursion.PacketFrameMachine

open Turing ListAssemblyMachine PacketFraming

set_option maxHeartbeats 1500000

theorem skipFrame_iterate (data : List Symbol) (h : Symbol.endPacket∉data)
    (v : Option Symbol) (rest output work : List Symbol) :
    skipAdvance^[data.length+1]
      (some (skipConfiguration (some ()) v (data++Symbol.endPacket::rest) output work))=
      some (skipConfiguration none (some .endPacket) rest output work) := by
  induction data generalizing v with
  | nil => exact skip_end v rest output work
  | cons a data ih =>
    have ha : a≠.endPacket := by intro he;apply h;rw [he];exact List.mem_cons_self
    have ht : Symbol.endPacket∉data := fun hm => h (List.mem_cons_of_mem a hm)
    rw [List.length_cons,Function.iterate_succ_apply]
    change skipAdvance^[data.length+1]
      (TM2.step skipProgram (skipConfiguration (some ()) v (a::(data++Symbol.endPacket::rest)) output work))=_
    rw [skip_payload v a ha,ih ht]

theorem copyScan_iterate (data : List Symbol) (h : Symbol.endPacket∉data)
    (v : Option Symbol) (rest output work : List Symbol) :
    copyAdvance^[data.length+1]
      (some (copyConfiguration (some .scan) v (data++Symbol.endPacket::rest) output work))=
      some (copyConfiguration (some .restore) (some .endPacket) rest output (.endPacket::(data.reverse++work))) := by
  induction data generalizing v work with
  | nil => exact copy_end v rest output work
  | cons a data ih =>
    have ha : a≠.endPacket := by intro he;apply h;rw [he];exact List.mem_cons_self
    have ht : Symbol.endPacket∉data := fun hm => h (List.mem_cons_of_mem a hm)
    rw [List.length_cons,Function.iterate_succ_apply]
    change copyAdvance^[data.length+1]
      (TM2.step copyProgram (copyConfiguration (some .scan) v (a::(data++Symbol.endPacket::rest)) output work))=_
    rw [copy_payload v a ha,ih ht]
    simp only [List.reverse_cons,List.append_assoc,List.cons_append,List.nil_append]

theorem copyRestore_iterate (v : Option Symbol) (input output work : List Symbol) :
    copyAdvance^[work.length+1] (some (copyConfiguration (some .restore) v input output work))=
      some (copyConfiguration none none input (work.reverse++output) []) := by
  induction work generalizing v output with
  | nil => exact copy_restore_nil v input output
  | cons a work ih =>
    rw [List.length_cons,Function.iterate_succ_apply]
    change copyAdvance^[work.length+1]
      (TM2.step copyProgram (copyConfiguration (some .restore) v input output (a::work)))=_
    rw [copy_restore_cons,ih]
    simp only [List.reverse_cons,List.append_assoc,List.cons_append,List.nil_append]

theorem copyFrame_iterate (data : List Symbol) (h : Symbol.endPacket∉data)
    (rest output : List Symbol) :
    copyAdvance^[2*data.length+3]
      (some (copyConfiguration (some .scan) none (data++Symbol.endPacket::rest) output []))=
      some (copyConfiguration none none rest ((data++[.endPacket])++output) []) := by
  let work:=Symbol.endPacket::data.reverse
  have hn : 2*data.length+3=(work.length+1)+(data.length+1) := by
    simp only [work,List.length_cons,List.length_reverse]
    omega
  rw [hn,Function.iterate_add_apply,copyScan_iterate data h]
  simp only [List.append_nil]
  change copyAdvance^[work.length+1] (some (copyConfiguration (some .restore) (some .endPacket) rest output work))=_
  rw [copyRestore_iterate]
  simp only [work,List.reverse_cons,List.reverse_reverse]

/-- Actual packet-boundary scan. Data/field syntax supplies the no-internal-
terminator invariant internally; lengths are only external time indices. -/
def skipPacketRun (p : WordIntegerPacket) (rest output work : List Symbol) :
    StateTransition.EvalsToInTime (TM2.step skipProgram)
      (skipConfiguration (some ()) none (encodePacket p++rest) output work)
      (some (skipConfiguration none (some .endPacket) rest output work)) (encodePacket p).length :=
  ⟨⟨(payload (rawPacket p)).length+1,by
    change skipAdvance^[(payload (rawPacket p)).length+1]
      (some (skipConfiguration (some ()) none (encodePacket p++rest) output work))=_
    simpa only [encodePacket,encodeRaw,List.append_assoc,List.singleton_append] using
      skipFrame_iterate (payload (rawPacket p)) (payload_no_end _) none rest output work⟩,by
    simp only [encodePacket,encodeRaw,List.length_append,List.length_cons,List.length_nil]
    omega⟩

def copyPacketRun (p : WordIntegerPacket) (rest output : List Symbol) :
    StateTransition.EvalsToInTime (TM2.step copyProgram)
      (copyConfiguration (some .scan) none (encodePacket p++rest) output [])
      (some (copyConfiguration none none rest (encodePacket p++output) [])) (2*(encodePacket p).length+1) :=
  ⟨⟨2*(payload (rawPacket p)).length+3,by
    change copyAdvance^[2*(payload (rawPacket p)).length+3]
      (some (copyConfiguration (some .scan) none (encodePacket p++rest) output []))=_
    simpa only [encodePacket,encodeRaw,List.append_assoc,List.singleton_append] using
      copyFrame_iterate (payload (rawPacket p)) (payload_no_end _) rest output⟩,by
    simp only [encodePacket,encodeRaw,List.length_append,List.length_cons,List.length_nil]
    omega⟩

theorem skipPacketRun_steps (p : WordIntegerPacket) (rest output work : List Symbol) :
    (skipPacketRun p rest output work).steps=(encodePacket p).length := by
  simp only [skipPacketRun,encodePacket,encodeRaw,List.length_append,List.length_cons,List.length_nil]

theorem copyPacketRun_steps (p : WordIntegerPacket) (rest output : List Symbol) :
    (copyPacketRun p rest output).steps=2*(encodePacket p).length+1 := by
  simp only [copyPacketRun,encodePacket,encodeRaw,List.length_append,List.length_cons,List.length_nil]
  omega

theorem skipPacket_mem_eval (p : WordIntegerPacket) (rest output work : List Symbol) :
    skipConfiguration none (some .endPacket) rest output work∈StateTransition.eval (TM2.step skipProgram)
      (skipConfiguration (some ()) none (encodePacket p++rest) output work) :=
  evalsTo_terminal_mem_eval (skipPacketRun p rest output work).toEvalsTo (skip_halt _ _ _ _)

theorem copyPacket_mem_eval (p : WordIntegerPacket) (rest output : List Symbol) :
    copyConfiguration none none rest (encodePacket p++output) []∈StateTransition.eval (TM2.step copyProgram)
      (copyConfiguration (some .scan) none (encodePacket p++rest) output []) :=
  evalsTo_terminal_mem_eval (copyPacketRun p rest output).toEvalsTo (copy_halt _ _ _ _)

theorem skipCache_head_mem_eval (p : WordIntegerPacket) (ps : List WordIntegerPacket) (output work : List Symbol) :
    skipConfiguration none (some .endPacket) (encodeCache ps) output work∈StateTransition.eval (TM2.step skipProgram)
      (skipConfiguration (some ()) none (encodeCache (p::ps)) output work) := skipPacket_mem_eval p _ _ _

theorem copyCache_head_mem_eval (p : WordIntegerPacket) (ps : List WordIntegerPacket) (output : List Symbol) :
    copyConfiguration none none (encodeCache ps) (encodePacket p++output) []∈StateTransition.eval (TM2.step copyProgram)
      (copyConfiguration (some .scan) none (encodeCache (p::ps)) output []) := copyPacket_mem_eval p _ _

theorem copied_output_decode (p : WordIntegerPacket) (rest output : List Symbol) :
    decodeRaw ((copyConfiguration none none rest (encodePacket p++output) []).stk .right)=some (rawPacket p,output) :=
  decodeRaw_encodePacket p output

theorem skipPacketRun_steps_height (p : WordIntegerPacket) (rest output work : List Symbol) (B : ℕ)
    (h : IntegerPacketHeight p.decode B) : (skipPacketRun p rest output work).steps≤5*B+14 := by
  rw [skipPacketRun_steps]
  exact encodePacket_length_height p B h

theorem copyPacketRun_steps_height (p : WordIntegerPacket) (rest output : List Symbol) (B : ℕ)
    (h : IntegerPacketHeight p.decode B) : (copyPacketRun p rest output).steps≤10*B+29 := by
  rw [copyPacketRun_steps]
  have hp:=encodePacket_length_height p B h
  omega

end CircuitRecursion.PacketFrameMachine
