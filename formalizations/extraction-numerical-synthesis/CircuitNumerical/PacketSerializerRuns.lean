import CircuitNumerical.PacketSerializer

namespace CircuitRecursion.PacketSerializerMachine

open Turing PacketFraming

set_option maxHeartbeats 1500000

theorem clear_iterate (flags : Flags) (v : Option Symbol) (ok : Bool) (out : List Symbol) (s : List Bool)
    (fields : Coordinate → List Bool) (d : List Bool) :
    advance^[s.length+1] (some (configuration (some .clearScratch) flags v ok out s fields d))=
      some (configuration (some .start) flags none ok out [] fields d) := by
  induction s generalizing v with
  | nil => exact clear_nil flags v ok out fields d
  | cons b s ih =>
    rw [List.length_cons,Function.iterate_succ_apply]
    change advance^[s.length+1] (TM2.step program (configuration (some .clearScratch) flags v ok out (b::s) fields d))=_
    rw [clear_cons,ih]

theorem denRead_iterate (flags : Flags) (v : Option Symbol) (ok : Bool) (out : List Symbol) (s : List Bool)
    (fields : Coordinate → List Bool) (d : List Bool) :
    advance^[d.length+1] (some (configuration (some .denRead) flags v ok out s fields d))=
      some (configuration (some .denWrite) flags none ok out (d.reverse++s) fields []) := by
  induction d generalizing v s with
  | nil => exact denRead_nil flags v ok out s fields
  | cons b d ih =>
    rw [List.length_cons,Function.iterate_succ_apply]
    change advance^[d.length+1] (TM2.step program (configuration (some .denRead) flags v ok out s fields (b::d)))=_
    rw [denRead_cons,ih]
    simp only [List.reverse_cons,List.append_assoc,List.cons_append,List.nil_append]

theorem denWrite_iterate (flags : Flags) (v : Option Symbol) (ok : Bool) (out : List Symbol) (s : List Bool)
    (fields : Coordinate → List Bool) (d : List Bool) :
    advance^[s.length+1] (some (configuration (some .denWrite) flags v ok out s fields d))=
      some (configuration (some (.beginNum .n3)) flags none ok (s.reverse.map Symbol.bit++out) [] fields d) := by
  induction s generalizing v out with
  | nil => exact denWrite_nil flags v ok out fields d
  | cons b s ih =>
    rw [List.length_cons,Function.iterate_succ_apply]
    change advance^[s.length+1] (TM2.step program (configuration (some .denWrite) flags v ok out (b::s) fields d))=_
    rw [denWrite_cons,ih]
    simp only [List.reverse_cons,List.map_append,List.map_cons,List.map_nil,List.append_assoc,List.cons_append,List.nil_append]

theorem readNum_iterate_override (q : Coordinate) (data : List Bool) (flags : Flags) (v : Option Symbol) (ok : Bool)
    (out : List Symbol) (s : List Bool) (fields : Coordinate → List Bool) (d : List Bool) :
    advance^[data.length+1]
      (some (configuration (some (.readNum q)) flags v ok out s (Function.update fields q data) d))=
      some (configuration (some (.writeNum q)) flags none ok out (data.reverse++s) (Function.update fields q []) d) := by
  induction data generalizing v s with
  | nil => exact readNum_nil q flags v ok out s fields d
  | cons b data ih =>
    rw [List.length_cons,Function.iterate_succ_apply]
    change advance^[data.length+1] (TM2.step program
      (configuration (some (.readNum q)) flags v ok out s (Function.update fields q (b::data)) d))=_
    rw [readNum_cons,ih]
    simp only [List.reverse_cons,List.append_assoc,List.cons_append,List.nil_append]

theorem writeNum_iterate (q : Coordinate) (flags : Flags) (v : Option Symbol) (ok : Bool)
    (out : List Symbol) (s : List Bool) (fields : Coordinate → List Bool) (d : List Bool) :
    advance^[s.length+1] (some (configuration (some (.writeNum q)) flags v ok out s fields d))=
      some (configuration (some (.finishNum q)) flags none ok (s.reverse.map Symbol.bit++out) [] fields d) := by
  induction s generalizing v out with
  | nil => exact writeNum_nil q flags v ok out fields d
  | cons b s ih =>
    rw [List.length_cons,Function.iterate_succ_apply]
    change advance^[s.length+1] (TM2.step program (configuration (some (.writeNum q)) flags v ok out (b::s) fields d))=_
    rw [writeNum_cons,ih]
    simp only [List.reverse_cons,List.map_append,List.map_cons,List.map_nil,List.append_assoc,List.cons_append,List.nil_append]

theorem denominator_iterate (flags : Flags) (v : Option Symbol) (ok : Bool) (out : List Symbol)
    (fields : Coordinate → List Bool) (d : List Bool) :
    advance^[2*d.length+2] (some (configuration (some .denRead) flags v ok out [] fields d))=
      some (configuration (some (.beginNum .n3)) flags none ok (d.map Symbol.bit++out) [] fields []) := by
  rw [show 2*d.length+2=(d.reverse.length+1)+(d.length+1) by simp;omega,
    Function.iterate_add_apply,denRead_iterate]
  simp only [List.append_nil]
  rw [denWrite_iterate]
  simp only [List.reverse_reverse]

theorem readWriteNum_iterate (q : Coordinate) (data : List Bool) (flags : Flags) (v : Option Symbol) (ok : Bool)
    (out : List Symbol) (fields : Coordinate → List Bool) (d : List Bool) :
    advance^[2*data.length+2]
      (some (configuration (some (.readNum q)) flags v ok out [] (Function.update fields q data) d))=
      some (configuration (some (.finishNum q)) flags none ok (data.map Symbol.bit++out) [] (Function.update fields q []) d) := by
  rw [show 2*data.length+2=(data.reverse.length+1)+(data.length+1) by simp;omega,
    Function.iterate_add_apply,readNum_iterate_override]
  simp only [List.append_nil]
  rw [writeNum_iterate]
  simp only [List.reverse_reverse]

theorem numerator_iterate_override (q : Coordinate) (data : List Bool) (flags : Flags) (v : Option Symbol) (ok : Bool)
    (out : List Symbol) (fields : Coordinate → List Bool) (d : List Bool) :
    advance^[2*data.length+4]
      (some (configuration (some (.beginNum q)) flags v ok out [] (Function.update fields q data) d))=
      some (configuration (next q) flags none ok (signedField ⟨signBit q flags,data⟩++out) [] (Function.update fields q []) d) := by
  rw [show 2*data.length+4=(1+(2*data.length+2))+1 by omega,Function.iterate_succ_apply]
  change advance^[1+(2*data.length+2)]
    (TM2.step program (configuration (some (.beginNum q)) flags v ok out [] (Function.update fields q data) d))=_
  rw [beginNum_step,Function.iterate_add_apply,readWriteNum_iterate]
  change TM2.step program (configuration (some (.finishNum q)) flags none ok
    (data.map Symbol.bit++Symbol.field::out) [] (Function.update fields q []) d)=_
  rw [finishNum_step]
  simp only [signedField,List.cons_append,List.append_assoc,List.singleton_append,List.nil_append]

theorem numerator_iterate (q : Coordinate) (flags : Flags) (v : Option Symbol) (ok : Bool)
    (out : List Symbol) (fields : Coordinate → List Bool) (d : List Bool) :
    advance^[2*(fields q).length+4]
      (some (configuration (some (.beginNum q)) flags v ok out [] fields d))=
      some (configuration (next q) flags none ok (signedField ⟨signBit q flags,fields q⟩++out) [] (Function.update fields q []) d) := by
  simpa only [PacketFieldMachine.fields_update_self] using numerator_iterate_override q (fields q) flags v ok out fields d

end CircuitRecursion.PacketSerializerMachine
