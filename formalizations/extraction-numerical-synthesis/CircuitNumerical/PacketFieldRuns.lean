import CircuitNumerical.PacketFieldParser

namespace CircuitRecursion.PacketFieldMachine

open Turing PacketFraming

set_option maxHeartbeats 1500000

theorem fields_update_self (fields : Coordinate → List Bool) (q : Coordinate) :
    Function.update fields q (fields q)=fields := by
  funext j
  by_cases hj : j=q
  · subst j;simp only [Function.update_self]
  · simp only [Function.update_of_ne hj]

theorem scan_iterate (q : Coordinate) (bits : List Bool) (flags : Flags) (v : Option Symbol) (ok : Bool)
    (rest : List Symbol) (s : List Bool) (fields : Coordinate → List Bool) (d : List Bool) :
    advance^[bits.length+1]
      (some (configuration (some (.scan q)) flags v ok (bits.map Symbol.bit++Symbol.field::rest) s fields d))=
      some (configuration (some (.restore q)) flags (some .field) ok rest (bits.reverse++s) fields d) := by
  induction bits generalizing v s with
  | nil => exact scan_boundary q flags v ok rest s fields d
  | cons b bits ih =>
    rw [List.length_cons,Function.iterate_succ_apply]
    change advance^[bits.length+1] (TM2.step program
      (configuration (some (.scan q)) flags v ok (.bit b::(bits.map Symbol.bit++Symbol.field::rest)) s fields d))=_
    rw [scan_bit,ih]
    simp only [List.reverse_cons,List.append_assoc,List.cons_append,List.nil_append]

theorem restore_iterate (q : Coordinate) (flags : Flags) (v : Option Symbol) (ok : Bool)
    (rest : List Symbol) (s : List Bool) (fields : Coordinate → List Bool) (d : List Bool) :
    advance^[s.length+1] (some (configuration (some (.restore q)) flags v ok rest s fields d))=
      some (configuration (some (next q)) flags none ok rest []
        (Function.update fields q (s.reverse++fields q)) d) := by
  induction s generalizing v fields with
  | nil =>
    change TM2.step program (configuration (some (.restore q)) flags v ok rest [] fields d)=_
    simpa only [List.reverse_nil,List.nil_append,fields_update_self] using restore_nil q flags v ok rest fields d
  | cons b s ih =>
    rw [List.length_cons,Function.iterate_succ_apply]
    change advance^[s.length+1] (TM2.step program
      (configuration (some (.restore q)) flags v ok rest (b::s) fields d))=_
    rw [restore_cons,ih]
    simp only [Function.update_self,fields_update_twice,List.reverse_cons,List.append_assoc,List.cons_append,List.nil_append]

theorem den_scan_iterate (bits : List Bool) (flags : Flags) (v : Option Symbol) (ok : Bool)
    (rest : List Symbol) (s : List Bool) (fields : Coordinate → List Bool) (d : List Bool) :
    advance^[bits.length+1]
      (some (configuration (some .denScan) flags v ok (bits.map Symbol.bit++Symbol.endPacket::rest) s fields d))=
      some (configuration (some .denRestore) flags (some .endPacket) ok rest (bits.reverse++s) fields d) := by
  induction bits generalizing v s with
  | nil => exact den_end flags v ok rest s fields d
  | cons b bits ih =>
    rw [List.length_cons,Function.iterate_succ_apply]
    change advance^[bits.length+1] (TM2.step program
      (configuration (some .denScan) flags v ok (.bit b::(bits.map Symbol.bit++Symbol.endPacket::rest)) s fields d))=_
    rw [den_bit,ih]
    simp only [List.reverse_cons,List.append_assoc,List.cons_append,List.nil_append]

theorem den_restore_iterate (flags : Flags) (v : Option Symbol) (ok : Bool)
    (rest : List Symbol) (s : List Bool) (fields : Coordinate → List Bool) (d : List Bool) :
    advance^[s.length+1] (some (configuration (some .denRestore) flags v ok rest s fields d))=
      some (configuration none flags none true rest [] fields (s.reverse++d)) := by
  induction s generalizing v d with
  | nil => exact den_restore_nil flags v ok rest fields d
  | cons b s ih =>
    rw [List.length_cons,Function.iterate_succ_apply]
    change advance^[s.length+1] (TM2.step program
      (configuration (some .denRestore) flags v ok rest (b::s) fields d))=_
    rw [den_restore_cons,ih]
    simp only [List.reverse_cons,List.append_assoc,List.cons_append,List.nil_append]

theorem signedField_iterate (q : Coordinate) (a : SignedBinaryWord) (flags : Flags) (v : Option Symbol) (ok : Bool)
    (rest : List Symbol) (fields : Coordinate → List Bool) (d : List Bool) :
    advance^[2*a.bits.length+3]
      (some (configuration (some (.sign q)) flags v ok (signedField a++rest) [] fields d))=
      some (configuration (some (next q)) (setSign q flags a.negative) none ok rest []
        (Function.update fields q (a.bits++fields q)) d) := by
  rw [show 2*a.bits.length+3=((a.bits.reverse.length+1)+(a.bits.length+1))+1 by simp;omega,
    Function.iterate_succ_apply]
  simp only [signedField,List.append_assoc,List.cons_append,List.singleton_append]
  change advance^[(a.bits.reverse.length+1)+(a.bits.length+1)]
    (TM2.step program (configuration (some (.sign q)) flags v ok
      (.bit a.negative::(a.bits.map Symbol.bit++Symbol.field::rest)) [] fields d))=_
  rw [sign_bit,Function.iterate_add_apply,scan_iterate]
  simp only [List.append_nil]
  rw [restore_iterate]
  simp only [List.reverse_reverse]

theorem denominator_iterate (bits : List Bool) (flags : Flags) (v : Option Symbol) (ok : Bool)
    (rest : List Symbol) (fields : Coordinate → List Bool) (d : List Bool) :
    advance^[2*bits.length+2]
      (some (configuration (some .denScan) flags v ok (bits.map Symbol.bit++Symbol.endPacket::rest) [] fields d))=
      some (configuration none flags none true rest [] fields (bits++d)) := by
  rw [show 2*bits.length+2=(bits.reverse.length+1)+(bits.length+1) by simp;omega,
    Function.iterate_add_apply,den_scan_iterate]
  simp only [List.append_nil]
  rw [den_restore_iterate]
  simp only [List.reverse_reverse]

end CircuitRecursion.PacketFieldMachine
