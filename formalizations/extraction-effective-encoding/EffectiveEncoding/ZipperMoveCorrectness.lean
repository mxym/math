import EffectiveEncoding.ZipperMoveProgram

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding


theorem packedZipper_head_value {n : ℕ} (state : PackedBits n) (beforeRev : List Bool)
    (c : Bool) (cs : List Bool) (hs : state.toList=beforeRev.reverse++c::cs)
    (j : Fin n) (hj : j.val=beforeRev.length) : unpackBits state j=c := by
  simp only [unpackBits,List.Vector.get_eq_get_toList,List.get_eq_getElem,Fin.val_cast]
  simp only [hs,hj]
  rw [List.getElem_append_right (as := beforeRev.reverse) (bs := c::cs) (i := beforeRev.length) (by simp)]
  simp only [List.length_reverse,Nat.sub_self,List.getElem_cons_zero]


theorem zipperPreparedMoveProgram_word {n : ℕ} (plans : List (PreparedPauliPlan n)) (x : Bits n)
    (wires : List (Fin n)) (target current beforeRev : List Bool) (seen : Bool)
    (h : beforeRev.length+current.length=n) (state : PackedBits n)
    (ht : target=wires.map x)
    (hc : wires.map Fin.val=List.range' beforeRev.length wires.length)
    (hs : state.toList=beforeRev.reverse++current) :
    (zipperPreparedMoveProgram plans wires target current beforeRev seen h).word=
      skipFirstMoveSpecification plans x wires (unpackBits state) seen := by
  induction wires generalizing target current beforeRev seen state with
  | nil => rfl
  | cons j js ih =>
    have hp : j.val=beforeRev.length ∧ js.map Fin.val=List.range' (beforeRev.length+1) js.length := by
      simpa only [List.map_cons,List.length_cons,List.range'_succ,List.cons.injEq] using hc
    cases target with
    | nil => simp at ht
    | cons b bs =>
      have htarget : b=x j ∧ bs=js.map x := by simpa only [List.map_cons,List.cons.injEq] using ht
      cases current with
      | nil =>
        have hn : beforeRev.length=n := by simpa only [List.length_nil,Nat.add_zero] using h
        have hj:=j.isLt
        omega
      | cons c cs =>
        have hv:=packedZipper_head_value state beforeRev c cs hs j hp.1
        have hlen : (c::beforeRev).length+cs.length=n := by
          have hh:=h;simp only [List.length_cons] at hh ⊢;omega
        have hlen' : (b::beforeRev).length+cs.length=n := by
          have hh:=h;simp only [List.length_cons] at hh ⊢;omega
        have hcursor : js.map Fin.val=List.range' (c::beforeRev).length js.length := by
          simpa only [List.length_cons] using hp.2
        have hcursor' : js.map Fin.val=List.range' (b::beforeRev).length js.length := by
          simpa only [List.length_cons] using hp.2
        have hstate : state.toList=(c::beforeRev).reverse++cs := by
          simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using hs
        by_cases he : b=c
        · subst b
          have hy : unpackBits state j=x j := hv.trans htarget.1
          have hi:=ih bs cs (c::beforeRev) seen hlen state htarget.2 hcursor hstate
          simpa only [zipperPreparedMoveProgram,beq_self_eq_true,ite_true,
            skipFirstMoveSpecification,if_pos hy] using hi
        · have hb : (b==c)=false := by simp [he]
          have hy : unpackBits state j≠x j := by rw [hv,←htarget.1];exact Ne.symm he
          cases seen with
          | false =>
            have hi:=ih bs cs (c::beforeRev) true hlen state htarget.2 hcursor hstate
            simpa only [zipperPreparedMoveProgram,hb,Bool.false_eq_true,ite_false,
              skipFirstMoveSpecification,if_neg hy] using hi
          | true =>
            have ha : (zipperPackedAssemblyProgram beforeRev (c::cs) h).point=state := by
              apply Subtype.ext
              exact (zipperPackedAssemblyProgram_bits beforeRev (c::cs) h).trans hs.symm
            have hu : beforeRev.length+1+cs.length=n := by
              have hh:=h;simp only [List.length_cons] at hh;omega
            let updated:=zipperPackedUpdateProgram beforeRev b cs hu
            have hupdated : updated.point.toList=(b::beforeRev).reverse++cs := by
              simpa only [updated,zipperPackedUpdateProgram_bits,List.reverse_cons,List.append_assoc,
                List.singleton_append]
            have hupdate:=zipperPackedUpdateProgram_unpack state beforeRev c b cs hs hu j hp.1
            have hi:=ih bs cs (b::beforeRev) true hlen' updated.point htarget.2 hcursor' hupdated
            simp only [zipperPreparedMoveProgram,hb,Bool.false_eq_true,ite_false,ite_true,
              skipFirstMoveSpecification,if_neg hy]
            rw [ha,hi]
            change _++skipFirstMoveSpecification plans x js (unpackBits updated.point) true=_
            rw [hupdate,htarget.1]

end EffectiveEncoding
