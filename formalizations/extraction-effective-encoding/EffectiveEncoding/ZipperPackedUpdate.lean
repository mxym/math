import EffectiveEncoding.ScannedGraySerializedRun

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

structure ZipperPackedUpdateResult (n : ℕ) where
  point : PackedBits n
  assembly : ListAssemblyResult Bool

/-- Rebuild the actual stored state by a retained Boolean reverse/cons program.
 The prefix is already stored in reverse order by the forward zipper. No Nat
 index, List.set, indexed get or Function.update is evaluated by this program.
 The length proof and output-vector proof are erased. -/
def zipperPackedUpdateProgram {n : ℕ} (beforeRev : List Bool) (bit : Bool) (after : List Bool)
    (h : beforeRev.length+1+after.length=n) : ZipperPackedUpdateResult n :=
  let assembly:=listReverseMapIntoProgram id beforeRev (bit::after)
  ⟨⟨assembly.value,by
    change (listReverseMapIntoProgram id beforeRev (bit::after)).value.length=n
    simp only [listReverseMapIntoProgram_value,List.length_append,List.length_reverse,List.length_map,List.length_cons]
    omega⟩,assembly⟩


theorem zipperPackedUpdateProgram_bits {n : ℕ} (beforeRev : List Bool) (bit : Bool) (after : List Bool)
    (h : beforeRev.length+1+after.length=n) :
    (zipperPackedUpdateProgram beforeRev bit after h).point.toList=beforeRev.reverse++bit::after := by
  simp only [zipperPackedUpdateProgram,List.Vector.toList_mk,listReverseMapIntoProgram_value,List.map_id]


theorem zipperPackedUpdateProgram_set {n : ℕ} (state : PackedBits n)
    (beforeRev : List Bool) (old bit : Bool) (after : List Bool)
    (hs : state.toList=beforeRev.reverse++old::after)
    (h : beforeRev.length+1+after.length=n) (i : Fin n) (hi : i.val=beforeRev.length) :
    (zipperPackedUpdateProgram beforeRev bit after h).point=state.set i bit := by
  apply Subtype.ext
  change (zipperPackedUpdateProgram beforeRev bit after h).point.toList=(state.set i bit).toList
  rw [zipperPackedUpdateProgram_bits,List.Vector.toList_set,hs,hi]
  have he:=List.set_append_right (s := beforeRev.reverse) (t := old::after) beforeRev.length bit (by simp)
  simpa only [List.length_reverse,Nat.sub_self,List.set_cons_zero] using he.symm

/-- Exact old function-state semantics, used only in correctness proofs. The
 update program above never executes the semantic indexed function update. -/
theorem zipperPackedUpdateProgram_unpack {n : ℕ} (state : PackedBits n)
    (beforeRev : List Bool) (old bit : Bool) (after : List Bool)
    (hs : state.toList=beforeRev.reverse++old::after)
    (h : beforeRev.length+1+after.length=n) (i : Fin n) (hi : i.val=beforeRev.length) :
    unpackBits (zipperPackedUpdateProgram beforeRev bit after h).point=
      Function.update (unpackBits state) i bit := by
  rw [zipperPackedUpdateProgram_set state beforeRev old bit after hs h i hi]
  funext j
  change (state.set i bit).get j=_
  rw [List.Vector.get_set_eq_if]
  by_cases hij : i=j
  · subst j;simp
  · simp [hij,Function.update_of_ne (Ne.symm hij),unpackBits]


def ZipperPackedUpdateResult.actions {n : ℕ} (r : ZipperPackedUpdateResult n) : ℕ :=
  r.assembly.trace.actions


theorem zipperPackedUpdateProgram_actions {n : ℕ} (beforeRev : List Bool) (bit : Bool) (after : List Bool)
    (h : beforeRev.length+1+after.length=n) :
    (zipperPackedUpdateProgram beforeRev bit after h).actions=4*beforeRev.length+1 := by
  exact listReverseMapIntoProgram_actions _ _ _

end EffectiveEncoding
