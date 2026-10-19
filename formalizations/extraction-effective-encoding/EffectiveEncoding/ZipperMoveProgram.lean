import EffectiveEncoding.SkipFirstMoveSpecification

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

/-- Actual final/adjacent-state reconstruction, sharing the untouched suffix.
 Its reversed prefix is traversed by the existing concrete list program. -/
def zipperPackedAssemblyProgram {n : ℕ} (beforeRev after : List Bool)
    (h : beforeRev.length+after.length=n) : ZipperPackedUpdateResult n :=
  let assembly:=listReverseMapIntoProgram id beforeRev after
  ⟨⟨assembly.value,by
    change (listReverseMapIntoProgram id beforeRev after).value.length=n
    simpa only [listReverseMapIntoProgram_value,List.length_append,List.length_reverse,List.length_map] using h⟩,assembly⟩


theorem zipperPackedAssemblyProgram_bits {n : ℕ} (beforeRev after : List Bool)
    (h : beforeRev.length+after.length=n) :
    (zipperPackedAssemblyProgram beforeRev after h).point.toList=beforeRev.reverse++after := by
  simp only [zipperPackedAssemblyProgram,List.Vector.toList_mk,listReverseMapIntoProgram_value,List.map_id]


theorem zipperPackedAssemblyProgram_actions {n : ℕ} (beforeRev after : List Bool)
    (h : beforeRev.length+after.length=n) :
    (zipperPackedAssemblyProgram beforeRev after h).actions=4*beforeRev.length+1 :=
  listReverseMapIntoProgram_actions _ _ _

inductive ZipperMoveTrace where
  | terminal
  | equal : Bool → ZipperMoveTrace → ZipperMoveTrace
  | pivot : Bool → Bool → ZipperMoveTrace → ZipperMoveTrace
  | moved : Bool → Bool → ZipperMoveTrace → ZipperMoveTrace


def ZipperMoveTrace.actions : ZipperMoveTrace → ℕ
  | .terminal => 1
  | .equal _ tail => tail.actions+4
  | .pivot _ _ tail => tail.actions+5
  | .moved _ _ tail => tail.actions+5

structure ZipperMoveResult (n : ℕ) where
  word : WordCode n
  final : PackedBits n
  assemblies : List (ZipperPackedUpdateResult n)
  trace : ZipperMoveTrace


def finishZipperMoveProgram {n : ℕ} (beforeRev current : List Bool)
    (h : beforeRev.length+current.length=n) : ZipperMoveResult n :=
  let assembled:=zipperPackedAssemblyProgram beforeRev current h
  ⟨[],assembled.point,[assembled],.terminal⟩

/-- Real parallel Bool-list control. Updating a coordinate is one cons onto
 the stored reversed prefix. No indexed input read, wire equality or function
 update runs here. A full state is reconstructed only when the adjacent-word
 program needs it, and once at the end; both actual assemblies are retained.
 Adjacent selected-phase evaluation and its AST construction retain their
 separate cost boundary. -/
def zipperPreparedMoveProgram {n : ℕ} (plans : List (PreparedPauliPlan n)) :
    (wires : List (Fin n)) → (target current beforeRev : List Bool) → Bool →
    (beforeRev.length+current.length=n) → ZipperMoveResult n
  | [],_,current,beforeRev,_,h => finishZipperMoveProgram beforeRev current h
  | _::_,[],current,beforeRev,_,h => finishZipperMoveProgram beforeRev current h
  | _::_,_::_,[],beforeRev,_,h => finishZipperMoveProgram beforeRev [] h
  | j::js,b::bs,c::cs,beforeRev,seen,h =>
    if b==c then
      let tail:=zipperPreparedMoveProgram plans js bs cs (c::beforeRev) seen (by have hh:=h; simp only [List.length_cons] at hh ⊢; omega)
      ⟨tail.word,tail.final,tail.assemblies,.equal c tail.trace⟩
    else if seen then
      let assembled:=zipperPackedAssemblyProgram beforeRev (c::cs) h
      let adjacent:=preparedAdjacentSwapCode plans j (unpackBits assembled.point)
      let tail:=zipperPreparedMoveProgram plans js bs cs (b::beforeRev) true (by have hh:=h; simp only [List.length_cons] at hh ⊢; omega)
      ⟨adjacent++tail.word,tail.final,assembled::tail.assemblies,.moved b c tail.trace⟩
    else
      let tail:=zipperPreparedMoveProgram plans js bs cs (c::beforeRev) true (by have hh:=h; simp only [List.length_cons] at hh ⊢; omega)
      ⟨tail.word,tail.final,tail.assemblies,.pivot b c tail.trace⟩

/-- Only the actual loop's finite Bool/list branches and executed state
 assembly records. This excludes adjacent AST/parity and host/control costs. -/
def ZipperMoveResult.actions {n : ℕ} (r : ZipperMoveResult n) : ℕ :=
  r.trace.actions+(r.assemblies.map ZipperPackedUpdateResult.actions).sum


theorem finishZipperMoveProgram_actions {n : ℕ} (beforeRev current : List Bool)
    (h : beforeRev.length+current.length=n) :
    (finishZipperMoveProgram beforeRev current h).actions≤4*n+2 := by
  dsimp only [finishZipperMoveProgram,ZipperMoveResult.actions]
  simp only [ZipperMoveTrace.actions,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    zipperPackedAssemblyProgram_actions]
  omega


theorem zipperPreparedMoveProgram_actions {n : ℕ} (plans : List (PreparedPauliPlan n))
    (wires : List (Fin n)) (target current beforeRev : List Bool) (seen : Bool)
    (h : beforeRev.length+current.length=n) :
    (zipperPreparedMoveProgram plans wires target current beforeRev seen h).actions≤
      (4*n+6)*(wires.length+1) := by
  induction wires generalizing target current beforeRev seen with
  | nil => exact (finishZipperMoveProgram_actions beforeRev current h).trans (by simp only [List.length_nil,Nat.zero_add,Nat.mul_one]; omega)
  | cons j js ih =>
    cases target with
    | nil => exact (finishZipperMoveProgram_actions beforeRev current h).trans (by simp only [List.length_cons]; nlinarith)
    | cons b bs =>
      cases current with
      | nil => exact (finishZipperMoveProgram_actions beforeRev [] h).trans (by simp only [List.length_cons]; nlinarith)
      | cons c cs =>
        have hl : (c::beforeRev).length+cs.length=n := by have hh:=h; simp only [List.length_cons] at hh ⊢; omega
        have hl' : (b::beforeRev).length+cs.length=n := by have hh:=h; simp only [List.length_cons] at hh ⊢; omega
        by_cases he : (b==c)=true
        · have ht:=ih bs cs (c::beforeRev) seen hl
          simp only [Nat.mul_add,Nat.mul_one] at ht
          unfold ZipperMoveResult.actions at ht ⊢
          simp only [zipperPreparedMoveProgram,if_pos he,ZipperMoveTrace.actions,List.length_cons,
            Nat.mul_add,Nat.mul_one]
          omega
        · cases seen with
          | false =>
            have ht:=ih bs cs (c::beforeRev) true hl
            simp only [Nat.mul_add,Nat.mul_one] at ht
            unfold ZipperMoveResult.actions at ht ⊢
            simp only [zipperPreparedMoveProgram,if_neg he,Bool.false_eq_true,ite_false,
              ZipperMoveTrace.actions,List.length_cons,Nat.mul_add,Nat.mul_one]
            omega
          | true =>
            have ht:=ih bs cs (b::beforeRev) true hl'
            have ha:=zipperPackedAssemblyProgram_actions beforeRev (c::cs) h
            simp only [Nat.mul_add,Nat.mul_one] at ht
            unfold ZipperMoveResult.actions at ht ⊢
            simp only [zipperPreparedMoveProgram,if_neg he,ite_true,ZipperMoveTrace.actions,
              List.map_cons,List.sum_cons,List.length_cons,Nat.mul_add,Nat.mul_one]
            simp only [List.length_cons] at h
            omega

end EffectiveEncoding
