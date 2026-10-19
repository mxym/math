import EffectiveEncoding.LetterSelectedSerializedRun

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

inductive GrayScanTrace where
  | terminal
  | equal : Bool → GrayScanTrace → GrayScanTrace
  | different : Bool → Bool → GrayScanTrace

structure BooleanGrayScanResult (α : Type*) where
  first : Option α
  others : List α
  trace : GrayScanTrace

/-- A synchronized stored-list scan. At the first different Boolean pair its
 wire is returned and the untouched wire tail is shared. Equal-prefix wires
 are retained in order. Neither Nat/indexed lookup nor wire equality chooses
 the executed branch. Missing-input cases are explicit but unreachable for
 the paired maps used by the actual packed-vector wrapper. -/
def booleanGrayScanProgram {α : Type*} : List α → List Bool → List Bool → BooleanGrayScanResult α
  | [],_,_ => ⟨none,[],.terminal⟩
  | w::ws,[],_ => ⟨none,w::ws,.terminal⟩
  | w::ws,_::_,[] => ⟨none,w::ws,.terminal⟩
  | w::ws,x::xs,y::ys =>
    if x==y then
      let tail:=booleanGrayScanProgram ws xs ys
      ⟨tail.first,w::tail.others,.equal x tail.trace⟩
    else ⟨some w,ws,.different x y⟩


def GrayScanTrace.actions : GrayScanTrace → ℕ
  | .terminal => 1
  | .equal _ tail => tail.actions+5
  | .different _ _ => 5


theorem booleanGrayScanProgram_actions {α : Type*} (wires : List α) (xs ys : List Bool) :
    (booleanGrayScanProgram wires xs ys).trace.actions≤5*wires.length+1 := by
  induction wires generalizing xs ys with
  | nil => exact le_refl 1
  | cons w ws ih =>
    cases xs with
    | nil => simp [booleanGrayScanProgram,GrayScanTrace.actions]
    | cons x xs =>
      cases ys with
      | nil => simp [booleanGrayScanProgram,GrayScanTrace.actions]
      | cons y ys =>
        have ht:=ih xs ys
        simp only [booleanGrayScanProgram]
        split <;> simp only [GrayScanTrace.actions,List.length_cons] <;> omega


theorem booleanGrayScanProgram_first {α : Type*} (wires : List α) (f g : α → Bool) :
    (booleanGrayScanProgram wires (wires.map f) (wires.map g)).first=
      (wires.filter (fun a => !(f a==g a))).head? := by
  induction wires with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.map_cons,booleanGrayScanProgram,List.filter_cons]
    cases f w <;> cases g w <;> simp_all


theorem booleanGrayScanProgram_first_mem {α : Type*} (wires : List α) (f g : α → Bool)
    (a : α) (ha : (booleanGrayScanProgram wires (wires.map f) (wires.map g)).first=some a) : a∈wires := by
  rw [booleanGrayScanProgram_first] at ha
  cases hf : wires.filter (fun a => !(f a==g a)) with
  | nil => simp [hf] at ha
  | cons b bs =>
    simp only [hf,List.head?_cons,Option.some.injEq] at ha
    subst b
    exact (List.mem_filter.mp (show a∈wires.filter (fun a => !(f a==g a)) by rw [hf];simp)).1


theorem booleanGrayScanProgram_others {α : Type*} [DecidableEq α] (wires : List α) (f g : α → Bool)
    (hnd : wires.Nodup) (a : α)
    (ha : (booleanGrayScanProgram wires (wires.map f) (wires.map g)).first=some a) :
    (booleanGrayScanProgram wires (wires.map f) (wires.map g)).others=wires.erase a := by
  induction wires with
  | nil => simp [booleanGrayScanProgram] at ha
  | cons w ws ih =>
    simp only [List.map_cons,booleanGrayScanProgram] at ha ⊢
    by_cases he : (f w==g w)=true
    · simp only [if_pos he] at ha ⊢
      have hm:=booleanGrayScanProgram_first_mem ws f g a ha
      have hne : w≠a := by intro he;subst w;exact (List.nodup_cons.mp hnd).1 hm
      have ht:=ih (List.nodup_cons.mp hnd).2 ha
      simp [List.erase_cons, hne,Ne.symm hne,ht]
    · simp only [if_neg he] at ha ⊢
      simp_all


theorem booleanGrayScanProgram_none {α : Type*} (wires : List α) (f g : α → Bool) :
    (booleanGrayScanProgram wires (wires.map f) (wires.map g)).first=none ↔
      ∀ a∈wires,f a=g a := by
  rw [booleanGrayScanProgram_first]
  simp

/-- PackedBits is List.Vector; this operation is precisely its existing list
 projection, not a conversion or a fresh per-bit traversal. The projected list
 is retained and a single local projection action is recorded. -/
inductive PackedListProjectionTrace where
  | project

structure PackedListProjectionResult where
  bits : List Bool
  trace : PackedListProjectionTrace


def packedListProjectionProgram {n : ℕ} (x : PackedBits n) : PackedListProjectionResult :=
  ⟨x.1,.project⟩


def PackedListProjectionTrace.actions : PackedListProjectionTrace → ℕ
  | .project => 1


theorem packedListProjectionProgram_bits {n : ℕ} (x : PackedBits n) :
    (packedListProjectionProgram x).bits=x.toList := rfl

structure PackedGrayScanResult (n : ℕ) where
  wires : List (Fin n)
  left : PackedListProjectionResult
  right : PackedListProjectionResult
  scan : BooleanGrayScanResult (Fin n)

/-- Two retained zero-copy list projections and one actual scan. FinRange's
 Nat-based construction/control and Fin payload bit work remain outside the
 scan/projection partial charge; no hidden per-bit conversion is executed. -/
def packedGrayScanProgram {n : ℕ} (x y : PackedBits n) : PackedGrayScanResult n :=
  let wires:=List.finRange n
  let left:=packedListProjectionProgram x
  let right:=packedListProjectionProgram y
  let scan:=booleanGrayScanProgram wires left.bits right.bits
  ⟨wires,left,right,scan⟩


theorem packedGrayScanProgram_first {n : ℕ} (x y : PackedBits n) :
    (packedGrayScanProgram x y).scan.first=
      ((List.finRange n).filter (fun a => !(unpackBits x a==unpackBits y a))).head? := by
  change (booleanGrayScanProgram (List.finRange n) x.toList y.toList).first=_
  rw [←packedMask_finRange_map x,←packedMask_finRange_map y,booleanGrayScanProgram_first]


def PackedGrayScanResult.actions {n : ℕ} (r : PackedGrayScanResult n) : ℕ :=
  r.left.trace.actions+r.right.trace.actions+r.scan.trace.actions


theorem packedGrayScanProgram_actions {n : ℕ} (x y : PackedBits n) :
    (packedGrayScanProgram x y).actions≤5*n+3 := by
  have h:=booleanGrayScanProgram_actions (List.finRange n) x.toList y.toList
  simp only [List.length_finRange] at h
  change 1+1+(booleanGrayScanProgram (List.finRange n) x.toList y.toList).trace.actions≤_
  omega

end EffectiveEncoding
