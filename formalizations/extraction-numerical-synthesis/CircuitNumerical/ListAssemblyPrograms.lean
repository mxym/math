import CircuitNumerical.InputNumericalSynthesis

namespace CircuitRecursion

/-- Control trace of concrete list-spine copies. Sequence nodes retain the
traces of calls already executed; annotations themselves are not charged. -/
inductive ListAssemblyTrace where
  | done
  | copy : ListAssemblyTrace → ListAssemblyTrace
  | sequence : ListAssemblyTrace → ListAssemblyTrace → ListAssemblyTrace

def ListAssemblyTrace.actions : ListAssemblyTrace → ℕ
  | .done => 1
  | .copy t => t.actions+4
  | .sequence a b => a.actions+b.actions

def ListAssemblyTrace.copies : ListAssemblyTrace → ℕ
  | .done => 0
  | .copy t => t.copies+1
  | .sequence a b => a.copies+b.copies

theorem ListAssemblyTrace.copies_le_actions (t : ListAssemblyTrace) : t.copies≤t.actions := by
  induction t with
  | done => decide
  | copy t ih => simp only [ListAssemblyTrace.copies,ListAssemblyTrace.actions];omega
  | sequence a b ia ib => exact Nat.add_le_add ia ib

structure ListAssemblyResult (α : Type*) where
  value : List α
  trace : ListAssemblyTrace

/-- The tail result is stored once. A copy step charges its concrete spine
case/cons operations; accessing a list element is not re-evaluation of it. -/
def listAppendProgram {α : Type*} : List α → List α → ListAssemblyResult α
  | [],bs => ⟨bs,.done⟩
  | a::as,bs =>
    let tail:=listAppendProgram as bs
    ⟨a::tail.value,.copy tail.trace⟩

theorem listAppendProgram_value {α : Type*} (as bs : List α) :
    (listAppendProgram as bs).value=as++bs := by
  induction as with
  | nil => rfl
  | cons a as ih => simpa only [listAppendProgram,List.cons_append] using congrArg (List.cons a) ih

theorem listAppendProgram_actions {α : Type*} (as bs : List α) :
    (listAppendProgram as bs).trace.actions=4*as.length+1 := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [listAppendProgram,ListAssemblyTrace.actions,List.length_cons]
    omega

theorem listAppendProgram_copies {α : Type*} (as bs : List α) :
    (listAppendProgram as bs).trace.copies=as.length := by
  induction as with
  | nil => rfl
  | cons a as ih => simpa only [listAppendProgram,ListAssemblyTrace.copies,List.length_cons] using congrArg Nat.succ ih

/-- One pass computes reverse-map into a supplied accumulator. Each step
calls f exactly once, separately from the charged list-spine operations. -/
def listReverseMapIntoProgram {α β : Type*} (f : α → β) : List α → List β → ListAssemblyResult β
  | [],acc => ⟨acc,.done⟩
  | a::as,acc =>
    let tail:=listReverseMapIntoProgram f as (f a::acc)
    ⟨tail.value,.copy tail.trace⟩

theorem listReverseMapIntoProgram_value {α β : Type*} (f : α → β) (as : List α) (acc : List β) :
    (listReverseMapIntoProgram f as acc).value=as.reverse.map f++acc := by
  induction as generalizing acc with
  | nil => rfl
  | cons a as ih =>
    simp only [listReverseMapIntoProgram,ih,List.reverse_cons,List.map_append,List.map_cons,List.map_nil,
      List.append_assoc,List.cons_append,List.nil_append]

theorem listReverseMapIntoProgram_actions {α β : Type*} (f : α → β) (as : List α) (acc : List β) :
    (listReverseMapIntoProgram f as acc).trace.actions=4*as.length+1 := by
  induction as generalizing acc with
  | nil => rfl
  | cons a as ih =>
    simp only [listReverseMapIntoProgram,ListAssemblyTrace.actions,ih,List.length_cons]
    omega

theorem listReverseMapIntoProgram_copies {α β : Type*} (f : α → β) (as : List α) (acc : List β) :
    (listReverseMapIntoProgram f as acc).trace.copies=as.length := by
  induction as generalizing acc with
  | nil => rfl
  | cons a as ih =>
    simp only [listReverseMapIntoProgram,ListAssemblyTrace.copies,ih,List.length_cons]

def listAppendFourProgram {α : Type*} (a b c d : List α) : ListAssemblyResult α :=
  let ab:=listAppendProgram a b
  let abc:=listAppendProgram ab.value c
  let abcd:=listAppendProgram abc.value d
  ⟨abcd.value,.sequence (.sequence ab.trace abc.trace) abcd.trace⟩

theorem listAppendFourProgram_value {α : Type*} (a b c d : List α) :
    (listAppendFourProgram a b c d).value=a++b++c++d := by
  simp only [listAppendFourProgram,listAppendProgram_value]

theorem listAppendFourProgram_actions_exact {α : Type*} (a b c d : List α) :
    (listAppendFourProgram a b c d).trace.actions=12*a.length+8*b.length+4*c.length+3 := by
  simp only [listAppendFourProgram,ListAssemblyTrace.actions,listAppendProgram_actions,
    listAppendProgram_value,List.length_append]
  omega

theorem listAppendFourProgram_actions {α : Type*} (a b c d : List α) :
    (listAppendFourProgram a b c d).trace.actions≤12*(a.length+b.length+c.length+d.length+1) := by
  simp only [listAppendFourProgram,ListAssemblyTrace.actions,listAppendProgram_actions,
    listAppendProgram_value,List.length_append]
  omega

/-- Inversion calls inverseLabel once per copied instruction. Its lookup or
provider cost is deliberately separate from this concrete list-spine fee. -/
def instructionInverseProgram {m : ℕ} (inverseLabel : Fin m → Fin m) (word : List (Fin m)) : ListAssemblyResult (Fin m) :=
  listReverseMapIntoProgram inverseLabel word []

theorem instructionInverseProgram_value {m : ℕ} (inverseLabel : Fin m → Fin m) (word : List (Fin m)) :
    (instructionInverseProgram inverseLabel word).value=instructionInverse inverseLabel word := by
  simp only [instructionInverseProgram,listReverseMapIntoProgram_value,List.append_nil,instructionInverse]

theorem instructionInverseProgram_actions {m : ℕ} (inverseLabel : Fin m → Fin m) (word : List (Fin m)) :
    (instructionInverseProgram inverseLabel word).trace.actions=4*word.length+1 :=
  listReverseMapIntoProgram_actions inverseLabel word []

theorem instructionInverseProgram_calls {m : ℕ} (inverseLabel : Fin m → Fin m) (word : List (Fin m)) :
    (instructionInverseProgram inverseLabel word).trace.copies=word.length :=
  listReverseMapIntoProgram_copies inverseLabel word []

end CircuitRecursion
