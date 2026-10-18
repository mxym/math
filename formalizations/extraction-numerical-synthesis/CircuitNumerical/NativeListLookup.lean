import CircuitNumerical.NativeSynthesisPolynomial

namespace CircuitRecursion

inductive NativeListLookupTrace where
  | empty
  | hit
  | step : NativeListLookupTrace → NativeListLookupTrace

structure NativeListLookupResult (α : Type*) where
  value : Option α
  trace : NativeListLookupTrace

/-- An actual list-spine lookup. Each recursive result is stored once.
The index is consumed by zero/successor matching; no host indexed read or
comparison on the input data is used. -/
def nativeListLookup {α : Type*} : List α → ℕ → NativeListLookupResult α
  | [],_ => ⟨none,.empty⟩
  | a::_,0 => ⟨some a,.hit⟩
  | _::as,q+1 =>
    let previous:=nativeListLookup as q
    ⟨previous.value,.step previous.trace⟩

def NativeListLookupTrace.nodes : NativeListLookupTrace → ℕ
  | .empty | .hit => 1
  | .step previous => previous.nodes+1

/-- Four local list/option/record model actions at each visited frame.
Precision-index generation and annotation arithmetic are separate. -/
def NativeListLookupTrace.actions : NativeListLookupTrace → ℕ
  | .empty | .hit => 4
  | .step previous => previous.actions+4

theorem nativeListLookup_value {α : Type*} (as : List α) (q : ℕ) :
    (nativeListLookup as q).value=as[q]? := by
  induction as generalizing q with
  | nil => simp only [nativeListLookup,List.getElem?_nil]
  | cons a as ih =>
    cases q with
    | zero => simp only [nativeListLookup,List.getElem?_cons_zero]
    | succ q => simpa only [nativeListLookup,List.getElem?_cons_succ] using ih q

theorem nativeListLookup_nodes {α : Type*} (as : List α) (q : ℕ) :
    (nativeListLookup as q).trace.nodes=min q as.length+1 := by
  induction as generalizing q with
  | nil => simp only [nativeListLookup,NativeListLookupTrace.nodes,List.length_nil,Nat.min_zero]
  | cons a as ih =>
    cases q with
    | zero => simp only [nativeListLookup,NativeListLookupTrace.nodes,Nat.zero_min]
    | succ q =>
      simp only [nativeListLookup,NativeListLookupTrace.nodes,List.length_cons,ih]
      omega

theorem NativeListLookupTrace.actions_eq (trace : NativeListLookupTrace) : trace.actions=4*trace.nodes := by
  induction trace <;> simp_all only [actions,nodes] <;> omega

theorem nativeListLookup_actions {α : Type*} (as : List α) (q : ℕ) :
    (nativeListLookup as q).trace.actions=4*(min q as.length+1) := by
  rw [NativeListLookupTrace.actions_eq,nativeListLookup_nodes]

theorem nativeListLookup_actions_length {α : Type*} (as : List α) (q : ℕ) :
    (nativeListLookup as q).trace.actions≤4*(as.length+1) := by
  rw [nativeListLookup_actions]
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (min_le_right _ _) _)

theorem nativeListLookup_actions_index {α : Type*} (as : List α) (q : ℕ) :
    (nativeListLookup as q).trace.actions≤4*(q+1) := by
  rw [nativeListLookup_actions]
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (min_le_left _ _) _)

theorem nativeListLookup_get {α : Type*} (as : List α) (i : Fin as.length) :
    (nativeListLookup as i.val).value=some (as.get i) := by
  rw [nativeListLookup_value,List.getElem?_eq_getElem i.isLt]
  rfl

end CircuitRecursion
