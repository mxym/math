import CircuitNumerical.FiniteBinaryCounterTerminal

namespace CircuitRecursion

structure BinaryIndex where
  bits : List Bool
  canonical : BinaryWordCanonical bits

/-- Specification only; the lookup value program never calls this decode. -/
def BinaryIndex.value (i : BinaryIndex) : ℕ := binaryWordValue i.bits

def BinaryIndex.predecessor (i : BinaryIndex) : BinaryIndex :=
  ⟨binaryPredecessorBits i.bits,binaryPredecessorBits_canonical i.bits i.canonical⟩

theorem BinaryIndex.predecessor_value (i : BinaryIndex) : i.predecessor.value=i.value-1 :=
  binaryPredecessorBits_value i.bits i.canonical

theorem BinaryIndex.predecessor_width (i : BinaryIndex) : i.predecessor.bits.length≤ i.bits.length :=
  binaryPredecessorBits_length i.bits i.canonical

theorem BinaryIndex.predecessor_progress (i : BinaryIndex) (hne : i.bits≠[]) :
    i.predecessor.value+1=i.value := by
  have hz : i.value≠0 := by
    intro hzero
    exact hne ((binaryWordCanonical_zero_iff i.bits i.canonical).mp hzero)
  rw [BinaryIndex.predecessor_value]
  omega

inductive BinaryIndexedLookupTrace where
  | empty | hit
  | step : BinaryIndex → BinaryIndexedLookupTrace → BinaryIndexedLookupTrace

structure BinaryIndexedLookupResult (α : Type*) where
  value : Option α
  trace : BinaryIndexedLookupTrace

/-- The actual lookup consumes a represented binary index. It matches list
and Boolean constructors only; no Nat decode, Nat predecessor or host indexed
access occurs in this value program. Each predecessor and recursive result
is stored once. Payload encoding is separate from this generic list driver. -/
def binaryIndexedLookup {α : Type*} : List α → BinaryIndex → BinaryIndexedLookupResult α
  | [],_ => ⟨none,.empty⟩
  | a::as,i =>
    match i.bits with
    | [] => ⟨some a,.hit⟩
    | _::_ =>
      let next:=i.predecessor
      let tail:=binaryIndexedLookup as next
      ⟨tail.value,.step i tail.trace⟩

theorem binaryIndexedLookup_value {α : Type*} (as : List α) (i : BinaryIndex) :
    (binaryIndexedLookup as i).value=(nativeListLookup as i.value).value := by
  induction as generalizing i with
  | nil => rfl
  | cons a as ih =>
    cases hb : i.bits with
    | nil =>
      have hz : i.value=0 := by unfold BinaryIndex.value;rw [hb];rfl
      simp only [binaryIndexedLookup,hb,hz,nativeListLookup]
    | cons b bs =>
      have hp:=i.predecessor_progress (by rw [hb];exact List.cons_ne_nil _ _)
      simp only [binaryIndexedLookup,hb]
      rw [←hp]
      simpa only [nativeListLookup] using ih i.predecessor

theorem binaryIndexedLookup_getElem {α : Type*} (as : List α) (i : BinaryIndex) :
    (binaryIndexedLookup as i).value=as[i.value]? := by
  rw [binaryIndexedLookup_value,nativeListLookup_value]

/-- Sum of the exact official TM2 counter runs for the predecessor calls
retained by this trace. This excludes the outer lookup loop/payload encoding
and annotation arithmetic; it is not total lookup machine runtime. -/
def BinaryIndexedLookupTrace.counterTransitions : BinaryIndexedLookupTrace → ℕ
  | .empty | .hit => 0
  | .step i tail => (BinaryCounterMachine.counterRun i.bits i.canonical []).steps+tail.counterTransitions

def BinaryIndexedLookupTrace.counterCalls : BinaryIndexedLookupTrace → ℕ
  | .empty | .hit => 0
  | .step _ tail => tail.counterCalls+1

theorem binaryIndexedLookup_counterTransitions {α : Type*} (as : List α) (i : BinaryIndex) :
    (binaryIndexedLookup as i).trace.counterTransitions≤(2*i.bits.length+2)*as.length := by
  induction as generalizing i with
  | nil => exact Nat.zero_le _
  | cons a as ih =>
    cases hb : i.bits with
    | nil => simp only [binaryIndexedLookup,hb,BinaryIndexedLookupTrace.counterTransitions,Nat.zero_le]
    | cons b bs =>
      have hs:=BinaryCounterMachine.counterRun_steps_bound i.bits i.canonical []
      have hw:=i.predecessor_width
      have hi:=ih i.predecessor
      have hm:=Nat.mul_le_mul_right as.length (show 2*i.predecessor.bits.length+2≤2*i.bits.length+2 by omega)
      have htail:=hi.trans hm
      simp only [binaryIndexedLookup,hb,BinaryIndexedLookupTrace.counterTransitions]
      rw [List.length_cons,Nat.mul_add,Nat.mul_one]
      simp only [hb,List.length_cons] at hs htail ⊢
      simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one] at htail ⊢
      omega

theorem binaryIndexedLookup_counterCalls {α : Type*} (as : List α) (i : BinaryIndex) :
    (binaryIndexedLookup as i).trace.counterCalls≤as.length := by
  induction as generalizing i with
  | nil => exact le_refl 0
  | cons a as ih =>
    cases hb : i.bits with
    | nil => simp only [binaryIndexedLookup,hb,BinaryIndexedLookupTrace.counterCalls,Nat.zero_le]
    | cons b bs => simpa only [binaryIndexedLookup,hb,BinaryIndexedLookupTrace.counterCalls,List.length_cons] using
        Nat.add_le_add_right (ih i.predecessor) 1

end CircuitRecursion
