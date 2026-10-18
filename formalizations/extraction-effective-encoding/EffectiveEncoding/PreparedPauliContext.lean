import EffectiveEncoding.NativeBooleanExtraction

open CircuitCompletion CircuitRecursion Matrix
namespace EffectiveEncoding

/-- Finite stored metadata for one Pauli mask, independent of the endpoint and
phase. Both CNOT words and sorted parity coordinates are built once. -/
structure PreparedPauliPlan (n : ℕ) where
  target : Fin n
  leading : WordCode n
  trailing : WordCode n
  parityWires : List (Fin n)
  negateOne : Bool


def preparePauliPlan {n : ℕ} (hn : 0<n) (S : Finset (Fin n)) : PreparedPauliPlan n :=
  let parityWires:=S.sort (·≤·)
  if hS : S.Nonempty then
    let target:=S.min' hS
    let cs:=controls target S
    let leading:=cnotCode target cs
    ⟨target,leading,reverseCode leading,parityWires,true⟩
  else ⟨⟨0,hn⟩,[],[],parityWires,false⟩


def runPreparedPauli {n : ℕ} (plan : PreparedPauliPlan n) (a : AngleCode) : WordCode n :=
  plan.leading++[.single plan.target (.phase a (if plan.negateOne then a.neg else a))]++plan.trailing


def preparedParity {n : ℕ} (plan : PreparedPauliPlan n) (x : Bits n) : Bool :=
  (plan.parityWires.map x).foldr Bool.xor false


theorem runPreparedPauli_eq {n : ℕ} (hn : 0<n) (S : Finset (Fin n)) (a : AngleCode) :
    runPreparedPauli (preparePauliPlan hn S) a=pauliCode hn S a := by
  by_cases h : S.Nonempty <;> simp [preparePauliPlan,runPreparedPauli,pauliCode,parityCode,h]


theorem preparedParity_eq {n : ℕ} (hn : 0<n) (S : Finset (Fin n)) (x : Bits n) :
    preparedParity (preparePauliPlan hn S) x=maskParity S x := by
  by_cases h : S.Nonempty <;> simp [preparePauliPlan,preparedParity,maskParity,h]


def preparedMaskTable {n : ℕ} (hn : 0<n) : List (PreparedPauliPlan n) :=
  (masks n).map (preparePauliPlan hn)

/-- The endpoint-dependent parity fold reads stored coordinates. The half
angle is formed once per call, before traversing the prepared table. -/
def preparedSelectedCode {n : ℕ} (plans : List (PreparedPauliPlan n))
    (x : Bits n) (a : AngleCode) : WordCode n :=
  let reduced:=a.half n
  plans.flatMap (fun plan => runPreparedPauli plan (signedCode reduced (preparedParity plan x)))


theorem preparedSelectedCode_eq {n : ℕ} (hn : 0<n) (x : Bits n) (a : AngleCode) :
    preparedSelectedCode (preparedMaskTable hn) x a=selectedCode hn x a := by
  simp only [preparedSelectedCode,preparedMaskTable,List.flatMap_map,
    preparedParity_eq,runPreparedPauli_eq,selectedCode]


theorem preparedMaskTable_length {n : ℕ} (hn : 0<n) :
    (preparedMaskTable hn).length=2^n := by
  simp only [preparedMaskTable,List.length_map,masks_length]

/-- A storage-cell metric on actual stored lists, plus one target and flag.
This is not a bit-size or constructor runtime metric. -/
def PreparedPauliPlan.payloadCells {n : ℕ} (plan : PreparedPauliPlan n) : ℕ :=
  plan.leading.length+plan.trailing.length+plan.parityWires.length+2


theorem preparePauliPlan_payloadCells {n : ℕ} (hn : 0<n) (S : Finset (Fin n)) :
    (preparePauliPlan hn S).payloadCells≤3*n+2 := by
  have hcard : S.card≤n := (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by simp)
  by_cases h : S.Nonempty
  · have he : (S.erase (S.min' h)).card≤n :=
      (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by simp)
    simp only [preparePauliPlan,dite_eq_left h,PreparedPauliPlan.payloadCells,
      reverseCode,List.length_map,List.length_reverse,cnotCode,controls_length,Finset.length_sort]
    omega
  · simp only [preparePauliPlan,dite_eq_right h,PreparedPauliPlan.payloadCells,
      List.length_nil,Finset.length_sort]
    omega


def preparedMaskTablePayload {n : ℕ} (plans : List (PreparedPauliPlan n)) : ℕ :=
  (plans.map PreparedPauliPlan.payloadCells).sum


theorem preparedMaskTablePayload_bound {n : ℕ} (hn : 0<n) :
    preparedMaskTablePayload (preparedMaskTable hn)≤2^n*(3*n+2) := by
  unfold preparedMaskTablePayload
  calc
    _≤((preparedMaskTable hn).map (fun _ => 3*n+2)).sum := by
      apply List.sum_le_sum
      intro plan hp
      obtain ⟨S,hS,rfl⟩:=List.mem_map.mp hp
      exact preparePauliPlan_payloadCells hn S
    _=_ := by simp [preparedMaskTable_length]

end EffectiveEncoding
