import EffectiveEncoding.BinaryCountRange
import EffectiveEncoding.PreparedPauliContext

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

/-- Semantic bridge only. The actual endpoint program reads/copies stored
Boolean digits; it does not call this Nat test-bit view. -/
theorem endpointBitsProgram_unary_exact (n i : ℕ) :
    (endpointBitsProgram n (unaryWordEncoding i).bits).bits=packBits (fun j => i.testBit j.val) := by
  apply List.Vector.ext
  intro j
  simp only [endpointBitsProgram_get,packBits,List.Vector.get_ofFn]
  rw [←binaryWordValue_testBit_getD,unaryWordEncoding_value]


theorem naturalRange_map_ofFn {α : Type*} (N : ℕ) (f : ℕ → α) :
    (List.range N).map f=List.ofFn (fun i : Fin N => f i.val) := by
  rw [List.ofFn_eq_pmap,List.pmap_eq_map]

structure BinaryMaskPlanResult (n : ℕ) where
  range : BinaryCountRangeResult
  outputs : List (EndpointBitsResult n)
  plans : List (PreparedPauliPlan n)

/-- Actual replacement for Nat.testBit mask enumeration. The inclusive binary
range stores each count encoding once; fixed-width bit-copy/padding runs once
per mask. Those same stored bits feed the existing native finite-set/Pauli-plan
constructors. Nat fuel/pow/index and those constructors' fees remain separate. -/
def binaryMaskPlanProgram {n : ℕ} (hn : 0<n) : BinaryMaskPlanResult n :=
  let range:=binaryCountRangeProgram (2^n-1)
  let outputs:=range.items.map (fun count => endpointBitsProgram n count.encoding.bits)
  let plans:=outputs.map (fun output => preparePauliPlan hn (maskOfBits (unpackBits output.bits)))
  ⟨range,outputs,plans⟩


theorem binaryMaskPlanProgram_outputs {n : ℕ} (hn : 0<n) :
    ((binaryMaskPlanProgram hn).outputs.map EndpointBitsResult.bits)=
      List.ofFn (fun i : Fin (2^n) => packBits (boundedBits n i)) := by
  have hN : 2^n-1+1=2^n := Nat.sub_add_cancel (Nat.one_le_pow _ _ (by decide))
  simp only [binaryMaskPlanProgram,binaryCountRangeProgram_items,List.map_map,Function.comp_def,
    endpointBitsProgram_unary_exact]
  rw [hN,naturalRange_map_ofFn]
  rfl

/-- Exact complete prepared-plan list in the old mask order. No permutation,
choice of representatives or merely matrix-semantic equality is used. -/
theorem binaryMaskPlanProgram_plans {n : ℕ} (hn : 0<n) :
    (binaryMaskPlanProgram hn).plans=preparedMaskTable hn := by
  change ((binaryMaskPlanProgram hn).outputs.map
    (fun output => preparePauliPlan hn (maskOfBits (unpackBits output.bits))))=_
  have h:=congrArg (List.map (fun b => preparePauliPlan hn (maskOfBits (unpackBits b))))
    (binaryMaskPlanProgram_outputs hn)
  simpa only [List.map_map,Function.comp_def,List.map_ofFn,unpackBits_packBits,
    preparedMaskTable,masks] using h


theorem binaryMaskPlanProgram_length {n : ℕ} (hn : 0<n) :
    (binaryMaskPlanProgram hn).outputs.length=2^n := by
  have h:=congrArg List.length (binaryMaskPlanProgram_outputs hn)
  simpa only [List.length_map,List.length_ofFn] using h

/-- The counted bit-copy traces are the results actually stored in outputs.
Generic List.map/finite-set/sort/plan construction is not included here. -/
def BinaryMaskPlanResult.copyActions {n : ℕ} (r : BinaryMaskPlanResult n) : ℕ :=
  (r.outputs.map (fun output => output.trace.listActions)).sum


theorem endpointBitsMap_actions (n : ℕ) (xs : List SavedCountWord) :
    ((xs.map (fun count => endpointBitsProgram n count.encoding.bits)).map
      (fun output => output.trace.listActions)).sum≤xs.length*(3*n+1) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have h:=endpointBitsProgram_listActions n x.encoding.bits
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    exact (Nat.add_le_add h ih).trans_eq (by ring)


theorem binaryMaskPlanProgram_copyActions {n : ℕ} (hn : 0<n) :
    (binaryMaskPlanProgram hn).copyActions≤2^n*(3*n+1) := by
  have h:=endpointBitsMap_actions n (binaryCountRangeProgram (2^n-1)).items
  have hN : 2^n-1+1=2^n := Nat.sub_add_cancel (Nat.one_le_pow _ _ (by decide))
  simpa only [binaryMaskPlanProgram,BinaryMaskPlanResult.copyActions,binaryCountRangeProgram_length,hN] using h


def BinaryMaskPlanResult.actions {n : ℕ} (r : BinaryMaskPlanResult n) : ℕ :=
  r.range.actions+r.copyActions


theorem binaryMaskPlanProgram_actions {n : ℕ} (hn : 0<n) :
    (binaryMaskPlanProgram hn).actions≤40*(2^n)^2+2^n*(3*n+1) := by
  have hN : 2^n-1+1=2^n := Nat.sub_add_cancel (Nat.one_le_pow _ _ (by decide))
  have h:=binaryCountRangeProgram_actions (2^n-1)
  rw [hN] at h
  exact Nat.add_le_add h (binaryMaskPlanProgram_copyActions hn)

/-- The actual binary range/copy model is polynomial at the existing active
width. This does not promote plan payload size into constructor runtime. -/
theorem binaryMaskPlanProgram_active_actions (k : ℕ) :
    (binaryMaskPlanProgram (by omega : 0<2+codeWires k)).actions≤10592*(k+3)^6 := by
  have hd : 2^(2+codeWires k)≤16*(k+3)^3 := by
    rw [nativeActiveWires_eq]
    exact activeDimension_polynomial k
  have hw:=activeWires_log_bound k
  rw [←nativeActiveWires_eq] at hw
  have hc : Nat.clog 2 (k+3)≤k+3 :=
    Nat.clog_le_of_le_pow (Nat.lt_two_pow_self (n:=k+3)).le
  have hf : 3*(2+codeWires k)+1≤22*(k+3) := by omega
  have hp : (k+3)^4≤(k+3)^6 := Nat.pow_le_pow_right (by omega) (by decide)
  calc
    _≤40*(2^(2+codeWires k))^2+2^(2+codeWires k)*(3*(2+codeWires k)+1) := binaryMaskPlanProgram_actions _
    _≤40*(16*(k+3)^3)^2+(16*(k+3)^3)*(22*(k+3)) :=
      Nat.add_le_add (Nat.mul_le_mul_left 40 (Nat.pow_le_pow_left hd 2)) (Nat.mul_le_mul hd hf)
    _=10240*(k+3)^6+352*(k+3)^4 := by ring
    _≤10240*(k+3)^6+352*(k+3)^6 := Nat.add_le_add_left (Nat.mul_le_mul_left 352 hp) _
    _=_ := by ring

end EffectiveEncoding
