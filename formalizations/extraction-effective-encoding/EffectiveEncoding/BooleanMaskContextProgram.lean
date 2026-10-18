import EffectiveEncoding.BooleanPauliPlanProgram

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

structure BooleanMaskContextResult (n : ℕ) where
  common : BinaryMaskPlanResult n
  planTable : BooleanPlanTableResult n

/-- One actual saved binary range and fixed-width output list feed one real
Bool/list Pauli-plan table builder. No legacy finite-set/sort/minimum/erase plan
constructor is executed to fill the common compatibility data. -/
def booleanMaskContextProgram {n : ℕ} (hn : 0<n) : BooleanMaskContextResult n :=
  let range:=binaryCountRangeProgram (2^n-1)
  let outputs:=range.items.map (fun count => endpointBitsProgram n count.encoding.bits)
  let plans:=booleanPlanTableProgram hn outputs
  ⟨⟨range,outputs,plans.plans⟩,plans⟩

/-- Exact entire common range/output/plan record, not just semantic equality.
The new plan-construction records remain retained in planTable. -/
theorem booleanMaskContextProgram_common {n : ℕ} (hn : 0<n) :
    (booleanMaskContextProgram hn).common=binaryMaskPlanProgram hn := by
  simp only [booleanMaskContextProgram,booleanPlanTableProgram_plans,binaryMaskPlanProgram]


theorem booleanMaskContextProgram_plans {n : ℕ} (hn : 0<n) :
    (booleanMaskContextProgram hn).common.plans=preparedMaskTable hn := by
  rw [booleanMaskContextProgram_common,binaryMaskPlanProgram_plans]


def BooleanMaskContextResult.planActions {n : ℕ} (r : BooleanMaskContextResult n) : ℕ := r.planTable.actions


theorem booleanMaskContextProgram_planActions {n : ℕ} (hn : 0<n) :
    (booleanMaskContextProgram hn).planActions≤2^n*(14*n+11)+1 := by
  have hl : (booleanMaskContextProgram hn).common.outputs.length=2^n := by
    rw [booleanMaskContextProgram_common]
    exact binaryMaskPlanProgram_length hn
  change (booleanPlanTableProgram hn (booleanMaskContextProgram hn).common.outputs).actions≤_
  exact (booleanPlanTableProgram_actions hn _).trans_eq (by rw [hl])


theorem booleanMaskContextProgram_active_planActions (k : ℕ) :
    (booleanMaskContextProgram (by omega : 0<2+codeWires k)).planActions≤1553*(k+3)^6 := by
  have hd : 2^(2+codeWires k)≤16*(k+3)^3 := by
    rw [nativeActiveWires_eq]
    exact activeDimension_polynomial k
  have hw:=activeWires_log_bound k
  rw [←nativeActiveWires_eq] at hw
  have hc : Nat.clog 2 (k+3)≤k+3 :=
    Nat.clog_le_of_le_pow (Nat.lt_two_pow_self (n:=k+3)).le
  have hf : 14*(2+codeWires k)+11≤97*(k+3) := by omega
  have hp : (k+3)^4≤(k+3)^6 := Nat.pow_le_pow_right (by omega) (by decide)
  have h1 : 1≤(k+3)^6 := Nat.one_le_pow _ _ (by omega)
  calc
    _≤2^(2+codeWires k)*(14*(2+codeWires k)+11)+1 := booleanMaskContextProgram_planActions _
    _≤(16*(k+3)^3)*(97*(k+3))+1 := Nat.add_le_add_right (Nat.mul_le_mul hd hf) 1
    _=1552*(k+3)^4+1 := by ring
    _≤1552*(k+3)^6+(k+3)^6 := Nat.add_le_add (Nat.mul_le_mul_left 1552 hp) h1
    _=_ := by ring

/-- Same actual saved range/copy records plus newly retained Bool/list plan
construction records. Computing annotations and remaining native index/control
costs are separate from this partial finite constructor/list model. -/
def BooleanMaskContextResult.actions {n : ℕ} (r : BooleanMaskContextResult n) : ℕ :=
  r.common.actions+r.planActions


theorem booleanMaskContextProgram_active_actions (k : ℕ) :
    (booleanMaskContextProgram (by omega : 0<2+codeWires k)).actions≤12145*(k+3)^6 := by
  unfold BooleanMaskContextResult.actions
  rw [booleanMaskContextProgram_common]
  exact (Nat.add_le_add (binaryMaskPlanProgram_active_actions k)
    (booleanMaskContextProgram_active_planActions k)).trans_eq (by ring)

end EffectiveEncoding
