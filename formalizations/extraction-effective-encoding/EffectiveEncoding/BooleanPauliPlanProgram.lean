import EffectiveEncoding.ListPauliPlanProgram

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

structure BooleanPauliPlanResult (n : ℕ) where
  coordinates : MaskCoordinateResult (Fin n)
  built : ListPauliPlanResult n

/-- Actual Bool/list plan construction. Only the erased proof relates selected
coordinates to finite sets; no finite-set construction, sort, minimum or erase
occurs in this runtime program or its concrete list-builder callees. -/
def booleanPauliPlanProgram {n : ℕ} (hn : 0<n) (mask : PackedBits n) : BooleanPauliPlanResult n :=
  let coordinates:=booleanMaskCoordinates mask
  let built:=listPauliPlanProgram hn coordinates.items (booleanMaskCoordinates_nodup mask)
  ⟨coordinates,built⟩


theorem booleanPauliPlanProgram_plan {n : ℕ} (hn : 0<n) (mask : PackedBits n) :
    (booleanPauliPlanProgram hn mask).built.plan=preparePauliPlan hn (maskOfBits (unpackBits mask)) :=
  listPauliPlanProgram_plan hn _ _ _ (booleanMaskCoordinates_sortedMask mask)


def BooleanPauliPlanResult.actions {n : ℕ} (r : BooleanPauliPlanResult n) : ℕ :=
  r.coordinates.trace.actions+r.built.actions


theorem booleanPauliPlanProgram_actions {n : ℕ} (hn : 0<n) (mask : PackedBits n) :
    (booleanPauliPlanProgram hn mask).actions≤14*n+5 := by
  have hc:=booleanMaskCoordinates_actions mask
  have hl : (booleanMaskCoordinates mask).items.length≤n := by
    rw [booleanMaskCoordinates_items]
    exact (List.length_filter_le _ _).trans_eq (List.length_finRange (n:=n))
  have hb:=(listPauliPlanProgram_actions hn (booleanMaskCoordinates mask).items
    (booleanMaskCoordinates_nodup mask)).trans (Nat.add_le_add_right (Nat.mul_le_mul_left 10 hl) 4)
  exact (Nat.add_le_add hc hb).trans_eq (by ring)

inductive BooleanPlanTableTrace where
  | done
  | emit : BooleanPlanTableTrace → BooleanPlanTableTrace


def BooleanPlanTableTrace.actions : BooleanPlanTableTrace → ℕ
  | .done => 1
  | .emit tail => tail.actions+6

structure BooleanPlanTableResult (n : ℕ) where
  plans : List (PreparedPauliPlan n)
  programs : List (BooleanPauliPlanResult n)
  trace : BooleanPlanTableTrace

/-- One pass invokes each actual builder once and stores its same plan and
program record. Both result spines and their finite constructor visits have a
concrete trace; no separate map can replay a builder. -/
def booleanPlanTableProgram {n : ℕ} (hn : 0<n) : List (EndpointBitsResult n) → BooleanPlanTableResult n
  | [] => ⟨[],[],.done⟩
  | x::xs =>
    let built:=booleanPauliPlanProgram hn x.bits
    let tail:=booleanPlanTableProgram hn xs
    ⟨built.built.plan::tail.plans,built::tail.programs,.emit tail.trace⟩


theorem booleanPlanTableProgram_plans {n : ℕ} (hn : 0<n) (xs : List (EndpointBitsResult n)) :
    (booleanPlanTableProgram hn xs).plans=
      xs.map (fun output => preparePauliPlan hn (maskOfBits (unpackBits output.bits))) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [booleanPlanTableProgram,booleanPauliPlanProgram_plan,ih,List.map_cons]


theorem booleanPlanTableProgram_programs {n : ℕ} (hn : 0<n) (xs : List (EndpointBitsResult n)) :
    (booleanPlanTableProgram hn xs).programs=xs.map (fun output => booleanPauliPlanProgram hn output.bits) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [booleanPlanTableProgram,ih,List.map_cons]


theorem booleanPlanTableProgram_traceActions {n : ℕ} (hn : 0<n) (xs : List (EndpointBitsResult n)) :
    (booleanPlanTableProgram hn xs).trace.actions=6*xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [booleanPlanTableProgram,BooleanPlanTableTrace.actions,List.length_cons,ih];omega


def BooleanPlanTableResult.actions {n : ℕ} (r : BooleanPlanTableResult n) : ℕ :=
  (r.programs.map BooleanPauliPlanResult.actions).sum+r.trace.actions


theorem booleanPlanTableProgram_actions {n : ℕ} (hn : 0<n) (xs : List (EndpointBitsResult n)) :
    (booleanPlanTableProgram hn xs).actions≤xs.length*(14*n+11)+1 := by
  induction xs with
  | nil => simp [booleanPlanTableProgram,BooleanPlanTableResult.actions,BooleanPlanTableTrace.actions]
  | cons x xs ih =>
    have h:=booleanPauliPlanProgram_actions hn x.bits
    change (booleanPauliPlanProgram hn x.bits).actions+
      ((booleanPlanTableProgram hn xs).programs.map BooleanPauliPlanResult.actions).sum+
      ((booleanPlanTableProgram hn xs).trace.actions+6)≤_
    unfold BooleanPlanTableResult.actions at ih
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

end EffectiveEncoding
