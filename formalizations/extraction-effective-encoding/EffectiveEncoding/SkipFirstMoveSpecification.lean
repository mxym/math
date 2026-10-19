import EffectiveEncoding.ZipperPackedUpdate

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

/-- Proof specification for the zipper loop, not its runtime implementation.
 Equal prefix coordinates need no move. The first unequal pair is the pivot
 and is skipped; later unequal pairs are the actual Gray moves. -/
def skipFirstMoveSpecification {n : ℕ} (plans : List (PreparedPauliPlan n)) (x : Bits n) :
    List (Fin n) → Bits n → Bool → WordCode n
  | [],_,_ => []
  | j::js,y,seen =>
    if y j=x j then skipFirstMoveSpecification plans x js y seen else
      if seen then preparedAdjacentSwapCode plans j y++
        skipFirstMoveSpecification plans x js (Function.update y j (x j)) true
      else skipFirstMoveSpecification plans x js y true


theorem skipFirstMoveSpecification_seen {n : ℕ} (plans : List (PreparedPauliPlan n)) (x : Bits n)
    (wires : List (Fin n)) (y : Bits n) :
    skipFirstMoveSpecification plans x wires y true=preparedMoveCode plans x wires y := by
  induction wires generalizing y with
  | nil => rfl
  | cons j js ih =>
    simp only [skipFirstMoveSpecification,preparedMoveCode,ite_true,ih]


theorem skipFirstMoveSpecification_scan {n : ℕ} (plans : List (PreparedPauliPlan n)) (x : Bits n)
    (wires : List (Fin n)) (hnd : wires.Nodup) (y : Bits n) :
    skipFirstMoveSpecification plans x wires y false=
      match (booleanGrayScanProgram wires (wires.map x) (wires.map y)).first with
      | none => []
      | some t => preparedMoveCode plans x (wires.erase t) y := by
  induction wires with
  | nil => rfl
  | cons j js ih =>
    by_cases hy : y j=x j
    · have hb : (x j==y j)=true := by simp [hy]
      simp only [skipFirstMoveSpecification,if_pos hy,List.map_cons,booleanGrayScanProgram,hb,ite_true]
      rw [ih (List.nodup_cons.mp hnd).2]
      cases hp : (booleanGrayScanProgram js (js.map x) (js.map y)).first with
      | none => rfl
      | some t =>
        have hm:=booleanGrayScanProgram_first_mem js x y t hp
        have hne : j≠t := by intro he;subst j;exact (List.nodup_cons.mp hnd).1 hm
        simp [List.erase_cons,hne,Ne.symm hne,preparedMoveCode,hy]
    · have hb : (x j==y j)=false := by simp [Ne.symm hy]
      simp only [skipFirstMoveSpecification,if_neg hy,Bool.false_eq_true,ite_false,List.map_cons,
        booleanGrayScanProgram,hb,skipFirstMoveSpecification_seen,List.erase_cons_head]

/-- The eventual packed zipper loop need only refine this specification. The
 old finite-set otherWires appears here on the proof side alone. -/
theorem skipFirstMoveSpecification_packed {n : ℕ} (plans : List (PreparedPauliPlan n))
    (x y : PackedBits n) (h : unpackBits x≠unpackBits y) :
    skipFirstMoveSpecification plans (unpackBits x) (List.finRange n) (unpackBits y) false=
      preparedMoveCode plans (unpackBits x) (otherWires (differingWire (unpackBits x) (unpackBits y) h)) (unpackBits y) := by
  rw [skipFirstMoveSpecification_scan _ _ _ (List.nodup_finRange n)]
  have hp:=packedGrayScanProgram_first_eq x y h
  change (booleanGrayScanProgram (List.finRange n) x.toList y.toList).first=_ at hp
  rw [←packedMask_finRange_map x,←packedMask_finRange_map y] at hp
  rw [hp]
  simp only [finRange_erase_otherWires]

end EffectiveEncoding
