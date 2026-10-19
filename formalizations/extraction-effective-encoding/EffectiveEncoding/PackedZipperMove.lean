import EffectiveEncoding.ZipperMoveCorrectness

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding


theorem finRange_values_range' (n : ℕ) : (List.finRange n).map Fin.val=List.range' 0 n := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

structure PackedZipperMoveResult (n : ℕ) where
  input : PackedGrayScanResult n
  program : ZipperMoveResult n

/-- The already executed decision's same wire/bit lists enter the actual
 zipper. No scan, input projection, vector conversion or index read is replayed
 here. The equality argument and data-length arguments are erased proofs. -/
def retainedPackedZipperMoveProgram {n : ℕ} (plans : List (PreparedPauliPlan n))
    (x y : PackedBits n) (decision : PackedGrayScanResult n) (hd : decision=packedGrayScanProgram x y) :
    PackedZipperMoveResult n :=
  let program:=zipperPreparedMoveProgram plans decision.wires decision.left.bits decision.right.bits [] false (by
    rw [hd]
    change 0+y.toList.length=n
    simp)
  ⟨decision,program⟩

/-- Complete literal Gray move word equality. The old function-index/update
 implementation is solely a proof specification of the new stored-list loop. -/
theorem retainedPackedZipperMoveProgram_word {n : ℕ} (plans : List (PreparedPauliPlan n))
    (x y : PackedBits n) (decision : PackedGrayScanResult n) (hd : decision=packedGrayScanProgram x y)
    (h : unpackBits x≠unpackBits y) :
    (retainedPackedZipperMoveProgram plans x y decision hd).program.word=
      preparedMoveCode plans (unpackBits x) (otherWires (differingWire (unpackBits x) (unpackBits y) h)) (unpackBits y) := by
  subst decision
  have ht : (packedGrayScanProgram x y).left.bits=(packedGrayScanProgram x y).wires.map (unpackBits x) := by
    exact (packedMask_finRange_map x).symm
  have hc : (packedGrayScanProgram x y).wires.map Fin.val=
      List.range' ([] : List Bool).length (packedGrayScanProgram x y).wires.length := by
    simpa only [packedGrayScanProgram,List.length_nil,List.length_finRange] using finRange_values_range' n
  have hs : y.toList=([] : List Bool).reverse++(packedGrayScanProgram x y).right.bits := rfl
  rw [←skipFirstMoveSpecification_packed plans x y h]
  exact zipperPreparedMoveProgram_word plans (unpackBits x) _ _ _ [] false _ y ht hc hs


theorem retainedPackedZipperMoveProgram_actions {n : ℕ} (plans : List (PreparedPauliPlan n))
    (x y : PackedBits n) (decision : PackedGrayScanResult n) (hd : decision=packedGrayScanProgram x y) :
    (retainedPackedZipperMoveProgram plans x y decision hd).program.actions≤(4*n+6)*(n+1) := by
  subst decision
  change (zipperPreparedMoveProgram plans (List.finRange n) x.toList y.toList [] false _).actions≤_
  simpa only [List.length_finRange] using
    zipperPreparedMoveProgram_actions plans (List.finRange n) x.toList y.toList [] false (by simp)

end EffectiveEncoding
