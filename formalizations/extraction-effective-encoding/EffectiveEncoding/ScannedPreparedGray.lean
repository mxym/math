import EffectiveEncoding.PackedGrayDecision

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

structure ScannedGrayCompileResult (n : ℕ) where
  word : WordCode n
  decision : PackedGrayScanResult n
  forward : WordCode n
  adjacent : WordCode n
  reversal : ListAssemblyResult (GateCode n)

/-- One actual packed-list decision, one stored forward Gray move, one stored
 adjacent word, and one actual reverse/inverse list program. All records belong
 to this execution. The old finite-set decision is used only in its proof. -/
def scannedPreparedSwapProgram {n : ℕ} (plans : List (PreparedPauliPlan n)) (x y : PackedBits n) :
    ScannedGrayCompileResult n :=
  let decision:=packedGrayScanProgram x y
  let core:=match decision.scan.first with
    | none => ([],[])
    | some t => (preparedMoveCode plans (unpackBits x) decision.scan.others (unpackBits y),
        preparedAdjacentSwapCode plans t (unpackBits x))
  let reversal:=listReverseMapIntoProgram GateCode.inverse core.1 []
  ⟨core.1++core.2++reversal.value,decision,core.1,core.2,reversal⟩


theorem scannedPreparedSwapProgram_word {n : ℕ} (plans : List (PreparedPauliPlan n)) (x y : PackedBits n) :
    (scannedPreparedSwapProgram plans x y).word=preparedSwapCode plans (unpackBits x) (unpackBits y) := by
  by_cases h : unpackBits x=unpackBits y
  · have hp:=(packedGrayScanProgram_none x y).mpr h
    simp only [scannedPreparedSwapProgram,hp,listReverseMapIntoProgram_value,List.map_nil,List.reverse_nil,
      List.append_nil,preparedSwapCode,dif_pos h]
  · have hp:=packedGrayScanProgram_first_eq x y h
    have ho:=packedGrayScanProgram_others_eq x y h
    simp only [scannedPreparedSwapProgram,hp,ho,listReverseMapIntoProgram_value,List.append_nil,
      preparedSwapCode,dif_neg h,reverseCode]

/-- It is harmless to define the equal-input case explicitly. Actual merge
 callers supply distinct endpoints; that fact is used only in correctness. -/
def scannedPreparedRotationProgram {n : ℕ} (plans : List (PreparedPauliPlan n))
    (x y : PackedBits n) (a : AngleCode) : ScannedGrayCompileResult n :=
  let decision:=packedGrayScanProgram x y
  let core:=match decision.scan.first with
    | none => ([],[])
    | some t => (preparedMoveCode plans (unpackBits x) decision.scan.others (unpackBits y),
        preparedOrientedRotationCode plans t (unpackBits x) a)
  let reversal:=listReverseMapIntoProgram GateCode.inverse core.1 []
  ⟨core.1++core.2++reversal.value,decision,core.1,core.2,reversal⟩


theorem scannedPreparedRotationProgram_word {n : ℕ} (plans : List (PreparedPauliPlan n))
    (x y : PackedBits n) (h : unpackBits x≠unpackBits y) (a : AngleCode) :
    (scannedPreparedRotationProgram plans x y a).word=
      preparedRotationCode plans (unpackBits x) (unpackBits y) h a := by
  have hp:=packedGrayScanProgram_first_eq x y h
  have ho:=packedGrayScanProgram_others_eq x y h
  simp only [scannedPreparedRotationProgram,hp,ho,listReverseMapIntoProgram_value,List.append_nil,
    preparedRotationCode,reverseCode]


theorem scannedPreparedRotationProgram_equal_word {n : ℕ} (plans : List (PreparedPauliPlan n))
    (x y : PackedBits n) (h : x=y) (a : AngleCode) :
    (scannedPreparedRotationProgram plans x y a).word=[] := by
  subst y
  have hp:=(packedGrayScanProgram_none x x).mpr rfl
  simp only [scannedPreparedRotationProgram,hp,listReverseMapIntoProgram_value,List.map_nil,
    List.reverse_nil,List.append_nil]


def ScannedGrayCompileResult.actions {n : ℕ} (r : ScannedGrayCompileResult n) : ℕ :=
  r.decision.actions+r.reversal.trace.actions


theorem scannedPreparedSwapProgram_actions {n : ℕ} (plans : List (PreparedPauliPlan n)) (x y : PackedBits n) :
    (scannedPreparedSwapProgram plans x y).actions≤
      5*n+3+4*(scannedPreparedSwapProgram plans x y).forward.length+1 := by
  have hs:=packedGrayScanProgram_actions x y
  dsimp only [ScannedGrayCompileResult.actions,scannedPreparedSwapProgram]
  rw [listReverseMapIntoProgram_actions]
  omega


theorem scannedPreparedRotationProgram_actions {n : ℕ} (plans : List (PreparedPauliPlan n))
    (x y : PackedBits n) (a : AngleCode) :
    (scannedPreparedRotationProgram plans x y a).actions≤
      5*n+3+4*(scannedPreparedRotationProgram plans x y a).forward.length+1 := by
  have hs:=packedGrayScanProgram_actions x y
  dsimp only [ScannedGrayCompileResult.actions,scannedPreparedRotationProgram]
  rw [listReverseMapIntoProgram_actions]
  omega


theorem scannedPreparedSwapProgram_forward_length {n : ℕ} (plans : List (PreparedPauliPlan n)) (x y : PackedBits n) :
    (scannedPreparedSwapProgram plans x y).forward.length≤(scannedPreparedSwapProgram plans x y).word.length := by
  dsimp only [scannedPreparedSwapProgram]
  simp only [List.length_append]
  omega


theorem scannedPreparedRotationProgram_forward_length {n : ℕ} (plans : List (PreparedPauliPlan n))
    (x y : PackedBits n) (a : AngleCode) :
    (scannedPreparedRotationProgram plans x y a).forward.length≤
      (scannedPreparedRotationProgram plans x y a).word.length := by
  dsimp only [scannedPreparedRotationProgram]
  simp only [List.length_append]
  omega


theorem scannedPreparedSwapProgram_actions_word {n : ℕ} (plans : List (PreparedPauliPlan n)) (x y : PackedBits n) :
    (scannedPreparedSwapProgram plans x y).actions≤5*n+4+4*(scannedPreparedSwapProgram plans x y).word.length := by
  have h:=scannedPreparedSwapProgram_actions plans x y
  have hl:=scannedPreparedSwapProgram_forward_length plans x y
  omega


theorem scannedPreparedRotationProgram_actions_word {n : ℕ} (plans : List (PreparedPauliPlan n))
    (x y : PackedBits n) (a : AngleCode) :
    (scannedPreparedRotationProgram plans x y a).actions≤5*n+4+4*(scannedPreparedRotationProgram plans x y a).word.length := by
  have h:=scannedPreparedRotationProgram_actions plans x y a
  have hl:=scannedPreparedRotationProgram_forward_length plans x y a
  omega

end EffectiveEncoding
