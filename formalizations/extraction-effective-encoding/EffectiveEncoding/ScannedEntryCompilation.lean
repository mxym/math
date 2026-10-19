import EffectiveEncoding.ScannedPreparedGray

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

structure ScannedEntryCompileResult (n : ℕ) where
  word : WordCode n
  gray : List (ScannedGrayCompileResult n)

/-- Packed endpoints survive through actual compilation, rather than being
 erased to functions and later reconstructed. Each stored-list decision and
 reverse program executes once. Its actual none/some branch also controls the
 accumulated mass, replacing the separate old endpoint-equality traversal. -/
def scannedEntryCompileProgram {n : ℕ} (plans : List (PreparedPauliPlan n)) (pivot : PackedBits n) :
    List (PackedBits n×ℕ) → ℕ → ℕ → ScannedEntryCompileResult n
  | [],_,_ => ⟨[],[]⟩
  | (target,B)::entries,A,j =>
    let compiled:=scannedPreparedRotationProgram plans pivot target (mergeCode A B j)
    let tail:=scannedEntryCompileProgram plans pivot entries
      (match compiled.decision.scan.first with | none => A | some _ => A+B) j
    ⟨compiled.word++tail.word,compiled::tail.gray⟩


theorem scannedEntryCompileProgram_word {n : ℕ} (plans : List (PreparedPauliPlan n))
    (pivot : PackedBits n) (entries : List (PackedBits n×ℕ)) (A j : ℕ) :
    (scannedEntryCompileProgram plans pivot entries A j).word=
      preparedCompileRaw plans (packedEntryProgram pivot entries A j) := by
  induction entries generalizing A with
  | nil => rfl
  | cons e entries ih =>
    obtain ⟨target,B⟩:=e
    by_cases he : pivot=target
    · have hp:=(packedGrayScanProgram_none pivot target).mpr (congrArg unpackBits he)
      simp only [scannedEntryCompileProgram,scannedPreparedRotationProgram, hp,
        listReverseMapIntoProgram_value,List.map_nil,List.reverse_nil,List.append_nil,List.nil_append,
        packedEntryProgram,dif_pos he,ih]
    · have hne : unpackBits pivot≠unpackBits target := fun h => he (unpackBits_injective n h)
      have hp:=packedGrayScanProgram_first_eq pivot target hne
      have hw:=scannedPreparedRotationProgram_word plans pivot target hne (mergeCode A B j)
      simp only [scannedEntryCompileProgram,packedEntryProgram,dif_neg he,
        preparedCompileRaw,List.flatMap_cons,preparedRawCompile,hw]
      change _++(scannedEntryCompileProgram plans pivot entries
        (match (packedGrayScanProgram pivot target).scan.first with | none => A | some _ => A+B) j).word=_
      rw [hp,ih]
      rfl


theorem scannedEntryCompileProgram_grayCount {n : ℕ} (plans : List (PreparedPauliPlan n))
    (pivot : PackedBits n) (entries : List (PackedBits n×ℕ)) (A j : ℕ) :
    (scannedEntryCompileProgram plans pivot entries A j).gray.length=entries.length := by
  induction entries generalizing A with
  | nil => rfl
  | cons e entries ih =>
    simp only [scannedEntryCompileProgram,List.length_cons,ih]

structure ScannedCandidateWordRun (n : ℕ) where
  common : CandidateWordRun n
  gray : List (ScannedGrayCompileResult n)

/-- Endpoint and mass records are stored once; the new packed entry compiler
 reads those same endpoints directly. Only erased proof transports refer to
 the old raw-code/function compiler. -/
def grayListIndexedCandidateRun {ι : Type*} {n : ℕ} (plans : List (PreparedPauliPlan n))
    (E : ι → CandidateRankEndpoint n) (c : ι → ℕ) (j : ℕ) : List ι → ScannedCandidateWordRun n
  | [] => ⟨⟨[],[]⟩,[]⟩
  | p::ps =>
    let pivot:=E p
    let initialMass:=c p
    let others:=ps.map (fun a => (E a,c a))
    let compiled:=scannedEntryCompileProgram plans pivot.point (others.map (fun a => (a.1.point,a.2))) initialMass j
    ⟨⟨compiled.word,pivot.ranks++others.flatMap (fun a => a.1.ranks)⟩,compiled.gray⟩


theorem grayListIndexedCandidateRun_common {ι : Type*} {n : ℕ} (plans : List (PreparedPauliPlan n))
    (E : ι → CandidateRankEndpoint n) (c : ι → ℕ) (j : ℕ) (xs : List ι) :
    (grayListIndexedCandidateRun plans E c j xs).common=listIndexedCandidateRun plans E c j xs := by
  cases xs with
  | nil => rfl
  | cons p ps => simp only [grayListIndexedCandidateRun,listIndexedCandidateRun,scannedEntryCompileProgram_word]


theorem grayListIndexedCandidateRun_grayCount {ι : Type*} {n : ℕ} (plans : List (PreparedPauliPlan n))
    (E : ι → CandidateRankEndpoint n) (c : ι → ℕ) (j : ℕ) (xs : List ι) :
    (grayListIndexedCandidateRun plans E c j xs).gray.length≤xs.length := by
  cases xs with
  | nil => exact le_refl 0
  | cons p ps =>
    simp only [grayListIndexedCandidateRun,scannedEntryCompileProgram_grayCount,List.length_map,List.length_cons]
    omega


def ScannedEntryCompileResult.actions {n : ℕ} (r : ScannedEntryCompileResult n) : ℕ :=
  (r.gray.map ScannedGrayCompileResult.actions).sum


theorem scannedEntryCompileProgram_actions {n : ℕ} (plans : List (PreparedPauliPlan n))
    (pivot : PackedBits n) (entries : List (PackedBits n×ℕ)) (A j : ℕ) :
    (scannedEntryCompileProgram plans pivot entries A j).actions≤
      (5*n+4)*entries.length+4*(scannedEntryCompileProgram plans pivot entries A j).word.length := by
  induction entries generalizing A with
  | nil => exact le_refl 0
  | cons e entries ih =>
    obtain ⟨target,B⟩:=e
    have hc:=scannedPreparedRotationProgram_actions_word plans pivot target (mergeCode A B j)
    have ht:=ih (match (scannedPreparedRotationProgram plans pivot target (mergeCode A B j)).decision.scan.first with
      | none => A | some _ => A+B)
    unfold ScannedEntryCompileResult.actions at ht
    dsimp only [ScannedEntryCompileResult.actions,scannedEntryCompileProgram]
    simp only [List.map_cons,List.sum_cons,List.length_append,List.length_cons,Nat.mul_add,Nat.mul_one]
    omega


def ScannedCandidateWordRun.actions {n : ℕ} (r : ScannedCandidateWordRun n) : ℕ :=
  (r.gray.map ScannedGrayCompileResult.actions).sum


theorem grayListIndexedCandidateRun_actions {ι : Type*} {n : ℕ} (plans : List (PreparedPauliPlan n))
    (E : ι → CandidateRankEndpoint n) (c : ι → ℕ) (j : ℕ) (xs : List ι) :
    (grayListIndexedCandidateRun plans E c j xs).actions≤(5*n+4)*xs.length+
      4*(grayListIndexedCandidateRun plans E c j xs).common.word.length := by
  cases xs with
  | nil => exact le_refl 0
  | cons p ps =>
    have h:=scannedEntryCompileProgram_actions plans (E p).point
      ((ps.map (fun a => (E a,c a))).map (fun a => (a.1.point,a.2))) (c p) j
    simp only [List.length_map] at h
    change (scannedEntryCompileProgram plans (E p).point _ _ _).actions≤_
    dsimp only [grayListIndexedCandidateRun]
    exact h.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.le_succ ps.length)) _)

end EffectiveEncoding
