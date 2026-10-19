import EffectiveEncoding.ScannedEntryCompilation

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding


def grayStoredLettersBranchRun {k : ℕ} (plans : List (PreparedPauliPlan (2+codeWires k)))
    (x : NativeOccupation (k+1)) (letters : List (Fin 4))
    (hs : letters=(nativeSelected x).sort (·≤·)) : ScannedCandidateWordRun (2+codeWires k) :=
  grayListIndexedCandidateRun plans (candidateNativeBranchEndpoint x) (fun a => nativeMass x a.1) (k+1)
    (typedOccupationLetters x letters hs)


theorem grayStoredLettersBranchRun_common {k : ℕ} (plans : List (PreparedPauliPlan (2+codeWires k)))
    (x : NativeOccupation (k+1)) (letters : List (Fin 4))
    (hs : letters=(nativeSelected x).sort (·≤·)) :
    (grayStoredLettersBranchRun plans x letters hs).common=storedLettersBranchRun plans x letters hs :=
  grayListIndexedCandidateRun_common _ _ _ _ _


theorem typedOccupationLetters_length {k : ℕ} (x : NativeOccupation k) (letters : List (Fin 4))
    (hs : letters=(nativeSelected x).sort (·≤·)) : (typedOccupationLetters x letters hs).length≤4 := by
  have h:=congrArg List.length (typedOccupationLetters_values x letters hs)
  simp only [List.length_map] at h
  rw [h,hs,Finset.length_sort]
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by decide)


theorem grayStoredLettersBranchRun_actions {k : ℕ} (plans : List (PreparedPauliPlan (2+codeWires k)))
    (x : NativeOccupation (k+1)) (letters : List (Fin 4))
    (hs : letters=(nativeSelected x).sort (·≤·)) :
    (grayStoredLettersBranchRun plans x letters hs).actions≤(5*(2+codeWires k)+4)*4+
      4*(grayStoredLettersBranchRun plans x letters hs).common.word.length :=
  (grayListIndexedCandidateRun_actions _ _ _ _ _).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left _ (typedOccupationLetters_length x letters hs)) _)


def grayStoredLettersBranchTableRun {k : ℕ} (plans : List (PreparedPauliPlan (2+codeWires k))) :
    (xs : List (AcceptedOccupationLettersResult (k+1))) →
    (∀ r∈xs,r.letters.items=(nativeSelected r.native).sort (·≤·)) → ScannedCandidateWordRun (2+codeWires k)
  | [],_ => ⟨⟨[],[]⟩,[]⟩
  | r::rs,h =>
    let branch:=grayStoredLettersBranchRun plans r.native r.letters.items (h r (by simp))
    let tail:=grayStoredLettersBranchTableRun plans rs (fun a ha => h a (by simp [ha]))
    ⟨⟨branch.common.word++tail.common.word,branch.common.ranks++tail.common.ranks⟩,branch.gray++tail.gray⟩


theorem grayStoredLettersBranchTableRun_common {k : ℕ} (plans : List (PreparedPauliPlan (2+codeWires k)))
    (xs : List (AcceptedOccupationLettersResult (k+1)))
    (h : ∀ r∈xs,r.letters.items=(nativeSelected r.native).sort (·≤·)) :
    (grayStoredLettersBranchTableRun plans xs h).common=storedLettersBranchTableRun plans xs h := by
  induction xs with
  | nil => rfl
  | cons r rs ih =>
    simp only [grayStoredLettersBranchTableRun,storedLettersBranchTableRun,grayStoredLettersBranchRun_common,ih]


theorem grayStoredLettersBranchTableRun_actions {k : ℕ} (plans : List (PreparedPauliPlan (2+codeWires k)))
    (xs : List (AcceptedOccupationLettersResult (k+1)))
    (h : ∀ r∈xs,r.letters.items=(nativeSelected r.native).sort (·≤·)) :
    (grayStoredLettersBranchTableRun plans xs h).actions≤(5*(2+codeWires k)+4)*4*xs.length+
      4*(grayStoredLettersBranchTableRun plans xs h).common.word.length := by
  induction xs with
  | nil => exact le_refl 0
  | cons r rs ih =>
    have hb:=grayStoredLettersBranchRun_actions plans r.native r.letters.items (h r (by simp))
    have ht:=ih (fun a ha => h a (by simp [ha]))
    simp only [Nat.mul_add,Nat.mul_one] at hb ht
    unfold ScannedCandidateWordRun.actions at hb ht ⊢
    dsimp only [grayStoredLettersBranchTableRun]
    simp only [List.map_append,List.sum_append,List.length_append,List.length_cons,Nat.mul_add,Nat.mul_one]
    omega

/-- Each actual packed swap compile retains its decision, projections and
 reverse-map trace. The same source/target endpoints update the swap stack. -/
def grayStoredLettersAlignmentRun {k : ℕ} (plans : List (PreparedPauliPlan (2+codeWires k))) :
    (xs : List (AcceptedOccupationLettersResult (k+1))) →
    (∀ r∈xs,r.letters.items=(nativeSelected r.native).sort (·≤·)) →
    List (PackedBits (2+codeWires k)×PackedBits (2+codeWires k)) → ScannedCandidateWordRun (2+codeWires k)
  | [],_,_ => ⟨⟨[],[]⟩,[]⟩
  | r::rs,h,ss =>
    let source:=storedLettersPivotEndpoint r.native r.letters.items (h r (by simp))
    let evaluated:=applyPackedSwaps ss source.point
    let target:=candidateNativeNextEndpoint r.native
    let compiled:=scannedPreparedSwapProgram plans evaluated.1 target.point
    let tail:=grayStoredLettersAlignmentRun plans rs (fun a ha => h a (by simp [ha])) ((evaluated.1,target.point)::ss)
    ⟨⟨compiled.word++tail.common.word,source.ranks++target.ranks++tail.common.ranks⟩,compiled::tail.gray⟩


theorem grayStoredLettersAlignmentRun_common {k : ℕ} (plans : List (PreparedPauliPlan (2+codeWires k)))
    (xs : List (AcceptedOccupationLettersResult (k+1)))
    (h : ∀ r∈xs,r.letters.items=(nativeSelected r.native).sort (·≤·))
    (ss : List (PackedBits (2+codeWires k)×PackedBits (2+codeWires k))) :
    (grayStoredLettersAlignmentRun plans xs h ss).common=storedLettersAlignmentRun plans xs h ss := by
  induction xs generalizing ss with
  | nil => rfl
  | cons r rs ih =>
    simp only [grayStoredLettersAlignmentRun,storedLettersAlignmentRun,scannedPreparedSwapProgram_word,ih]


theorem grayStoredLettersAlignmentRun_actions {k : ℕ} (plans : List (PreparedPauliPlan (2+codeWires k)))
    (xs : List (AcceptedOccupationLettersResult (k+1)))
    (h : ∀ r∈xs,r.letters.items=(nativeSelected r.native).sort (·≤·))
    (ss : List (PackedBits (2+codeWires k)×PackedBits (2+codeWires k))) :
    (grayStoredLettersAlignmentRun plans xs h ss).actions≤(5*(2+codeWires k)+4)*xs.length+
      4*(grayStoredLettersAlignmentRun plans xs h ss).common.word.length := by
  induction xs generalizing ss with
  | nil => exact le_refl 0
  | cons r rs ih =>
    let source:=storedLettersPivotEndpoint r.native r.letters.items (h r (by simp))
    let evaluated:=applyPackedSwaps ss source.point
    let target:=candidateNativeNextEndpoint r.native
    have hc:=scannedPreparedSwapProgram_actions_word plans evaluated.1 target.point
    have ht:=ih (fun a ha => h a (by simp [ha])) ((evaluated.1,target.point)::ss)
    dsimp only [source,evaluated,target] at hc ht
    simp only [Nat.mul_add,Nat.mul_one] at hc ht
    unfold ScannedCandidateWordRun.actions at ht ⊢
    dsimp only [grayStoredLettersAlignmentRun]
    simp only [List.map_cons,List.sum_cons,List.length_append,List.length_cons,Nat.mul_add,Nat.mul_one]
    omega

end EffectiveEncoding
