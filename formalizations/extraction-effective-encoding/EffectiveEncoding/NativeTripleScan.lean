import EffectiveEncoding.NativeTripleWords

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

structure NativeTripleScanResult where
  index : ℕ
  tests : List NativeTripleComparison

/-- Each candidate is tested once using its stored Boolean count words.
The scan stores exactly the executed comparison records. Nat result-index
increment and list/control/record bookkeeping are not charged here. -/
def nativeTripleScanProgram (x : NativeTripleWords) : List NativeTripleWords → NativeTripleScanResult
  | [] => ⟨0,[]⟩
  | y::ys =>
    let test:=nativeTripleComparisonProgram y x
    if test.equal then ⟨0,[test]⟩ else
      let tail:=nativeTripleScanProgram x ys
      ⟨tail.index+1,test::tail.tests⟩


theorem nativeTripleScanProgram_index (x : NativeTripleWords) (xs : List NativeTripleWords) :
    (nativeTripleScanProgram x xs).index=(indexTriplesWithQueries x.value (xs.map NativeTripleWords.value)).1 := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    simp only [nativeTripleScanProgram,indexTriplesWithQueries,List.map_cons,
      nativeTripleComparisonProgram_equal,tripleEqualityRun_value]
    split_ifs <;> simp_all

/-- Old logical field-query count, retained only as erased specification
metadata. The actual comparisons are the concrete Boolean records above. -/
theorem nativeTripleScanProgram_logicalQueryCount (x : NativeTripleWords) (xs : List NativeTripleWords) :
    3*(nativeTripleScanProgram x xs).tests.length=
      (indexTriplesWithQueries x.value (xs.map NativeTripleWords.value)).2 := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    simp only [nativeTripleScanProgram,indexTriplesWithQueries,List.map_cons,
      nativeTripleComparisonProgram_equal,tripleEqualityRun_value,tripleEqualityRun_count]
    split_ifs <;> simp_all [Nat.mul_add,Nat.add_comm]


theorem nativeTripleScanProgram_testCount (x : NativeTripleWords) (xs : List NativeTripleWords) :
    (nativeTripleScanProgram x xs).tests.length≤xs.length := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    simp only [nativeTripleScanProgram]
    split_ifs <;> simp_all <;> omega


def NativeTripleScanResult.comparisonActions (r : NativeTripleScanResult) : ℕ :=
  (r.tests.map NativeTripleComparison.actions).sum


theorem nativeTripleScanProgram_comparisonActions (x : NativeTripleWords) (xs : List NativeTripleWords) (B : ℕ)
    (hx : x.Width B) (hxs : ∀ y∈xs,y.Width B) :
    (nativeTripleScanProgram x xs).comparisonActions≤xs.length*(48*(B+1)+6) := by
  induction xs with
  | nil => simp [nativeTripleScanProgram,NativeTripleScanResult.comparisonActions]
  | cons y ys ih =>
    have hy:=hxs y (by simp)
    have ht:=ih (fun z hz => hxs z (by simp [hz]))
    have htest:=nativeTripleComparisonProgram_actions y x B hy hx
    simp only [nativeTripleScanProgram]
    split_ifs
    · simpa only [NativeTripleScanResult.comparisonActions,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
        Nat.add_zero] using htest.trans (Nat.le_mul_of_pos_left _ (by simp))
    · change (nativeTripleComparisonProgram y x).actions+
        (nativeTripleScanProgram x ys).comparisonActions≤_
      exact (Nat.add_le_add htest ht).trans_eq (by simp only [List.length_cons];ring)

end EffectiveEncoding
