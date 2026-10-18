import EffectiveEncoding.RankedBranchWork

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

structure RankedAlignmentRun (n : ℕ) where
  result : PackedAlignmentRun n
  work : RankWork

/-- Source/target rank records are evaluated once per step. The swap stack
stores only their finite endpoints. Annotations are read from these records. -/
def rankedAlignmentRun {ι : Type*} {n : ℕ} (hn : 0<n)
    (E F : ι → EncodedEndpoint n) :
    List ι → List (PackedBits n×PackedBits n) → RankedAlignmentRun n
  | [],_ => ⟨⟨[],0,0⟩,fun _ => 0⟩
  | a::as,ss =>
    let source:=E a
    let evaluated:=applyPackedSwaps ss source.point
    let target:=F a
    let headCode:=swapCode hn (unpackBits evaluated.1) (unpackBits target.point)
    let tail:=rankedAlignmentRun hn E F as ((evaluated.1,target.point)::ss)
    ⟨⟨headCode++tail.result.word,evaluated.2+tail.result.swapApplications,
      2*n+tail.result.endpointCoordinates⟩,
      fun i => source.work i+target.work i+tail.work i⟩


theorem rankedAlignmentRun_result {ι : Type*} {n : ℕ} (hn : 0<n)
    (E F : ι → EncodedEndpoint n) (e f : ι ↪ Bits n)
    (hE : ∀ a,(E a).point=packBits (e a)) (hF : ∀ a,(F a).point=packBits (f a))
    (xs : List ι) (ss : List (PackedBits n×PackedBits n)) :
    (rankedAlignmentRun hn E F xs ss).result=packedAlignmentRun hn e f xs ss := by
  induction xs generalizing ss with
  | nil => rfl
  | cons a xs ih => simp only [rankedAlignmentRun,packedAlignmentRun,hE,hF,ih]


theorem rankedAlignmentRun_work {ι : Type*} {n : ℕ} (hn : 0<n)
    (E F : ι → EncodedEndpoint n) (xs : List ι) (ss : List (PackedBits n×PackedBits n))
    (i : Fin 3) (B : ℕ) (hE : ∀ a,(E a).work i≤B) (hF : ∀ a,(F a).work i≤B) :
    (rankedAlignmentRun hn E F xs ss).work i≤2*B*xs.length := by
  induction xs generalizing ss with
  | nil => simp [rankedAlignmentRun]
  | cons a xs ih =>
    have ht:=ih (((applyPackedSwaps ss (E a).point).1,(F a).point)::ss)
    change (E a).work i+(F a).work i+_≤_
    calc
      _≤B+B+2*B*xs.length := Nat.add_le_add (Nat.add_le_add (hE a) (hF a)) ht
      _=2*B*(a::xs).length := by simp only [List.length_cons];ring


def encodedPivotEndpoint {k : ℕ} (ν : Sym (Fin 4) (k+1)) : EncodedEndpoint (2+codeWires k) :=
  encodedBranchEndpoint ν (occupiedPivot ν)


theorem encodedPivotEndpoint_value {k : ℕ} (ν : Sym (Fin 4) (k+1)) :
    (encodedPivotEndpoint ν).point=packBits (pivotEmbedding (constructedCompactEncoding k) ν) := by
  exact encodedBranchEndpoint_value ν (occupiedPivot ν)


theorem encodedPivotEndpoint_work {k : ℕ} (ν : Sym (Fin 4) (k+1)) (i : Fin 3) :
    (encodedPivotEndpoint ν).work i≤rankWorkConstant i*(k+2)^3 := by
  exact (encodedBranchEndpoint_work ν (occupiedPivot ν) i).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3))

end EffectiveEncoding
