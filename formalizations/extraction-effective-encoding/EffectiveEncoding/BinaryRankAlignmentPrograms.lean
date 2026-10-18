import EffectiveEncoding.BinaryRankBranchPrograms

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

structure BinaryAlignmentResult (n : ℕ) where
  result : RankedAlignmentRun n
  programs : List BinaryRankProgramRecord


def BinaryAlignmentResult.encodingActions {n : ℕ} (r : BinaryAlignmentResult n) : ℕ :=
  binaryRankProgramsActions r.programs

/-- Stored-swap alignment with the actual source/target rank-bit records
retained once per step. Existing shared Pauli plans are reused. -/
def binaryAlignmentRun {ι : Type*} {n : ℕ} (plans : List (PreparedPauliPlan n))
    (E F : ι → BinaryEncodedEndpoint n) :
    List ι → List (PackedBits n×PackedBits n) → BinaryAlignmentResult n
  | [],_ => ⟨⟨⟨[],0,0⟩,fun _ => 0⟩,[]⟩
  | a::as,ss =>
    let source:=E a
    let evaluated:=applyPackedSwaps ss source.endpoint.point
    let target:=F a
    let headCode:=preparedSwapCode plans (unpackBits evaluated.1) (unpackBits target.endpoint.point)
    let tail:=binaryAlignmentRun plans E F as ((evaluated.1,target.endpoint.point)::ss)
    ⟨⟨⟨headCode++tail.result.result.word,evaluated.2+tail.result.result.swapApplications,
      2*n+tail.result.result.endpointCoordinates⟩,
      fun i => source.endpoint.work i+target.endpoint.work i+tail.result.work i⟩,
      source.programs++target.programs++tail.programs⟩


theorem binaryAlignmentRun_result {ι : Type*} {n : ℕ} (plans : List (PreparedPauliPlan n))
    (E F : ι → BinaryEncodedEndpoint n) (xs : List ι) (ss : List (PackedBits n×PackedBits n)) :
    (binaryAlignmentRun plans E F xs ss).result=
      preparedRankedAlignmentRun plans (fun a => (E a).endpoint) (fun a => (F a).endpoint) xs ss := by
  induction xs generalizing ss with
  | nil => rfl
  | cons a xs ih => simp only [binaryAlignmentRun,preparedRankedAlignmentRun,ih]


theorem binaryAlignmentRun_encodingActions {ι : Type*} {n : ℕ} (plans : List (PreparedPauliPlan n))
    (E F : ι → BinaryEncodedEndpoint n) (xs : List ι) (ss : List (PackedBits n×PackedBits n))
    (B : ℕ) (hE : ∀ a,(E a).encodingActions≤B) (hF : ∀ a,(F a).encodingActions≤B) :
    (binaryAlignmentRun plans E F xs ss).encodingActions≤2*B*xs.length := by
  induction xs generalizing ss with
  | nil => exact le_refl 0
  | cons a xs ih =>
    have ht:=ih (((applyPackedSwaps ss (E a).endpoint.point).1,(F a).endpoint.point)::ss)
    change binaryRankProgramsActions ((E a).programs++(F a).programs++_)≤_
    rw [binaryRankProgramsActions_append,binaryRankProgramsActions_append]
    exact (Nat.add_le_add (Nat.add_le_add (hE a) (hF a)) ht).trans_eq (by simp only [List.length_cons];ring)


def binaryNativeBranchTableRun {k : ℕ} (plans : List (PreparedPauliPlan (2+codeWires k))) :
    List (NativeOccupation (k+1)) → BinaryGeneratedRun (2+codeWires k)
  | [] => ⟨⟨[],fun _ => 0⟩,[]⟩
  | x::xs =>
    let branch:=binaryNativeBranchRun plans x
    let tail:=binaryNativeBranchTableRun plans xs
    ⟨⟨branch.result.word++tail.result.word,fun i => branch.result.work i+tail.result.work i⟩,
      branch.programs++tail.programs⟩


theorem binaryNativeBranchTableRun_result {k : ℕ} (plans : List (PreparedPauliPlan (2+codeWires k)))
    (xs : List (NativeOccupation (k+1))) :
    (binaryNativeBranchTableRun plans xs).result=preparedNativeBranchTableRun plans xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [binaryNativeBranchTableRun,preparedNativeBranchTableRun,binaryNativeBranchRun_result,ih]


theorem binaryNativeBranchTableRun_encodingActions {k : ℕ} (plans : List (PreparedPauliPlan (2+codeWires k)))
    (xs : List (NativeOccupation (k+1))) :
    (binaryNativeBranchTableRun plans xs).encodingActions≤204*(k+4)^6*xs.length := by
  induction xs with
  | nil => exact le_refl 0
  | cons x xs ih =>
    change binaryRankProgramsActions ((binaryNativeBranchRun plans x).programs++_)≤_
    rw [binaryRankProgramsActions_append]
    exact (Nat.add_le_add (binaryNativeBranchRun_encodingActions plans x) ih).trans_eq
      (by simp only [List.length_cons];ring)

end EffectiveEncoding
