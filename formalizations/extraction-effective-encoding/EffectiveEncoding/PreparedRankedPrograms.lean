import EffectiveEncoding.PreparedGrayCompiler

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

/-- The same executed endpoint/mass records, compiled with a caller-supplied
shared Pauli context rather than rebuilding the mask table at every phase. -/
def preparedIndexedRun {ι : Type*} [Fintype ι] [LinearOrder ι] {n : ℕ}
    (plans : List (PreparedPauliPlan n))
    (E : ι → EncodedEndpoint n) (c : ι → ℕ) (p : ι) (j : ℕ) : RankedBranchRun n :=
  let pivot:=E p
  let initialMass:=c p
  let others:=((Finset.univ.erase p).attach.sort (·≤·)).map (fun a => (E a.1,c a.1))
  ⟨preparedCompileRaw plans (packedEntryProgram pivot.point
      (others.map (fun a => (a.1.point,a.2))) initialMass j),
    fun i => pivot.work i+endpointMassWork others i⟩


theorem preparedIndexedRun_eq {ι : Type*} [Fintype ι] [LinearOrder ι] {n : ℕ}
    (hn : 0<n) (E : ι → EncodedEndpoint n) (c : ι → ℕ) (p : ι) (j : ℕ) :
    preparedIndexedRun (preparedMaskTable hn) E c p j=rankedIndexedRun hn E c p j := by
  simp only [preparedIndexedRun,rankedIndexedRun,preparedCompileRaw_eq]


def preparedRankedAlignmentRun {ι : Type*} {n : ℕ}
    (plans : List (PreparedPauliPlan n)) (E F : ι → EncodedEndpoint n) :
    List ι → List (PackedBits n×PackedBits n) → RankedAlignmentRun n
  | [],_ => ⟨⟨[],0,0⟩,fun _ => 0⟩
  | a::as,ss =>
    let source:=E a
    let evaluated:=applyPackedSwaps ss source.point
    let target:=F a
    let headCode:=preparedSwapCode plans (unpackBits evaluated.1) (unpackBits target.point)
    let tail:=preparedRankedAlignmentRun plans E F as ((evaluated.1,target.point)::ss)
    ⟨⟨headCode++tail.result.word,evaluated.2+tail.result.swapApplications,
      2*n+tail.result.endpointCoordinates⟩,
      fun i => source.work i+target.work i+tail.work i⟩


theorem preparedRankedAlignmentRun_eq {ι : Type*} {n : ℕ} (hn : 0<n)
    (E F : ι → EncodedEndpoint n) (xs : List ι) (ss : List (PackedBits n×PackedBits n)) :
    preparedRankedAlignmentRun (preparedMaskTable hn) E F xs ss=rankedAlignmentRun hn E F xs ss := by
  induction xs generalizing ss with
  | nil => rfl
  | cons a xs ih => simp only [preparedRankedAlignmentRun,rankedAlignmentRun,preparedSwapCode_eq,ih]


def preparedNativeBranchRun {k : ℕ} (plans : List (PreparedPauliPlan (2+codeWires k)))
    (x : NativeOccupation (k+1)) : RankedBranchRun (2+codeWires k) :=
  letI : Fintype {a : Fin 4 // a∈nativeOccupationValue x}:=nativeOccupiedFintype x
  preparedIndexedRun plans (nativeBranchEndpoint x) (fun a => nativeMass x a.1)
    (nativeOccupiedPivot x) (k+1)


theorem preparedNativeBranchRun_eq {k : ℕ} (x : NativeOccupation (k+1)) :
    preparedNativeBranchRun (preparedMaskTable (by omega)) x=nativeBranchRun x := by
  simp only [preparedNativeBranchRun,nativeBranchRun,preparedIndexedRun_eq]

end EffectiveEncoding
