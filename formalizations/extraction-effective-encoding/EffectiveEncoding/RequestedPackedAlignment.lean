import EffectiveEncoding.PackedSwapAlignment

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

structure RequestedAlignmentRun (n : ℕ) where
  result : PackedAlignmentRun n
  embeddingRequests : ℕ

/-- Explicit one-source/one-target callback requests per recursive step.
This retains the same packed endpoint and swap evaluation strategy. -/
def requestedAlignmentRun {ι : Type*} {n : ℕ} (hn : 0<n) (e f : ι ↪ Bits n) :
    List ι → List (PackedBits n×PackedBits n) → RequestedAlignmentRun n
  | [],_ => ⟨⟨[],0,0⟩,0⟩
  | i::is,ss =>
    let sourceFunction:=e i
    let source:=packBits sourceFunction
    let evaluated:=applyPackedSwaps ss source
    let a:=evaluated.1
    let targetFunction:=f i
    let b:=packBits targetFunction
    let headCode:=swapCode hn (unpackBits a) (unpackBits b)
    let tail:=requestedAlignmentRun hn e f is ((a,b)::ss)
    ⟨⟨headCode++tail.result.word,evaluated.2+tail.result.swapApplications,
      2*n+tail.result.endpointCoordinates⟩,1+1+tail.embeddingRequests⟩


theorem requestedAlignmentRun_result {ι : Type*} {n : ℕ} (hn : 0<n) (e f : ι ↪ Bits n)
    (xs : List ι) (ss : List (PackedBits n×PackedBits n)) :
    (requestedAlignmentRun hn e f xs ss).result=packedAlignmentRun hn e f xs ss := by
  induction xs generalizing ss with
  | nil => rfl
  | cons i xs ih => simp only [requestedAlignmentRun,packedAlignmentRun,ih]


theorem requestedAlignmentRun_requests {ι : Type*} {n : ℕ} (hn : 0<n) (e f : ι ↪ Bits n)
    (xs : List ι) (ss : List (PackedBits n×PackedBits n)) :
    (requestedAlignmentRun hn e f xs ss).embeddingRequests=2*xs.length := by
  induction xs generalizing ss with
  | nil => rfl
  | cons i xs ih => simp only [requestedAlignmentRun,ih,List.length_cons];omega

end EffectiveEncoding
