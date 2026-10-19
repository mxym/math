import EffectiveEncoding.CandidateNativeTable
import EffectiveEncoding.BooleanRankGenerationPrograms

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

structure CandidateWordRun (n : ℕ) where
  word : WordCode n
  ranks : List CandidateRankRecord


def CandidateWordRun.actions {n : ℕ} (r : CandidateWordRun n) : ℕ :=
  candidateRankRecordsActions r.ranks


theorem candidateEndpointMassActions {n : ℕ} (xs : List (CandidateRankEndpoint n×ℕ))
    (B : ℕ) (h : ∀ a∈xs,a.1.actions≤B) :
    candidateRankRecordsActions (xs.flatMap (fun a => a.1.ranks))≤xs.length*B := by
  induction xs with
  | nil => simp [candidateRankRecordsActions]
  | cons a as ih =>
    have ha:=h a (by simp)
    have ht:=ih (fun a ha => h a (by simp [ha]))
    simp only [List.flatMap_cons,candidateRankRecordsActions_append,List.length_cons]
    exact (Nat.add_le_add ha ht).trans_eq (by ring)

/-- Endpoints and masses are evaluated once and stored. Old logical rank-work
metadata is not computed to emit the word. The retained ranks are those used
by this actual compile call. Gray/AST/control fees are still separate. -/
def candidateIndexedRun {ι : Type*} [Fintype ι] [LinearOrder ι] {n : ℕ}
    (plans : List (PreparedPauliPlan n)) (E : ι → CandidateRankEndpoint n)
    (c : ι → ℕ) (p : ι) (j : ℕ) : CandidateWordRun n :=
  let pivot:=E p
  let initialMass:=c p
  let others:=((Finset.univ.erase p).attach.sort (·≤·)).map (fun a => (E a.1,c a.1))
  ⟨preparedCompileRaw plans (packedEntryProgram pivot.point
    (others.map (fun a => (a.1.point,a.2))) initialMass j),
    pivot.ranks++others.flatMap (fun a => a.1.ranks)⟩


theorem candidateIndexedRun_word {ι : Type*} [Fintype ι] [LinearOrder ι] {n : ℕ}
    (plans : List (PreparedPauliPlan n)) (E : ι → CandidateRankEndpoint n)
    (F : ι → ScannedEncodedEndpoint n) (c : ι → ℕ) (p : ι) (j : ℕ)
    (he : ∀ a,(E a).point=(F a).binary.endpoint.point) :
    (candidateIndexedRun plans E c p j).word=(scannedIndexedRun plans F c p j).result.result.word := by
  simp only [candidateIndexedRun,scannedIndexedRun,List.map_map,Function.comp_def,he]


theorem candidateIndexedRun_actions {ι : Type*} [Fintype ι] [LinearOrder ι] {n : ℕ}
    (plans : List (PreparedPauliPlan n)) (E : ι → CandidateRankEndpoint n)
    (c : ι → ℕ) (p : ι) (j B : ℕ) (hE : ∀ a,(E a).actions≤B) :
    (candidateIndexedRun plans E c p j).actions≤Fintype.card ι*B := by
  let xs:=((Finset.univ.erase p).attach.sort (·≤·)).map (fun a => (E a.1,c a.1))
  have hs : candidateRankRecordsActions (xs.flatMap (fun a => a.1.ranks))≤xs.length*B := by
    apply candidateEndpointMassActions
    intro a ha
    obtain ⟨a,ha,rfl⟩:=List.mem_map.mp ha
    exact hE a.1
  have hl : xs.length+1=Fintype.card ι := by
    have hc : 0<Fintype.card ι := Fintype.card_pos_iff.mpr ⟨p⟩
    simp only [xs,List.length_map,Finset.length_sort,Finset.card_attach,
      Finset.card_erase_of_mem (Finset.mem_univ p),Finset.card_univ]
    omega
  change candidateRankRecordsActions ((E p).ranks++xs.flatMap (fun a => a.1.ranks))≤_
  rw [candidateRankRecordsActions_append]
  exact (Nat.add_le_add (hE p) hs).trans_eq (by rw [←hl];ring)


def candidateNativeBranchRun {k : ℕ} (plans : List (PreparedPauliPlan (2+codeWires k)))
    (x : NativeOccupation (k+1)) : CandidateWordRun (2+codeWires k) :=
  letI : Fintype {a : Fin 4 // a∈nativeOccupationValue x}:=nativeOccupiedFintype x
  candidateIndexedRun plans (candidateNativeBranchEndpoint x) (fun a => nativeMass x a.1)
    (nativeOccupiedPivot x) (k+1)


theorem candidateNativeBranchRun_word {k : ℕ} (plans : List (PreparedPauliPlan (2+codeWires k)))
    (x : NativeOccupation (k+1)) :
    (candidateNativeBranchRun plans x).word=(scannedNativeBranchRun plans x).result.result.word := by
  letI : Fintype {a : Fin 4 // a∈nativeOccupationValue x}:=nativeOccupiedFintype x
  exact candidateIndexedRun_word plans _ _ _ _ _ (candidateNativeBranchEndpoint_point x)


theorem candidateNativeBranchRun_actions {k : ℕ} (plans : List (PreparedPauliPlan (2+codeWires k)))
    (x : NativeOccupation (k+1)) : (candidateNativeBranchRun plans x).actions≤2204*(k+5)^6 := by
  letI : Fintype {a : Fin 4 // a∈nativeOccupationValue x}:=nativeOccupiedFintype x
  have h:=candidateIndexedRun_actions plans (candidateNativeBranchEndpoint x) (fun a => nativeMass x a.1)
    (nativeOccupiedPivot x) (k+1) (551*(k+5)^6) (candidateNativeBranchEndpoint_actions x)
  have hc : Fintype.card {a : Fin 4 // a∈nativeOccupationValue x}≤4 :=
    Fintype.card_le_of_injective (fun a : {a : Fin 4 // a∈nativeOccupationValue x} => a.1) Subtype.val_injective
  exact h.trans ((Nat.mul_le_mul_right _ hc).trans_eq (by ring))

/-- The same stored-swap source algorithm, now fed by genuine binary-generated
rank endpoints. Each actual endpoint record persists; no old Nat table filter
is invoked to reconstruct logical work metadata. -/
def candidateAlignmentRun {ι : Type*} {n : ℕ} (plans : List (PreparedPauliPlan n))
    (E F : ι → CandidateRankEndpoint n) :
    List ι → List (PackedBits n×PackedBits n) → CandidateWordRun n
  | [],_ => ⟨[],[]⟩
  | a::as,ss =>
    let source:=E a
    let evaluated:=applyPackedSwaps ss source.point
    let target:=F a
    let headCode:=preparedSwapCode plans (unpackBits evaluated.1) (unpackBits target.point)
    let tail:=candidateAlignmentRun plans E F as ((evaluated.1,target.point)::ss)
    ⟨headCode++tail.word,source.ranks++target.ranks++tail.ranks⟩


theorem candidateAlignmentRun_word {ι : Type*} {n : ℕ} (plans : List (PreparedPauliPlan n))
    (E F : ι → CandidateRankEndpoint n) (G H : ι → ScannedEncodedEndpoint n)
    (xs : List ι) (ss : List (PackedBits n×PackedBits n))
    (he : ∀ a,(E a).point=(G a).binary.endpoint.point)
    (hf : ∀ a,(F a).point=(H a).binary.endpoint.point) :
    (candidateAlignmentRun plans E F xs ss).word=(scannedAlignmentRun plans G H xs ss).result.result.result.word := by
  induction xs generalizing ss with
  | nil => rfl
  | cons a xs ih => simp only [candidateAlignmentRun,scannedAlignmentRun,he,hf,ih]


theorem candidateAlignmentRun_actions {ι : Type*} {n : ℕ} (plans : List (PreparedPauliPlan n))
    (E F : ι → CandidateRankEndpoint n) (xs : List ι) (ss : List (PackedBits n×PackedBits n))
    (B : ℕ) (he : ∀ a,(E a).actions≤B) (hf : ∀ a,(F a).actions≤B) :
    (candidateAlignmentRun plans E F xs ss).actions≤2*B*xs.length := by
  induction xs generalizing ss with
  | nil => exact le_refl 0
  | cons a xs ih =>
    have ht:=ih (((applyPackedSwaps ss (E a).point).1,(F a).point)::ss)
    change candidateRankRecordsActions ((E a).ranks++(F a).ranks++_)≤_
    rw [candidateRankRecordsActions_append,candidateRankRecordsActions_append]
    exact (Nat.add_le_add (Nat.add_le_add (he a) (hf a)) ht).trans_eq (by simp only [List.length_cons];ring)

end EffectiveEncoding
