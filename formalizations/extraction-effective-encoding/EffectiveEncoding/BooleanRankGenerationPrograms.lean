import EffectiveEncoding.BooleanRankEndpoints
import EffectiveEncoding.BinaryRankAlignmentPrograms

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

structure ScannedGeneratedRun (n : ℕ) where
  result : BinaryGeneratedRun n
  scans : List BooleanRankRecord

def ScannedGeneratedRun.scanActions {n : ℕ} (r : ScannedGeneratedRun n) : ℕ :=
  booleanRankRecordsActions r.scans


theorem scannedEndpointMassActions_bound {n : ℕ} (xs : List (ScannedEncodedEndpoint n×ℕ))
    (B : ℕ) (h : ∀ a∈xs,a.1.scanActions≤B) :
    booleanRankRecordsActions (xs.flatMap (fun a => a.1.scans))≤xs.length*B := by
  induction xs with
  | nil => simp [booleanRankRecordsActions]
  | cons a as ih =>
    have ha:=h a (by simp)
    have ht:=ih (fun a ha => h a (by simp [ha]))
    simp only [List.flatMap_cons,booleanRankRecordsActions_append,List.length_cons]
    exact (Nat.add_le_add ha ht).trans_eq (by ring)

/-- Endpoint/mass records and both kinds of executed bit traces are retained
once; compilation only reads those same stored endpoint values. -/
def scannedIndexedRun {ι : Type*} [Fintype ι] [LinearOrder ι] {n : ℕ}
    (plans : List (PreparedPauliPlan n)) (E : ι → ScannedEncodedEndpoint n)
    (c : ι → ℕ) (p : ι) (j : ℕ) : ScannedGeneratedRun n :=
  let pivot:=E p
  let initialMass:=c p
  let others:=((Finset.univ.erase p).attach.sort (·≤·)).map (fun a => (E a.1,c a.1))
  ⟨⟨⟨preparedCompileRaw plans (packedEntryProgram pivot.binary.endpoint.point
      (others.map (fun a => (a.1.binary.endpoint.point,a.2))) initialMass j),
    fun i => pivot.binary.endpoint.work i+endpointMassWork (others.map (fun a => (a.1.binary.endpoint,a.2))) i⟩,
    pivot.binary.programs++others.flatMap (fun a => a.1.binary.programs)⟩,
    pivot.scans++others.flatMap (fun a => a.1.scans)⟩


theorem scannedIndexedRun_result {ι : Type*} [Fintype ι] [LinearOrder ι] {n : ℕ}
    (plans : List (PreparedPauliPlan n)) (E : ι → ScannedEncodedEndpoint n) (c : ι → ℕ) (p : ι) (j : ℕ) :
    (scannedIndexedRun plans E c p j).result=binaryIndexedRun plans (fun a => (E a).binary) c p j := by
  simp only [scannedIndexedRun,binaryIndexedRun,List.map_map,List.flatMap_map,Function.comp_def]


theorem scannedIndexedRun_scanActions {ι : Type*} [Fintype ι] [LinearOrder ι] {n : ℕ}
    (plans : List (PreparedPauliPlan n)) (E : ι → ScannedEncodedEndpoint n)
    (c : ι → ℕ) (p : ι) (j B : ℕ) (hE : ∀ a,(E a).scanActions≤B) :
    (scannedIndexedRun plans E c p j).scanActions≤Fintype.card ι*B := by
  let xs:=((Finset.univ.erase p).attach.sort (·≤·)).map (fun a => (E a.1,c a.1))
  have hs : booleanRankRecordsActions (xs.flatMap (fun a => a.1.scans))≤xs.length*B := by
    apply scannedEndpointMassActions_bound
    intro a ha
    obtain ⟨a,ha,rfl⟩:=List.mem_map.mp ha
    exact hE a.1
  have hl : xs.length+1=Fintype.card ι := by
    have hc : 0<Fintype.card ι := Fintype.card_pos_iff.mpr ⟨p⟩
    simp only [xs,List.length_map,Finset.length_sort,Finset.card_attach,
      Finset.card_erase_of_mem (Finset.mem_univ p),Finset.card_univ]
    omega
  change booleanRankRecordsActions ((E p).scans++xs.flatMap (fun a => a.1.scans))≤_
  rw [booleanRankRecordsActions_append]
  exact (Nat.add_le_add (hE p) hs).trans_eq (by rw [←hl];ring)


def scannedNativeBranchRun {k : ℕ} (plans : List (PreparedPauliPlan (2+codeWires k)))
    (x : NativeOccupation (k+1)) : ScannedGeneratedRun (2+codeWires k) :=
  letI : Fintype {a : Fin 4 // a∈nativeOccupationValue x}:=nativeOccupiedFintype x
  scannedIndexedRun plans (scannedNativeBranchEndpoint x) (fun a => nativeMass x a.1)
    (nativeOccupiedPivot x) (k+1)


theorem scannedNativeBranchRun_result {k : ℕ} (plans : List (PreparedPauliPlan (2+codeWires k)))
    (x : NativeOccupation (k+1)) : (scannedNativeBranchRun plans x).result=binaryNativeBranchRun plans x := by
  have he : (fun a => (scannedNativeBranchEndpoint x a).binary)=binaryNativeBranchEndpoint x :=
    funext (scannedNativeBranchEndpoint_binary x)
  simp only [scannedNativeBranchRun,binaryNativeBranchRun,scannedIndexedRun_result,he]


theorem scannedNativeBranchRun_scanActions {k : ℕ} (plans : List (PreparedPauliPlan (2+codeWires k)))
    (x : NativeOccupation (k+1)) : (scannedNativeBranchRun plans x).scanActions≤1200*(k+3)^5 := by
  letI : Fintype {a : Fin 4 // a∈nativeOccupationValue x}:=nativeOccupiedFintype x
  have h:=scannedIndexedRun_scanActions plans (scannedNativeBranchEndpoint x) (fun a => nativeMass x a.1)
    (nativeOccupiedPivot x) (k+1) (300*(k+3)^5) (scannedNativeBranchEndpoint_scanActions x)
  have hc : Fintype.card {a : Fin 4 // a∈nativeOccupationValue x}≤4 :=
    Fintype.card_le_of_injective (fun a : {a : Fin 4 // a∈nativeOccupationValue x} => a.1) Subtype.val_injective
  exact h.trans ((Nat.mul_le_mul_right _ hc).trans_eq (by ring))

structure ScannedAlignmentResult (n : ℕ) where
  result : BinaryAlignmentResult n
  scans : List BooleanRankRecord

def ScannedAlignmentResult.scanActions {n : ℕ} (r : ScannedAlignmentResult n) : ℕ :=
  booleanRankRecordsActions r.scans


def scannedAlignmentRun {ι : Type*} {n : ℕ} (plans : List (PreparedPauliPlan n))
    (E F : ι → ScannedEncodedEndpoint n) :
    List ι → List (PackedBits n×PackedBits n) → ScannedAlignmentResult n
  | [],_ => ⟨⟨⟨⟨[],0,0⟩,fun _ => 0⟩,[]⟩,[]⟩
  | a::as,ss =>
    let source:=E a
    let evaluated:=applyPackedSwaps ss source.binary.endpoint.point
    let target:=F a
    let headCode:=preparedSwapCode plans (unpackBits evaluated.1) (unpackBits target.binary.endpoint.point)
    let tail:=scannedAlignmentRun plans E F as ((evaluated.1,target.binary.endpoint.point)::ss)
    ⟨⟨⟨⟨headCode++tail.result.result.result.word,evaluated.2+tail.result.result.result.swapApplications,
      2*n+tail.result.result.result.endpointCoordinates⟩,
      fun i => source.binary.endpoint.work i+target.binary.endpoint.work i+tail.result.result.work i⟩,
      source.binary.programs++target.binary.programs++tail.result.programs⟩,
      source.scans++target.scans++tail.scans⟩


theorem scannedAlignmentRun_result {ι : Type*} {n : ℕ} (plans : List (PreparedPauliPlan n))
    (E F : ι → ScannedEncodedEndpoint n) (xs : List ι) (ss : List (PackedBits n×PackedBits n)) :
    (scannedAlignmentRun plans E F xs ss).result=
      binaryAlignmentRun plans (fun a => (E a).binary) (fun a => (F a).binary) xs ss := by
  induction xs generalizing ss with
  | nil => rfl
  | cons a xs ih => simp only [scannedAlignmentRun,binaryAlignmentRun,ih]


theorem scannedAlignmentRun_scanActions {ι : Type*} {n : ℕ} (plans : List (PreparedPauliPlan n))
    (E F : ι → ScannedEncodedEndpoint n) (xs : List ι) (ss : List (PackedBits n×PackedBits n))
    (B : ℕ) (hE : ∀ a,(E a).scanActions≤B) (hF : ∀ a,(F a).scanActions≤B) :
    (scannedAlignmentRun plans E F xs ss).scanActions≤2*B*xs.length := by
  induction xs generalizing ss with
  | nil => exact le_refl 0
  | cons a xs ih =>
    have ht:=ih (((applyPackedSwaps ss (E a).binary.endpoint.point).1,(F a).binary.endpoint.point)::ss)
    change booleanRankRecordsActions ((E a).scans++(F a).scans++_)≤_
    rw [booleanRankRecordsActions_append,booleanRankRecordsActions_append]
    exact (Nat.add_le_add (Nat.add_le_add (hE a) (hF a)) ht).trans_eq (by simp only [List.length_cons];ring)

end EffectiveEncoding
