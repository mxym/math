import EffectiveEncoding.BinaryRankGenerationRecords

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

structure BinaryGeneratedRun (n : ℕ) where
  result : RankedBranchRun n
  programs : List BinaryRankProgramRecord


def BinaryGeneratedRun.encodingActions {n : ℕ} (r : BinaryGeneratedRun n) : ℕ :=
  binaryRankProgramsActions r.programs


theorem binaryEndpointMassActions_bound {n : ℕ} (xs : List (BinaryEncodedEndpoint n×ℕ))
    (B : ℕ) (h : ∀ a∈xs,a.1.encodingActions≤B) :
    binaryRankProgramsActions (xs.flatMap (fun a => a.1.programs))≤xs.length*B := by
  induction xs with
  | nil => simp [binaryRankProgramsActions]
  | cons a as ih =>
    have ha:=h a (by simp)
    have ht:=ih (fun a ha => h a (by simp [ha]))
    simp only [List.flatMap_cons,binaryRankProgramsActions_append,List.length_cons]
    exact (Nat.add_le_add ha ht).trans_eq (by ring)

/-- Same prepared compiler, retaining every executed rank-bit program. -/
def binaryIndexedRun {ι : Type*} [Fintype ι] [LinearOrder ι] {n : ℕ}
    (plans : List (PreparedPauliPlan n)) (E : ι → BinaryEncodedEndpoint n)
    (c : ι → ℕ) (p : ι) (j : ℕ) : BinaryGeneratedRun n :=
  let pivot:=E p
  let initialMass:=c p
  let others:=((Finset.univ.erase p).attach.sort (·≤·)).map (fun a => (E a.1,c a.1))
  ⟨⟨preparedCompileRaw plans (packedEntryProgram pivot.endpoint.point
      (others.map (fun a => (a.1.endpoint.point,a.2))) initialMass j),
    fun i => pivot.endpoint.work i+endpointMassWork (others.map (fun a => (a.1.endpoint,a.2))) i⟩,
    pivot.programs++others.flatMap (fun a => a.1.programs)⟩


theorem binaryIndexedRun_result {ι : Type*} [Fintype ι] [LinearOrder ι] {n : ℕ}
    (plans : List (PreparedPauliPlan n)) (E : ι → BinaryEncodedEndpoint n)
    (c : ι → ℕ) (p : ι) (j : ℕ) :
    (binaryIndexedRun plans E c p j).result=preparedIndexedRun plans (fun a => (E a).endpoint) c p j := by
  simp only [binaryIndexedRun,preparedIndexedRun,List.map_map,Function.comp_def]


theorem binaryIndexedRun_encodingActions {ι : Type*} [Fintype ι] [LinearOrder ι] {n : ℕ}
    (plans : List (PreparedPauliPlan n)) (E : ι → BinaryEncodedEndpoint n)
    (c : ι → ℕ) (p : ι) (j B : ℕ) (hE : ∀ a,(E a).encodingActions≤B) :
    (binaryIndexedRun plans E c p j).encodingActions≤Fintype.card ι*B := by
  let xs:=((Finset.univ.erase p).attach.sort (·≤·)).map (fun a => (E a.1,c a.1))
  have hs : binaryRankProgramsActions (xs.flatMap (fun a => a.1.programs))≤xs.length*B := by
    apply binaryEndpointMassActions_bound
    intro a ha
    obtain ⟨a,ha,rfl⟩:=List.mem_map.mp ha
    exact hE a.1
  have hl : xs.length+1=Fintype.card ι := by
    have hc : 0<Fintype.card ι := Fintype.card_pos_iff.mpr ⟨p⟩
    simp only [xs,List.length_map,Finset.length_sort,Finset.card_attach,
      Finset.card_erase_of_mem (Finset.mem_univ p),Finset.card_univ]
    omega
  change binaryRankProgramsActions ((E p).programs++xs.flatMap (fun a => a.1.programs))≤_
  rw [binaryRankProgramsActions_append]
  exact (Nat.add_le_add (hE p) hs).trans_eq (by rw [←hl];ring)


def binaryNativeBranchRun {k : ℕ} (plans : List (PreparedPauliPlan (2+codeWires k)))
    (x : NativeOccupation (k+1)) : BinaryGeneratedRun (2+codeWires k) :=
  letI : Fintype {a : Fin 4 // a∈nativeOccupationValue x}:=nativeOccupiedFintype x
  binaryIndexedRun plans (binaryNativeBranchEndpoint x) (fun a => nativeMass x a.1)
    (nativeOccupiedPivot x) (k+1)


theorem binaryNativeBranchRun_result {k : ℕ} (plans : List (PreparedPauliPlan (2+codeWires k)))
    (x : NativeOccupation (k+1)) :
    (binaryNativeBranchRun plans x).result=preparedNativeBranchRun plans x := by
  have he : (fun a => (binaryNativeBranchEndpoint x a).endpoint)=nativeBranchEndpoint x :=
    funext (binaryNativeBranchEndpoint_endpoint x)
  simp only [binaryNativeBranchRun,preparedNativeBranchRun,binaryIndexedRun_result,he]


theorem binaryNativeBranchRun_encodingActions {k : ℕ} (plans : List (PreparedPauliPlan (2+codeWires k)))
    (x : NativeOccupation (k+1)) :
    (binaryNativeBranchRun plans x).encodingActions≤204*(k+4)^6 := by
  letI : Fintype {a : Fin 4 // a∈nativeOccupationValue x}:=nativeOccupiedFintype x
  have h:=binaryIndexedRun_encodingActions plans (binaryNativeBranchEndpoint x) (fun a => nativeMass x a.1)
    (nativeOccupiedPivot x) (k+1) (51*(k+4)^6) (fun a =>
      (binaryNativeBranchEndpoint_encodingActions x a).trans
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 6)))
  have hc : Fintype.card {a : Fin 4 // a∈nativeOccupationValue x}≤4 :=
    Fintype.card_le_of_injective (fun a : {a : Fin 4 // a∈nativeOccupationValue x} => a.1) Subtype.val_injective
  exact h.trans ((Nat.mul_le_mul_right _ hc).trans_eq (by ring))

end EffectiveEncoding
