import EffectiveEncoding.AcceptedOccupationLetters
import EffectiveEncoding.CandidateDescriptorGeneration
import EffectiveEncoding.ListPauliPlanProgram

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

/-- Proof-only bridge for the old doubly attached enumeration. -/
theorem attachedSort_values {α : Type*} [LinearOrder α] (S : Finset α) :
    (S.attach.sort (·≤·)).map Subtype.val=S.sort (·≤·) := by
  let e : S ↪ α:=⟨Subtype.val,Subtype.val_injective⟩
  have he : S.attach.map e=S := by ext a;simp [e]
  have h:=Finset.map_sort e S.attach (·≤·) (·≤·) (by intro a ha b hb;rfl)
  simpa only [he,e,Function.Embedding.coeFn_mk] using h

/-- Explicit pivot/head and remaining-list compilation. No Fintype, finite-set
 erase, sorting or minimum is evaluated by this runtime definition. -/
def listIndexedCandidateRun {ι : Type*} {n : ℕ} (plans : List (PreparedPauliPlan n))
    (E : ι → CandidateRankEndpoint n) (c : ι → ℕ) (j : ℕ) : List ι → CandidateWordRun n
  | [] => ⟨[],[]⟩
  | p::ps =>
    let pivot:=E p
    let initialMass:=c p
    let others:=ps.map (fun a => (E a,c a))
    ⟨preparedCompileRaw plans (packedEntryProgram pivot.point
        (others.map (fun a => (a.1.point,a.2))) initialMass j),
      pivot.ranks++others.flatMap (fun a => a.1.ranks)⟩

/-- Whole word/rank-record equality, with Finset operations used only by this
 correctness specification. -/
theorem listIndexedCandidateRun_eq {ι : Type*} [Fintype ι] [LinearOrder ι] {n : ℕ}
    (plans : List (PreparedPauliPlan n)) (E : ι → CandidateRankEndpoint n)
    (c : ι → ℕ) (j : ℕ) (p : ι) (ps : List ι)
    (hs : (Finset.univ : Finset ι).sort (·≤·)=p::ps) :
    listIndexedCandidateRun plans E c j (p::ps)=candidateIndexedRun plans E c p j := by
  have ht:=sortedList_head_erase (Finset.univ : Finset ι) p ps hs
  have ho:=congrArg (List.map (fun a => (E a,c a))) (attachedSort_values (Finset.univ.erase p))
  simp only [List.map_map,Function.comp_def,ht] at ho
  simp only [listIndexedCandidateRun,candidateIndexedRun,ho]

/-- Only finite letter payloads and erased membership proofs are constructed.
 The semantic occupation and set membership in the argument type are erased. -/
def typedOccupationLetters {k : ℕ} (x : NativeOccupation k) (letters : List (Fin 4))
    (hs : letters=(nativeSelected x).sort (·≤·)) :
    List {a : Fin 4 // a∈nativeOccupationValue x} :=
  letters.attach.map (fun a => ⟨a.1,(nativeSelected_mem x a.1).mp
    ((Finset.mem_sort (·≤·)).mp (by rw [←hs];exact a.2))⟩)


theorem typedOccupationLetters_values {k : ℕ} (x : NativeOccupation k) (letters : List (Fin 4))
    (hs : letters=(nativeSelected x).sort (·≤·)) :
    (typedOccupationLetters x letters hs).map Subtype.val=letters := by
  simp only [typedOccupationLetters,List.map_map,Function.comp_def]
  simpa using (List.attach_map_val (l := letters) (f := id))


theorem typedOccupationLetters_sorted {k : ℕ} (x : NativeOccupation k) (letters : List (Fin 4))
    (hs : letters=(nativeSelected x).sort (·≤·)) :
    letI : Fintype {a : Fin 4 // a∈nativeOccupationValue x}:=nativeOccupiedFintype x
    typedOccupationLetters x letters hs=(Finset.univ : Finset {a : Fin 4 // a∈nativeOccupationValue x}).sort (·≤·) := by
  letI : Fintype {a : Fin 4 // a∈nativeOccupationValue x}:=nativeOccupiedFintype x
  apply List.map_injective_iff.mpr Subtype.val_injective
  rw [typedOccupationLetters_values,hs]
  let e : {a : Fin 4 // a∈nativeOccupationValue x} ↪ Fin 4:=⟨Subtype.val,Subtype.val_injective⟩
  have he : (Finset.univ : Finset {a : Fin 4 // a∈nativeOccupationValue x}).map e=nativeSelected x := by
    ext a
    simp only [Finset.mem_map,Finset.mem_univ,true_and,nativeSelected_mem]
    constructor
    · rintro ⟨b,rfl⟩;exact b.2
    · intro ha;exact ⟨⟨a,ha⟩,rfl⟩
  have h:=Finset.map_sort e (Finset.univ : Finset {a : Fin 4 // a∈nativeOccupationValue x})
    (·≤·) (·≤·) (by intro a ha b hb;rfl)
  simpa only [he,e,Function.Embedding.coeFn_mk] using h.symm


theorem typedOccupationLetters_head {k : ℕ} (x : NativeOccupation (k+1)) (letters : List (Fin 4))
    (hs : letters=(nativeSelected x).sort (·≤·))
    (p : {a : Fin 4 // a∈nativeOccupationValue x}) (ps : List {a : Fin 4 // a∈nativeOccupationValue x})
    (hp : typedOccupationLetters x letters hs=p::ps) : p=nativeOccupiedPivot x := by
  have hv:=typedOccupationLetters_values x letters hs
  rw [hp,List.map_cons] at hv
  have hh : (nativeSelected x).sort (·≤·)=p.1::ps.map Subtype.val := by rw [←hs,←hv]
  apply Subtype.ext
  exact (sortedList_head_min (nativeSelected x) p.1 (ps.map Subtype.val)
    ⟨p.1,(nativeSelected_mem x p.1).mpr p.2⟩ hh).symm

/-- Actual list selector output controls this branch. Erased sortedness proofs
 transport membership only; no old finite-set selection or enumeration runs. -/
def storedLettersBranchRun {k : ℕ} (plans : List (PreparedPauliPlan (2+codeWires k)))
    (x : NativeOccupation (k+1)) (letters : List (Fin 4))
    (hs : letters=(nativeSelected x).sort (·≤·)) : CandidateWordRun (2+codeWires k) :=
  listIndexedCandidateRun plans (candidateNativeBranchEndpoint x) (fun a => nativeMass x a.1) (k+1)
    (typedOccupationLetters x letters hs)


theorem storedLettersBranchRun_common {k : ℕ} (plans : List (PreparedPauliPlan (2+codeWires k)))
    (x : NativeOccupation (k+1)) (letters : List (Fin 4))
    (hs : letters=(nativeSelected x).sort (·≤·)) :
    storedLettersBranchRun plans x letters hs=candidateNativeBranchRun plans x := by
  letI : Fintype {a : Fin 4 // a∈nativeOccupationValue x}:=nativeOccupiedFintype x
  have hu:=typedOccupationLetters_sorted x letters hs
  cases hl : typedOccupationLetters x letters hs with
  | nil =>
    have hz : (Finset.univ : Finset {a : Fin 4 // a∈nativeOccupationValue x}).sort (·≤·)=[] := by rw [←hu,hl]
    have hp:=Finset.mem_sort (·≤·) |>.mpr (Finset.mem_univ (nativeOccupiedPivot x))
    rw [hz] at hp
    exact False.elim (List.not_mem_nil hp)
  | cons p ps =>
    have hp:=typedOccupationLetters_head x letters hs p ps hl
    have he : (Finset.univ : Finset {a : Fin 4 // a∈nativeOccupationValue x}).sort (·≤·)=p::ps := by rw [←hu,hl]
    unfold storedLettersBranchRun
    rw [hl,listIndexedCandidateRun_eq plans _ _ _ p ps he,hp]
    rfl


theorem typedOccupationLetters_nonempty {k : ℕ} (x : NativeOccupation (k+1)) (letters : List (Fin 4))
    (hs : letters=(nativeSelected x).sort (·≤·)) : typedOccupationLetters x letters hs≠[] := by
  intro he
  have hv:=typedOccupationLetters_values x letters hs
  rw [he,List.map_nil] at hv
  obtain ⟨a,ha⟩:=Sym.exists_mem (nativeOccupationValue x)
  have hm:=(Finset.mem_sort (·≤·)).mpr ((nativeSelected_mem x a).mpr ha)
  rw [←hs,←hv] at hm
  exact List.not_mem_nil hm

/-- The actual head of the retained selector list determines the alignment
 pivot. No Nat/minimum comparison is invoked to recover that endpoint. -/
def storedLettersPivotEndpoint {k : ℕ} (x : NativeOccupation (k+1)) (letters : List (Fin 4))
    (hs : letters=(nativeSelected x).sort (·≤·)) : CandidateRankEndpoint (2+codeWires k) :=
  candidateNativeBranchEndpoint x ((typedOccupationLetters x letters hs).head
    (typedOccupationLetters_nonempty x letters hs))


theorem storedLettersPivotEndpoint_common {k : ℕ} (x : NativeOccupation (k+1)) (letters : List (Fin 4))
    (hs : letters=(nativeSelected x).sort (·≤·)) :
    storedLettersPivotEndpoint x letters hs=candidateNativePivotEndpoint x := by
  cases hl : typedOccupationLetters x letters hs with
  | nil => exact False.elim (typedOccupationLetters_nonempty x letters hs hl)
  | cons p ps =>
    have hp:=typedOccupationLetters_head x letters hs p ps hl
    simp only [storedLettersPivotEndpoint,hl,List.head_cons,hp,candidateNativePivotEndpoint]


def storedLettersBranchTableRun {k : ℕ} (plans : List (PreparedPauliPlan (2+codeWires k))) :
    (xs : List (AcceptedOccupationLettersResult (k+1))) →
    (∀ r∈xs,r.letters.items=(nativeSelected r.native).sort (·≤·)) → CandidateWordRun (2+codeWires k)
  | [],_ => ⟨[],[]⟩
  | r::rs,h =>
    let branch:=storedLettersBranchRun plans r.native r.letters.items (h r (by simp))
    let tail:=storedLettersBranchTableRun plans rs (fun a ha => h a (by simp [ha]))
    ⟨branch.word++tail.word,branch.ranks++tail.ranks⟩


theorem storedLettersBranchTableRun_common {k : ℕ} (plans : List (PreparedPauliPlan (2+codeWires k)))
    (xs : List (AcceptedOccupationLettersResult (k+1)))
    (h : ∀ r∈xs,r.letters.items=(nativeSelected r.native).sort (·≤·)) :
    storedLettersBranchTableRun plans xs h=candidateBranchTableRun plans (xs.map AcceptedOccupationLettersResult.native) := by
  induction xs with
  | nil => rfl
  | cons r rs ih =>
    simp only [storedLettersBranchTableRun,candidateBranchTableRun,List.map_cons,storedLettersBranchRun_common,ih]

/-- The same stored-swap algorithm, now selecting each source pivot from the
 same retained Boolean letter-list result used by its branch compiler. -/
def storedLettersAlignmentRun {k : ℕ} (plans : List (PreparedPauliPlan (2+codeWires k))) :
    (xs : List (AcceptedOccupationLettersResult (k+1))) →
    (∀ r∈xs,r.letters.items=(nativeSelected r.native).sort (·≤·)) →
    List (PackedBits (2+codeWires k)×PackedBits (2+codeWires k)) → CandidateWordRun (2+codeWires k)
  | [],_,_ => ⟨[],[]⟩
  | r::rs,h,ss =>
    let source:=storedLettersPivotEndpoint r.native r.letters.items (h r (by simp))
    let evaluated:=applyPackedSwaps ss source.point
    let target:=candidateNativeNextEndpoint r.native
    let headCode:=preparedSwapCode plans (unpackBits evaluated.1) (unpackBits target.point)
    let tail:=storedLettersAlignmentRun plans rs (fun a ha => h a (by simp [ha])) ((evaluated.1,target.point)::ss)
    ⟨headCode++tail.word,source.ranks++target.ranks++tail.ranks⟩


theorem storedLettersAlignmentRun_common {k : ℕ} (plans : List (PreparedPauliPlan (2+codeWires k)))
    (xs : List (AcceptedOccupationLettersResult (k+1)))
    (h : ∀ r∈xs,r.letters.items=(nativeSelected r.native).sort (·≤·))
    (ss : List (PackedBits (2+codeWires k)×PackedBits (2+codeWires k))) :
    storedLettersAlignmentRun plans xs h ss=
      candidateAlignmentRun plans candidateNativePivotEndpoint candidateNativeNextEndpoint
        (xs.map AcceptedOccupationLettersResult.native) ss := by
  induction xs generalizing ss with
  | nil => rfl
  | cons r rs ih =>
    simp only [storedLettersAlignmentRun,candidateAlignmentRun,List.map_cons,storedLettersPivotEndpoint_common,ih]

end EffectiveEncoding
