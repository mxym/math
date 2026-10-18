import EffectiveEncoding.BooleanMaskCoordinates

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

inductive CnotListTrace where
  | done
  | emit : CnotListTrace → CnotListTrace


def CnotListTrace.actions : CnotListTrace → ℕ
  | .done => 1
  | .emit tail => tail.actions+6

structure CnotListResult (n : ℕ) where
  word : WordCode n
  trace : CnotListTrace

/-- Direct CNOT/list construction. Distinctness proofs are erased; no runtime
finite-set membership or inequality test occurs in this list program. -/
def cnotListProgram {n : ℕ} (target : Fin n) : (xs : List (Fin n)) →
    (∀ j∈xs,j≠target) → CnotListResult n
  | [],_ => ⟨[],.done⟩
  | j::js,h =>
    let gate:=GateCode.cnot j target (h j (by simp))
    let tail:=cnotListProgram target js (fun i hi => h i (by simp [hi]))
    ⟨gate::tail.word,.emit tail.trace⟩


theorem cnotListProgram_word {n : ℕ} (target : Fin n) (xs : List (Fin n)) (h : ∀ j∈xs,j≠target) :
    (cnotListProgram target xs h).word=xs.attach.map (fun j => GateCode.cnot j.1 target (h j.1 j.2)) := by
  induction xs with
  | nil => rfl
  | cons j js ih =>
    simp only [cnotListProgram,List.attach_cons,List.map_cons,List.map_map,Function.comp_def,ih]


theorem cnotListProgram_length {n : ℕ} (target : Fin n) (xs : List (Fin n)) (h : ∀ j∈xs,j≠target) :
    (cnotListProgram target xs h).word.length=xs.length := by
  rw [cnotListProgram_word,List.length_map,List.length_attach]


theorem cnotListProgram_actions {n : ℕ} (target : Fin n) (xs : List (Fin n)) (h : ∀ j∈xs,j≠target) :
    (cnotListProgram target xs h).trace.actions=6*xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons j js ih => simp only [cnotListProgram,CnotListTrace.actions,List.length_cons,ih];omega

/-- Pinned Mathlib sort/minimum bridge, used only by correctness proofs. -/
theorem sortedList_head_min {α : Type*} [LinearOrder α] (S : Finset α) (t : α) (ts : List α)
    (hS : S.Nonempty) (hs : S.sort (·≤·)=t::ts) : S.min' hS=t := by
  rw [Finset.min'_eq_sorted_zero]
  simp only [hs,List.getElem_cons_zero]


theorem sortedList_head_erase {α : Type*} [LinearOrder α] (S : Finset α) (t : α) (ts : List α)
    (hs : S.sort (·≤·)=t::ts) : (S.erase t).sort (·≤·)=ts := by
  have hnd : (t::ts).Nodup := by rw [←hs];exact Finset.sort_nodup _ _
  have hnot : t∉ts := (List.nodup_cons.mp hnd).1
  have hp : List.Pairwise (·<·) (t::ts) := by rw [←hs];exact (Finset.sortedLT_sort S).pairwise
  apply List.Pairwise.eq_of_mem_iff (Finset.sortedLT_sort _).pairwise (List.pairwise_cons.mp hp).2
  intro a
  have hm : a∈S ↔ a∈t::ts := by rw [←hs,Finset.mem_sort]
  constructor
  · intro ha
    rcases Finset.mem_erase.mp ((Finset.mem_sort (·≤·)).mp ha) with ⟨hne,hmS⟩
    exact (List.mem_cons.mp (hm.mp hmS)).resolve_left hne
  · intro ha
    apply (Finset.mem_sort (·≤·)).mpr
    refine Finset.mem_erase.mpr ⟨?_,hm.mpr (List.mem_cons_of_mem _ ha)⟩
    intro he
    subst a
    exact hnot ha

structure ListPauliPlanResult (n : ℕ) where
  plan : PreparedPauliPlan n
  leading : CnotListResult n
  trailing : ListAssemblyResult (GateCode n)

/-- The first selected coordinate is the target, and the remaining list gives
its controls. Head-case selection, actual CNOT construction and reverse-map are
performed once. Sorting/minimum/erase do not occur in this value program. -/
def listPauliPlanProgram {n : ℕ} (hn : 0<n) : (xs : List (Fin n)) → xs.Nodup → ListPauliPlanResult n
  | [],_ =>
    let target : Fin n:=⟨0,hn⟩
    let leading:=cnotListProgram target [] (by simp)
    let trailing:=listReverseMapIntoProgram GateCode.inverse leading.word []
    ⟨⟨target,leading.word,trailing.value,[],false⟩,leading,trailing⟩
  | target::xs,h =>
    let leading:=cnotListProgram target xs (fun j hj => by
      intro he
      subst j
      exact (List.nodup_cons.mp h).1 hj)
    let trailing:=listReverseMapIntoProgram GateCode.inverse leading.word []
    ⟨⟨target,leading.word,trailing.value,target::xs,true⟩,leading,trailing⟩

/-- Entire plan record equality, including target, both CNOT words, ordered
parity coordinates and sign flag. Finsets occur only in this specification. -/
theorem listPauliPlanProgram_plan {n : ℕ} (hn : 0<n) (S : Finset (Fin n))
    (xs : List (Fin n)) (hnd : xs.Nodup) (hs : xs=S.sort (·≤·)) :
    (listPauliPlanProgram hn xs hnd).plan=preparePauliPlan hn S := by
  cases xs with
  | nil =>
    have hS : S=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro a ha
      have hl := (Finset.mem_sort (·≤·)).mpr ha
      rw [←hs] at hl
      exact List.not_mem_nil hl
    subst S
    simp [listPauliPlanProgram,preparePauliPlan,cnotListProgram,listReverseMapIntoProgram ]
  | cons t ts =>
    have hS : S.Nonempty := ⟨t,(Finset.mem_sort (·≤·)).mp (by rw [←hs];simp)⟩
    have ht:=sortedList_head_min S t ts hS hs.symm
    have he:=sortedList_head_erase S t ts hs.symm
    have hl : ∀ h : ∀ j∈ts,j≠t,(cnotListProgram t ts h).word=cnotCode t (controls t S) := by
      intro h
      subst ts
      simp only [cnotListProgram_word,cnotCode,controls,List.map_map,Function.comp_def]
    subst t
    simp only [listPauliPlanProgram,preparePauliPlan,dite_eq_left hS,hl,
      listReverseMapIntoProgram_value,List.append_nil,reverseCode,←hs]

/-- Actual local CNOT/list/reverse-map models plus two head-case actions.
Index payload bit costs and generic wrapper/annotation work remain separate. -/
def ListPauliPlanResult.actions {n : ℕ} (r : ListPauliPlanResult n) : ℕ :=
  r.leading.trace.actions+r.trailing.trace.actions+2


theorem listPauliPlanProgram_actions {n : ℕ} (hn : 0<n) (xs : List (Fin n)) (h : xs.Nodup) :
    (listPauliPlanProgram hn xs h).actions≤10*xs.length+4 := by
  cases xs with
  | nil => simp [listPauliPlanProgram,ListPauliPlanResult.actions,cnotListProgram,CnotListTrace.actions,
      listReverseMapIntoProgram,ListAssemblyTrace.actions]
  | cons t ts =>
    simp only [listPauliPlanProgram,ListPauliPlanResult.actions,cnotListProgram_actions,
      listReverseMapIntoProgram_actions,cnotListProgram_length,List.length_cons]
    omega

end EffectiveEncoding
