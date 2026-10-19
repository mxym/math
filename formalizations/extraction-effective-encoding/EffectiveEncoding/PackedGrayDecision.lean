import EffectiveEncoding.BooleanGrayScan

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding


theorem packedGrayDifferences_sorted {n : ℕ} (x y : PackedBits n) :
    ((List.finRange n).filter (fun a => !(unpackBits x a==unpackBits y a)))=
      (Finset.univ.filter (fun a : Fin n => unpackBits y a≠unpackBits x a)).sort (·≤·) := by
  apply List.Pairwise.eq_of_mem_iff
    (List.Pairwise.filter _ (List.sortedLT_finRange n).pairwise) (Finset.sortedLT_sort _).pairwise
  intro a
  simp [ne_comm]


theorem packedGrayScanProgram_none {n : ℕ} (x y : PackedBits n) :
    (packedGrayScanProgram x y).scan.first=none ↔ unpackBits x=unpackBits y := by
  change (booleanGrayScanProgram (List.finRange n) x.toList y.toList).first=none ↔ _
  rw [←packedMask_finRange_map x,←packedMask_finRange_map y,booleanGrayScanProgram_none]
  constructor
  · intro h;funext j;exact h j (by simp)
  · intro h j hj;exact congrFun h j


theorem packedGrayScanProgram_first_eq {n : ℕ} (x y : PackedBits n)
    (h : unpackBits x≠unpackBits y) :
    (packedGrayScanProgram x y).scan.first=some (differingWire (unpackBits x) (unpackBits y) h) := by
  rw [packedGrayScanProgram_first,packedGrayDifferences_sorted]
  let S:=Finset.univ.filter (fun a : Fin n => unpackBits y a≠unpackBits x a)
  have hS : S.Nonempty:=differing_exists (unpackBits x) (unpackBits y) h
  change (S.sort (·≤·)).head?=some (S.min' hS)
  cases hs : S.sort (·≤·) with
  | nil =>
    obtain ⟨a,ha⟩:=hS
    have hm:=(Finset.mem_sort (·≤·)).mpr ha
    rw [hs] at hm
    exact False.elim (List.not_mem_nil hm)
  | cons t ts =>
    simp only [List.head?_cons,Option.some.injEq]
    exact (sortedList_head_min S t ts hS hs).symm


theorem finRange_erase_otherWires {n : ℕ} (t : Fin n) :
    (List.finRange n).erase t=otherWires t := by
  rw [(List.nodup_finRange n).erase_eq_filter]
  apply List.Pairwise.eq_of_mem_iff
    (List.Pairwise.filter _ (List.sortedLT_finRange n).pairwise) (Finset.sortedLT_sort _).pairwise
  intro a
  simp [otherWires]


theorem packedGrayScanProgram_others_eq {n : ℕ} (x y : PackedBits n)
    (h : unpackBits x≠unpackBits y) :
    (packedGrayScanProgram x y).scan.others=otherWires (differingWire (unpackBits x) (unpackBits y) h) := by
  have hp:=packedGrayScanProgram_first_eq x y h
  change (booleanGrayScanProgram (List.finRange n) x.toList y.toList).first=_ at hp
  change (booleanGrayScanProgram (List.finRange n) x.toList y.toList).others=_
  rw [←packedMask_finRange_map x,←packedMask_finRange_map y] at hp ⊢
  exact (booleanGrayScanProgram_others (List.finRange n) (unpackBits x) (unpackBits y)
    (List.nodup_finRange n) _ hp).trans (finRange_erase_otherWires _)

end EffectiveEncoding
