import EffectiveEncoding.ConstructiveRankExtraction

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding


def replicateBuild {α : Type*} : ℕ → α → ListBuild α
  | 0,_ => ListBuild.empty
  | n+1,a => ListBuild.emit a (replicateBuild n a)


theorem replicateBuild_items {α : Type*} (n : ℕ) (a : α) :
    (replicateBuild n a).items=List.replicate n a := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [replicateBuild,ListBuild.emit,ih,List.replicate_succ]


theorem replicateBuild_steps {α : Type*} (n : ℕ) (a : α) : (replicateBuild n a).steps=n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [replicateBuild,ListBuild.emit,ih]


def occupationLettersBuild (k : ℕ) (t : Triple) : ListBuild (Fin 4) :=
  let a:=replicateBuild t.1 (0 : Fin 4)
  let b:=replicateBuild t.2.1 (1 : Fin 4)
  let c:=replicateBuild t.2.2 (2 : Fin 4)
  let d:=replicateBuild (k-total t) (3 : Fin 4)
  ((a.append b).append c).append d


theorem occupationLettersBuild_items (k : ℕ) (t : Triple) :
    (occupationLettersBuild k t).items=
      List.replicate t.1 (0 : Fin 4)++List.replicate t.2.1 1++
        List.replicate t.2.2 2++List.replicate (k-total t) 3 := by
  simp only [occupationLettersBuild,ListBuild.append,replicateBuild_items]


theorem occupationLettersBuild_length (k : ℕ) (t : Triple) (h : total t≤k) :
    (occupationLettersBuild k t).items.length=k := by
  rw [occupationLettersBuild_items]
  simp only [List.length_append,List.length_replicate]
  unfold total at h ⊢
  omega

/-- This counts all four replicate lists and all left-list copies in the
three actual append operations; Nat arithmetic is outside this source model. -/
theorem occupationLettersBuild_steps (k : ℕ) (t : Triple) (h : total t≤k) :
    (occupationLettersBuild k t).steps≤4*k+7 := by
  simp only [occupationLettersBuild,ListBuild.append,replicateBuild_steps,replicateBuild_items,
    List.length_append,List.length_replicate]
  unfold total at h ⊢
  omega

structure OccupationLiteralResult (k : ℕ) where
  occupation : Sym (Fin 4) k
  steps : ℕ

/-- Construct the concrete list once and use its quotient as the occupation.
No finite-type choice or arbitrary multiset representative is requested. -/
def occupationLiteralProgram (k : ℕ) (t : Triple) (h : total t≤k) : OccupationLiteralResult k :=
  let letters:=occupationLettersBuild k t
  ⟨⟨(letters.items : Multiset (Fin 4)),by
    simpa only [Multiset.coe_card] using occupationLettersBuild_length k t h⟩,letters.steps⟩


theorem occupationLiteralProgram_value (k : ℕ) (t : Triple) (h : total t≤k) :
    (occupationLiteralProgram k t h).occupation=fromTriple k t h := by
  apply Subtype.ext
  change ((occupationLettersBuild k t).items : Multiset (Fin 4))=_
  rw [occupationLettersBuild_items]
  rfl


theorem occupationLiteralProgram_steps (k : ℕ) (t : Triple) (h : total t≤k) :
    (occupationLiteralProgram k t h).steps≤4*k+7 := occupationLettersBuild_steps k t h

structure LiteralOccupationTable (k : ℕ) where
  occupations : List (Sym (Fin 4) k)
  tripleSteps : ℕ
  literalSteps : ℕ

theorem triplesBuild_total {k : ℕ} {t : Triple} (ht : t∈(triplesBuild k).items) : total t≤k := by
  apply mem_triples.mp
  simpa only [triplesBuild_items] using ht

/-- Each literal occupation record is stored once and reused for its value
and source fee. The fee does not charge these table maps or record bookkeeping. -/
def literalOccupationTable (k : ℕ) : LiteralOccupationTable k :=
  let candidates:=triplesBuild k
  let stored:=candidates.items.attach.map (fun t => occupationLiteralProgram k t.1 (triplesBuild_total t.2))
  ⟨stored.map OccupationLiteralResult.occupation,candidates.steps,(stored.map OccupationLiteralResult.steps).sum⟩


theorem literalOccupationTable_value (k : ℕ) : (literalOccupationTable k).occupations=builtOccupations k := by
  simp only [literalOccupationTable,List.map_map,Function.comp_def,occupationLiteralProgram_value,
    builtOccupations,occupationList]


theorem literalOccupationTable_tripleSteps (k : ℕ) :
    (literalOccupationTable k).tripleSteps≤28*(k+1)^3 := triplesBuild_steps k


theorem literalOccupationTable_literalSteps (k : ℕ) :
    (literalOccupationTable k).literalSteps≤(4*k+7)*(k+1)^3 := by
  unfold literalOccupationTable
  dsimp only
  calc
    _≤(((triplesBuild k).items.attach.map (fun t => occupationLiteralProgram k t.1 (triplesBuild_total t.2))).map
        (fun _ => 4*k+7)).sum := by
      apply List.sum_le_sum
      intro r hr
      obtain ⟨t,ht,rfl⟩:=List.mem_map.mp hr
      exact occupationLiteralProgram_steps k t.1 _
    _=(triples k).length*(4*k+7) := by simp [List.map_map,Function.comp_def,triplesBuild_items]
    _≤(k+1)^3*(4*k+7) := by
      apply Nat.mul_le_mul_right
      simpa only [occupations,List.length_map,List.length_attach] using enumeration_candidate_bound k
    _=_ := Nat.mul_comm _ _

end EffectiveEncoding
