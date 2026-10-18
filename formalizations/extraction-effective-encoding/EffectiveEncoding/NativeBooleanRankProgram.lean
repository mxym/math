import EffectiveEncoding.NativeTripleScan

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding


theorem nativeTripleWordMap_values (xs : List Triple) :
    (xs.map nativeTripleWordProgram).map NativeTripleWords.value=xs := by
  simp only [List.map_map,Function.comp_def,nativeTripleWordProgram_value]
  exact List.map_id xs

structure NativeBooleanRankResult (k : ℕ) where
  candidates : FilterBuild Triple
  preparedCandidates : List NativeTripleWords
  preparedInput : NativeTripleWords
  scan : NativeTripleScanResult
  ranked : ConstructiveRankRun k

/-- Actual Boolean rank scan. Candidate table arithmetic/filter/control is
still the explicit Nat program, and is separate from the charged bit traces.
No host Nat equality selects the rank-scan branch. -/
def nativeBooleanRankProgram (k : ℕ) (t : Triple) (h : total t≤k) : NativeBooleanRankResult k :=
  let candidates:=triplesBuild k
  let prepared:=candidates.items.map nativeTripleWordProgram
  let input:=nativeTripleWordProgram t
  let scan:=nativeTripleScanProgram input prepared
  let ranked : ConstructiveRankRun k:=
    ⟨⟨scan.index,by
      change (nativeTripleScanProgram (nativeTripleWordProgram t)
        ((triplesBuild k).items.map nativeTripleWordProgram)).index<occupationRank k
      rw [nativeTripleScanProgram_index,nativeTripleWordProgram_value,nativeTripleWordMap_values,
        indexTriplesWithQueries_value,triplesBuild_items,←triples_length]
      exact List.idxOf_lt_length_iff.mpr (mem_triples.mpr h)⟩,
      candidates.steps,candidates.queries,3*scan.tests.length⟩
  ⟨candidates,prepared,input,scan,ranked⟩

/-- Entire old rank specification record, including its logical field-query
metadata. That metadata is not a claim of executed Nat equality bit fees. -/
theorem nativeBooleanRankProgram_ranked (k : ℕ) (t : Triple) (h : total t≤k) :
    (nativeBooleanRankProgram k t h).ranked=carriedTripleRankProgram k t h := by
  simp only [nativeBooleanRankProgram,carriedTripleRankProgram,nativeTripleScanProgram_index,
    nativeTripleWordProgram_value,nativeTripleWordMap_values,nativeTripleScanProgram_logicalQueryCount]

/-- Exactly the real input/candidate encoding traces and scan comparison
traces. The sum does not execute or replay a scan or count-word conversion. -/
def NativeBooleanRankResult.booleanActions {k : ℕ} (r : NativeBooleanRankResult k) : ℕ :=
  r.preparedInput.encodingActions+(r.preparedCandidates.map NativeTripleWords.encodingActions).sum+
    r.scan.comparisonActions


theorem nativeTripleWordMap_encodingActions (k : ℕ) (xs : List Triple)
    (hx : ∀ t∈xs,total t≤k) :
    ((xs.map nativeTripleWordProgram).map NativeTripleWords.encodingActions).sum≤xs.length*(96*(k+1)^2) := by
  induction xs with
  | nil => simp
  | cons t ts ih =>
    have ht:=nativeTripleWordProgram_encodingActions k t (hx t (by simp))
    have hs:=ih (fun t ht => hx t (by simp [ht]))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    exact (Nat.add_le_add ht hs).trans_eq (by ring)


theorem nativeBooleanRankProgram_booleanActions_bound (k : ℕ) (t : Triple) (h : total t≤k) :
    (nativeBooleanRankProgram k t h).booleanActions≤
      96*(k+1)^2+(k+1)^3*(96*(k+1)^2)+(k+1)^3*(48*(k+2)+6) := by
  have hx : ∀ y∈(triplesBuild k).items,total y≤k := by
    intro y hy
    apply mem_triples.mp
    rwa [triplesBuild_items] at hy
  have hl : (triplesBuild k).items.length≤(k+1)^3 := by
    rw [triplesBuild_items,triples_length,←occupations_length]
    exact enumeration_candidate_bound k
  have hp:=nativeTripleWordMap_encodingActions k (triplesBuild k).items hx
  have hs:=nativeTripleScanProgram_comparisonActions (nativeTripleWordProgram t)
    ((triplesBuild k).items.map nativeTripleWordProgram) (k+1) (nativeTripleWordProgram_width k t h) (by
      intro y hy
      rcases List.mem_map.mp hy with ⟨s,hs,heq⟩
      rw [←heq]
      exact nativeTripleWordProgram_width k s (hx s hs))
  have hp':=hp.trans (Nat.mul_le_mul_right _ hl)
  have hs': (nativeTripleScanProgram (nativeTripleWordProgram t)
      ((triplesBuild k).items.map nativeTripleWordProgram)).comparisonActions≤(k+1)^3*(48*(k+2)+6) := by
    simpa only [List.length_map,Nat.add_assoc,Nat.reduceAdd] using hs.trans (Nat.mul_le_mul_right _ (by simpa using hl))
  exact Nat.add_le_add (Nat.add_le_add (nativeTripleWordProgram_encodingActions k t h) hp') hs'


theorem nativeBooleanRank_algebra (x : ℕ) (hx : 1≤x) :
    96*x^2+x^3*(96*x^2)+x^3*(48*(x+1)+6)≤300*(x+1)^5 := by
  have h25 : x^2≤(x+1)^5 := (Nat.pow_le_pow_left (by omega : x≤x+1) 2).trans
    (Nat.pow_le_pow_right (by omega) (by decide))
  have h55 : x^5≤(x+1)^5 := Nat.pow_le_pow_left (by omega) 5
  have h4 : x^3*(48*(x+1)+6)≤54*(x+1)^4 := by
    have h3 := Nat.pow_le_pow_left (show x≤x+1 by omega) 3
    have hlinear : 48*(x+1)+6≤54*(x+1) := by omega
    exact (Nat.mul_le_mul h3 hlinear).trans_eq (by ring)
  have h45 : (x+1)^4≤(x+1)^5 := Nat.pow_le_pow_right (by omega) (by decide)
  nlinarith


theorem nativeBooleanRankProgram_booleanActions_polynomial (k : ℕ) (t : Triple) (h : total t≤k) :
    (nativeBooleanRankProgram k t h).booleanActions≤300*(k+2)^5 :=
  (nativeBooleanRankProgram_booleanActions_bound k t h).trans
    (nativeBooleanRank_algebra (k+1) (by omega))

end EffectiveEncoding
