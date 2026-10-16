import CircuitCompletion.SparseCompression
import CircuitCompletion.EncodedBranches

open scoped BigOperators
open Matrix
namespace CircuitCompletion

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

noncomputable def indexedMass (e : ι ↪ Bits n) (a : ι → ℝ) (w : Bits n) : ℝ :=
  ∑ i,if w=e i then a i else 0

theorem indexedMass_image (e : ι ↪ Bits n) (a : ι → ℝ) (i : ι) : indexedMass e a (e i)=a i := by
  simp [indexedMass,e.injective.eq_iff]

theorem indexedMass_nonneg (e : ι ↪ Bits n) (a : ι → ℝ) (ha : ∀ i,0≤a i) (w : Bits n) :
    0 ≤ indexedMass e a w := by
  apply Finset.sum_nonneg
  intro i hi
  split_ifs <;> simp [ha]

noncomputable def indexedOthers (e : ι ↪ Bits n) (p : ι) : List {q : Bits n // q≠e p} :=
  (Finset.univ.erase p).attach.toList.map
    (fun i => ⟨e i.1,fun h => (Finset.mem_erase.mp i.2).1 (e.injective h)⟩)

theorem indexedOthers_nodup (e : ι ↪ Bits n) (p : ι) : (indexedOthers e p).Nodup := by
  apply List.Nodup.map _ (Finset.nodup_toList _)
  intro i j h
  apply Subtype.ext
  exact e.injective (congrArg Subtype.val h)

theorem indexedOthers_length (e : ι ↪ Bits n) (p : ι) :
    (indexedOthers e p).length=Fintype.card ι-1 := by simp [indexedOthers]

theorem indexedOthers_sum (e : ι ↪ Bits n) (a : ι → ℝ) (p : ι) :
    ((indexedOthers e p).map (fun q => indexedMass e a q.1)).sum=
      ∑ i ∈ (Finset.univ : Finset ι).erase p,a i := by
  simp only [indexedOthers,List.map_map,Function.comp_def,indexedMass_image]
  rw [Finset.sum_map_toList,Finset.sum_attach]

theorem indexedOthers_vector (e : ι ↪ Bits n) (a : ι → ℝ) (p : ι) :
    ((indexedOthers e p).map (fun q => (Pi.single q.1 (Real.sqrt (indexedMass e a q.1) : ℂ) : Bits n → ℂ))).sum=
      ∑ i ∈ (Finset.univ : Finset ι).erase p,(Pi.single (e i) (Real.sqrt (a i) : ℂ) : Bits n → ℂ) := by
  simp only [indexedOthers,List.map_map,Function.comp_def,indexedMass_image]
  rw [Finset.sum_map_toList]
  exact Finset.sum_attach _ (fun i => (Pi.single (e i) (Real.sqrt (a i) : ℂ) : Bits n → ℂ))

theorem coordinateIsometry_sum {κ : Type*} [Fintype κ] [DecidableEq κ]
    (e : ι ↪ κ) (v : ι → ℂ) :
    Extraction.coordinateIsometry e*ᵥv=∑ i,Pi.single (e i) (v i) := by
  ext w
  simp [Matrix.mulVec,dotProduct,Extraction.coordinateIsometry,Pi.single_apply,eq_comm]

theorem coordinateIsometry_sqrtMass (e : ι ↪ Bits n) (a : ι → ℝ)
    (ha : ∀ i,0≤a i) (w : Bits n) :
    (Extraction.coordinateIsometry e*ᵥ(fun i => (Real.sqrt (a i) : ℂ))) w=
      (Real.sqrt (indexedMass e a w) : ℂ) := by
  by_cases hw : ∃ i,e i=w
  · obtain ⟨i,rfl⟩ := hw
    simp [Matrix.mulVec,dotProduct,Extraction.coordinateIsometry,indexedMass_image,e.injective.eq_iff]
  · have hn (i : ι) : w≠e i := by intro h;exact hw ⟨i,h.symm⟩
    simp [Matrix.mulVec,dotProduct,Extraction.coordinateIsometry,indexedMass,hn]

noncomputable def indexedCompression (hn : 0<n) (e : ι ↪ Bits n) (a : ι → ℝ)
    (ha : ∀ i,0≤a i) (p : ι) : Circuit n :=
  compileProgram hn (sparseProgram (e p) (indexedMass e a) (indexedMass_nonneg e a ha)
    (indexedOthers e p) (a p) (ha p))

/-- A normalized nonnegative finite sparse vector is compressed by a
constructed elementary word into any of its actual occupied coordinates. -/
theorem indexedCompression_action (hn : 0<n) (e : ι ↪ Bits n) (a : ι → ℝ)
    (ha : ∀ i,0≤a i) (hsum : ∑ i,a i=1) (p : ι) :
    run (indexedCompression hn e a ha p)
      (Extraction.coordinateIsometry e*ᵥ(fun i => (Real.sqrt (a i) : ℂ)))=Pi.single (e p) 1 := by
  have hv := coordinateIsometry_sqrtMass e a ha
  have hp : (Extraction.coordinateIsometry e*ᵥ(fun i => (Real.sqrt (a i) : ℂ))) (e p)=
      (Real.sqrt (a p) : ℂ) := by rw [hv,indexedMass_image]
  have hq : ∀ q∈indexedOthers e p,
      (Extraction.coordinateIsometry e*ᵥ(fun i => (Real.sqrt (a i) : ℂ))) q.1=
        (Real.sqrt (indexedMass e a q.1) : ℂ) := by intro q hq;exact hv q.1
  rw [indexedCompression,compiled_sparse_action hn _ _ _ _ (indexedOthers_nodup e p) _ _ _ hp hq,
    indexedOthers_sum,indexedOthers_vector]
  rw [Finset.add_sum_erase _ _ (Finset.mem_univ p),hsum,Real.sqrt_one,Complex.ofReal_one]
  rw [Finset.add_sum_erase (Finset.univ : Finset ι)
    (fun i => (Pi.single (e i) (Real.sqrt (a i) : ℂ) : Bits n → ℂ)) (Finset.mem_univ p),
    ← coordinateIsometry_sum]
  simp

theorem indexedCompression_length (hn : 0<n) (e : ι ↪ Bits n) (a : ι → ℝ)
    (ha : ∀ i,0≤a i) (p : ι) :
    (indexedCompression hn e a ha p).length≤(Fintype.card ι-1)*(20*n^2*2^n) := by
  simpa only [indexedCompression,indexedOthers_length] using
    compiled_sparse_length hn (e p) (indexedMass e a) (indexedMass_nonneg e a ha)
      (indexedOthers e p) (a p) (ha p)

theorem indexedCompression_fixes_zero (hn : 0<n) (e : ι ↪ Bits n) (a : ι → ℝ)
    (ha : ∀ i,0≤a i) (p : ι) (v : Bits n → ℂ) (hv : ∀ i,v (e i)=0) :
    run (indexedCompression hn e a ha p) v=v := by
  apply compiled_sparse_fixes_zero hn _ _ _ _ _ _ v (hv p)
  intro q hq
  rcases List.mem_map.mp hq with ⟨i,hi,h⟩
  subst q
  exact hv i.1

end CircuitCompletion
