import EffectiveEncoding.RawCompiler

open scoped BigOperators
open CircuitCompletion CircuitRecursion Matrix
namespace EffectiveEncoding

set_option maxHeartbeats 800000

def countProgram {n : ℕ} (p : Bits n) (c : Bits n → ℕ) :
    List {q : Bits n // q≠p} → ℕ → ℕ → List (RawCode n)
  | [],_,_ => []
  | q::qs,A,j => .merge p q.1 (Ne.symm q.2) A (c q.1) j::
      countProgram p c qs (A+c q.1) j

theorem countProgram_length {n : ℕ} (p : Bits n) (c : Bits n → ℕ)
    (qs : List {q : Bits n // q≠p}) (A j : ℕ) :
    (countProgram p c qs A j).length=qs.length := by
  induction qs generalizing A with
  | nil => rfl
  | cons q qs ih => simp only [countProgram,List.length_cons,ih]

theorem countProgram_sparse {n : ℕ} (p : Bits n) (c : Bits n → ℕ)
    (qs : List {q : Bits n // q≠p}) (A j : ℕ) :
    (countProgram p c qs A j).map RawCode.value=
      sparseProgram p (fun w => (c w:ℝ)/j) (by intro w;positivity)
        qs ((A:ℝ)/j) (by positivity) := by
  induction qs generalizing A with
  | nil => rfl
  | cons q qs ih =>
    simp only [countProgram,List.map_cons,RawCode.value,sparseProgram,ih]
    congr 2
    push_cast
    ring

def indexedCount {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (e : ι ↪ Bits n) (c : ι → ℕ) (w : Bits n) : ℕ :=
  ∑ i,if w=e i then c i else 0

theorem indexedCount_image {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (e : ι ↪ Bits n) (c : ι → ℕ) (i : ι) :
    indexedCount e c (e i)=c i := by
  simp [indexedCount,e.injective.eq_iff]

theorem indexedCount_ratio {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (e : ι ↪ Bits n) (c : ι → ℕ) (j : ℕ) :
    (fun w => (indexedCount e c w:ℝ)/j)=indexedMass e (fun i => (c i:ℝ)/j) := by
  funext w
  simp only [indexedCount,indexedMass,Nat.cast_sum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> simp

def explicitOthers {ι : Type*} [Fintype ι] [LinearOrder ι] {n : ℕ}
    (e : ι ↪ Bits n) (p : ι) : List {q : Bits n // q≠e p} :=
  ((Finset.univ.erase p).attach.sort (·≤·)).map
    (fun i => ⟨e i.1,fun h => (Finset.mem_erase.mp i.2).1 (e.injective h)⟩)

theorem explicitOthers_perm {ι : Type*} [Fintype ι] [LinearOrder ι] {n : ℕ}
    (e : ι ↪ Bits n) (p : ι) : (explicitOthers e p).Perm (indexedOthers e p) := by
  exact (Finset.sort_perm_toList ((Finset.univ.erase p).attach) (·≤·)).map _

theorem explicitOthers_nodup {ι : Type*} [Fintype ι] [LinearOrder ι] {n : ℕ}
    (e : ι ↪ Bits n) (p : ι) : (explicitOthers e p).Nodup :=
  (explicitOthers_perm e p).nodup_iff.mpr (indexedOthers_nodup e p)

theorem explicitOthers_length {ι : Type*} [Fintype ι] [LinearOrder ι] {n : ℕ}
    (e : ι ↪ Bits n) (p : ι) : (explicitOthers e p).length=Fintype.card ι-1 :=
  (explicitOthers_perm e p).length_eq.trans (indexedOthers_length e p)

def integerIndexedCode {ι : Type*} [Fintype ι] [LinearOrder ι] {n : ℕ}
    (hn : 0<n) (e : ι ↪ Bits n) (c : ι → ℕ) (p : ι) (j : ℕ) : WordCode n :=
  compileRaw hn (countProgram (e p) (indexedCount e c) (explicitOthers e p) (c p) j)

theorem integerIndexedCode_raw {ι : Type*} [Fintype ι] [LinearOrder ι] {n : ℕ}
    (hn : 0<n) (e : ι ↪ Bits n) (c : ι → ℕ) (p : ι) (j : ℕ)
    (v : Bits n → ℂ) :
    run (interpret (integerIndexedCode hn e c p j)) v=
      rawRun (sparseProgram (e p) (indexedMass e (fun i => (c i:ℝ)/j))
        (indexedMass_nonneg _ _ (by intro i;positivity))
        (explicitOthers e p) ((c p:ℝ)/j) (by positivity)) v := by
  simp only [integerIndexedCode,run,compileRaw_denote,rawRun]
  simp only [countProgram_sparse,indexedCount_ratio]

theorem integerIndexedCode_action {ι : Type*} [Fintype ι] [LinearOrder ι] {n : ℕ}
    (hn : 0<n) (e : ι ↪ Bits n) (c : ι → ℕ) (p : ι) (j : ℕ)
    (hsum : ∑ i,(c i:ℝ)/j=1) :
    run (interpret (integerIndexedCode hn e c p j))
      (Extraction.coordinateIsometry e*ᵥ(fun i => (Real.sqrt ((c i:ℝ)/j):ℂ)))=
        Pi.single (e p) 1 := by
  let a : ι → ℝ := fun i => (c i:ℝ)/j
  have ha : ∀ i,0≤a i := by intro i;dsimp [a];positivity
  let v := Extraction.coordinateIsometry e*ᵥ(fun i => (Real.sqrt (a i):ℂ))
  have hv := coordinateIsometry_sqrtMass e a ha
  have hp : v (e p)=(Real.sqrt (a p):ℂ) := by
    change (Extraction.coordinateIsometry e*ᵥ(fun i => (Real.sqrt (a i):ℂ))) (e p)=_
    rw [hv,indexedMass_image]
  have hq : ∀ q∈explicitOthers e p,v q.1=(Real.sqrt (indexedMass e a q.1):ℂ) := by
    intro q hq
    exact hv q.1
  rw [integerIndexedCode_raw]
  rw [sparseProgram_action _ _ (indexedMass_nonneg e a ha) _
    (explicitOthers_nodup e p) _ _ v hp hq]
  have hs := ((explicitOthers_perm e p).map (fun q => indexedMass e a q.1)).sum_eq
  have hvsum := ((explicitOthers_perm e p).map
    (fun q => (Pi.single q.1 (Real.sqrt (indexedMass e a q.1):ℂ):Bits n → ℂ))).sum_eq
  rw [hs,hvsum,indexedOthers_sum,indexedOthers_vector]
  rw [Finset.add_sum_erase _ _ (Finset.mem_univ p),hsum,Real.sqrt_one,Complex.ofReal_one]
  rw [Finset.add_sum_erase (Finset.univ : Finset ι)
    (fun i => (Pi.single (e i) (Real.sqrt (a i):ℂ):Bits n → ℂ)) (Finset.mem_univ p),
    ← coordinateIsometry_sum]
  simp [v]

theorem integerIndexedCode_fixes_zero {ι : Type*} [Fintype ι] [LinearOrder ι] {n : ℕ}
    (hn : 0<n) (e : ι ↪ Bits n) (c : ι → ℕ) (p : ι) (j : ℕ)
    (v : Bits n → ℂ) (hv : ∀ i,v (e i)=0) :
    run (interpret (integerIndexedCode hn e c p j)) v=v := by
  rw [integerIndexedCode_raw]
  apply sparseProgram_fixes_zero _ _ _ _ _ _ v (hv p)
  intro q hq
  have hq' := (explicitOthers_perm e p).mem_iff.mp hq
  rcases List.mem_map.mp hq' with ⟨i,hi,h⟩
  subst q
  exact hv i.1

theorem integerIndexedCode_length {ι : Type*} [Fintype ι] [LinearOrder ι] {n : ℕ}
    (hn : 0<n) (e : ι ↪ Bits n) (c : ι → ℕ) (p : ι) (j : ℕ) :
    (integerIndexedCode hn e c p j).length≤(Fintype.card ι-1)*(20*n^2*2^n) := by
  exact (compileRaw_length hn _).trans_eq (by rw [countProgram_length,explicitOthers_length])

def occupiedPivot {k : ℕ} (ν : Sym (Fin 4) (k+1)) : {i : Fin 4 // i∈ν} :=
  ⟨ν.val.toFinset.min' (by
    obtain ⟨i,hi⟩ := Sym.exists_mem ν
    exact ⟨i,Multiset.mem_toFinset.mpr hi⟩),
    Multiset.mem_toFinset.mp (Finset.min'_mem _ _)⟩

def branchEmbedding {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q)
    (ν : Sym (Fin 4) (k+1)) : {i : Fin 4 // i∈ν} ↪ Bits (2+q) where
  toFun i := Fin.append (letterBits i.1) (enc (ν.erase i.1 i.2))
  inj' := (CircuitCompletion.branchEmbedding enc ν).injective

theorem branchEmbedding_eq {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q)
    (ν : Sym (Fin 4) (k+1)) :
    branchEmbedding enc ν=CircuitCompletion.branchEmbedding enc ν := rfl

def pivotCoordinates {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q)
    (ν : Sym (Fin 4) (k+1)) : Bits (2+q) :=
  branchEmbedding enc ν (occupiedPivot ν)

def pivotEmbedding {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q) :
    Sym (Fin 4) (k+1) ↪ Bits (2+q) where
  toFun := pivotCoordinates enc
  inj' := by
    intro ν μ h
    exact (branchCoordinates_equal enc ν μ _ _ _ _ h).1

def branchCode {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q)
    (ν : Sym (Fin 4) (k+1)) : WordCode (2+q) :=
  integerIndexedCode (by omega) (branchEmbedding enc ν)
    (fun i => ν.val.count i.1) (occupiedPivot ν) (k+1)

theorem branchCode_action {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q)
    (ν : Sym (Fin 4) (k+1)) :
    run (interpret (branchCode enc ν)) (encodedBranch enc ν)=
      Pi.single (pivotCoordinates enc ν) 1 := by
  have hs : (∑ i : {i : Fin 4 // i∈ν},(ν.val.count i.1:ℝ)/((k+1:ℕ):ℝ))=1 := by
    simpa only [occupationMass,Nat.cast_add,Nat.cast_one] using occupationMass_occupied_sum ν
  simpa only [branchCode,pivotCoordinates,branchEmbedding_eq,encodedBranch,occupationMass,Nat.cast_add,Nat.cast_one] using
    integerIndexedCode_action (by omega) (branchEmbedding enc ν)
      (fun i => ν.val.count i.1) (occupiedPivot ν) (k+1) hs

theorem branchCode_fixes_other {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q)
    (ν μ : Sym (Fin 4) (k+1)) (h : ν≠μ) :
    run (interpret (branchCode enc μ)) (encodedBranch enc ν)=encodedBranch enc ν := by
  apply integerIndexedCode_fixes_zero
  intro i
  exact encodedBranch_disjoint_zero enc ν μ h i.1 i.2

theorem branchCode_fixes_other_pivot {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q)
    (ν μ : Sym (Fin 4) (k+1)) (h : ν≠μ) :
    run (interpret (branchCode enc μ)) (Pi.single (pivotCoordinates enc ν) 1)=
      Pi.single (pivotCoordinates enc ν) 1 := by
  apply integerIndexedCode_fixes_zero
  intro i
  have hn := branchCoordinates_disjoint enc ν μ h
    (occupiedPivot ν).1 i.1 (occupiedPivot ν).2 i.2
  simp only [Pi.single_apply]
  rw [if_neg]
  exact Ne.symm hn

theorem branchCode_length {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q)
    (ν : Sym (Fin 4) (k+1)) :
    (branchCode enc ν).length≤60*(2+q)^2*2^(2+q) := by
  have h := integerIndexedCode_length (by omega) (branchEmbedding enc ν)
    (fun i => ν.val.count i.1) (occupiedPivot ν) (k+1)
  have hc : Fintype.card {i : Fin 4 // i∈ν}≤4 :=
    Fintype.card_le_of_injective (fun i : {i : Fin 4 // i∈ν} => i.1) Subtype.val_injective
  have h' := Nat.mul_le_mul_right (20*(2+q)^2*2^(2+q))
    (show Fintype.card {i : Fin 4 // i∈ν}-1≤3 by omega)
  change (branchCode enc ν).length≤_ at h
  nlinarith

end EffectiveEncoding

