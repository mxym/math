import CircuitCompletion.RawCompiler
import CircuitCompletion.SparseBlocks

open scoped BigOperators
open Matrix
namespace CircuitCompletion

noncomputable def sparseProgram {n : ℕ} (p : Bits n) (a : Bits n → ℝ) (ha : ∀ w,0≤a w) :
    List {q : Bits n // q≠p} → (s : ℝ) → 0≤s → List (TwoLevel n)
  | [],_,_ => []
  | q::qs,s,hs => TwoLevel.givens p q.1 (Ne.symm q.2) s (a q.1) hs (ha q.1)::
      sparseProgram p a ha qs (s+a q.1) (add_nonneg hs (ha q.1))

noncomputable def rawRun {n : ℕ} (a : List (TwoLevel n)) (v : Bits n → ℂ) : Bits n → ℂ :=
  (rawDenote a : Matrix (Bits n) (Bits n) ℂ)*ᵥv

theorem rawRun_nil {n : ℕ} (v : Bits n → ℂ) : rawRun [] v=v := by simp [rawRun,rawDenote]

theorem rawRun_cons {n : ℕ} (g : TwoLevel n) (gs : List (TwoLevel n)) (v : Bits n → ℂ) :
    rawRun (g::gs) v=rawRun gs ((g.denote : Matrix (Bits n) (Bits n) ℂ)*ᵥv) := by
  simp only [rawRun,rawDenote,Matrix.UnitaryGroup.mul_val,← Matrix.mulVec_mulVec]

/-- No dummy coordinate is used for a missing occupation branch: the list
contains only actual occupied labels distinct from the chosen pivot. -/
theorem sparseProgram_action {n : ℕ} (p : Bits n) (a : Bits n → ℝ) (ha : ∀ w,0≤a w)
    (qs : List {q : Bits n // q≠p}) (hqs : qs.Nodup) (s : ℝ) (hs : 0≤s)
    (v : Bits n → ℂ) (hp : v p=(Real.sqrt s : ℂ))
    (hq : ∀ q∈qs,v q.1=(Real.sqrt (a q.1) : ℂ)) :
    rawRun (sparseProgram p a ha qs s hs) v=
      Pi.single p (Real.sqrt (s+(qs.map (fun q => a q.1)).sum) : ℂ)+
        (v-(Pi.single p (Real.sqrt s : ℂ)+
          (qs.map (fun q => Pi.single q.1 (Real.sqrt (a q.1) : ℂ))).sum)) := by
  classical
  induction qs generalizing s v with
  | nil => simp [sparseProgram,rawRun,rawDenote]
  | cons q qs ih =>
    have hnq : q∉qs := (List.nodup_cons.mp hqs).1
    have hnt : qs.Nodup := (List.nodup_cons.mp hqs).2
    let v1 : Bits n → ℂ := Pi.single p (Real.sqrt (s+a q.1) : ℂ)+
      (v-(Pi.single p (Real.sqrt s : ℂ)+Pi.single q.1 (Real.sqrt (a q.1) : ℂ)))
    have hv : ((TwoLevel.givens p q.1 (Ne.symm q.2) s (a q.1) hs (ha q.1)).denote :
        Matrix (Bits n) (Bits n) ℂ)*ᵥv=v1 :=
      mergeAt_action p q.1 (Ne.symm q.2) s (a q.1) hs (ha q.1) v hp (hq q (by simp))
    have hvp : v1 p=(Real.sqrt (s+a q.1) : ℂ) := by
      simp [v1,Pi.single_apply,hp,q.2]
    have hvt : ∀ r∈qs,v1 r.1=(Real.sqrt (a r.1) : ℂ) := by
      intro r hr
      have hrq : r.1≠q.1 := by intro h;exact hnq (Subtype.ext h ▸ hr)
      simp [v1,Pi.single_apply,r.2,hrq,hq r (by simp [hr])]
    simp only [sparseProgram,rawRun_cons,hv]
    rw [ih hnt _ (add_nonneg hs (ha q.1)) v1 hvp hvt]
    simp only [List.map_cons,List.sum_cons,← add_assoc]
    dsimp only [v1]
    abel

theorem sparseProgram_length {n : ℕ} (p : Bits n) (a : Bits n → ℝ) (ha : ∀ w,0≤a w)
    (qs : List {q : Bits n // q≠p}) (s : ℝ) (hs : 0≤s) :
    (sparseProgram p a ha qs s hs).length=qs.length := by
  induction qs generalizing s with
  | nil => rfl
  | cons q qs ih => simp only [sparseProgram,List.length_cons,ih]

theorem compiled_sparse_action {n : ℕ} (hn : 0<n) (p : Bits n) (a : Bits n → ℝ)
    (ha : ∀ w,0≤a w) (qs : List {q : Bits n // q≠p}) (hqs : qs.Nodup)
    (s : ℝ) (hs : 0≤s) (v : Bits n → ℂ) (hp : v p=(Real.sqrt s : ℂ))
    (hq : ∀ q∈qs,v q.1=(Real.sqrt (a q.1) : ℂ)) :
    run (compileProgram hn (sparseProgram p a ha qs s hs)) v=
      Pi.single p (Real.sqrt (s+(qs.map (fun q => a q.1)).sum) : ℂ)+
        (v-(Pi.single p (Real.sqrt s : ℂ)+
          (qs.map (fun q => Pi.single q.1 (Real.sqrt (a q.1) : ℂ))).sum)) := by
  simp only [run,compileProgram_denote]
  exact sparseProgram_action p a ha qs hqs s hs v hp hq

theorem compiled_sparse_length {n : ℕ} (hn : 0<n) (p : Bits n) (a : Bits n → ℝ)
    (ha : ∀ w,0≤a w) (qs : List {q : Bits n // q≠p}) (s : ℝ) (hs : 0≤s) :
    (compileProgram hn (sparseProgram p a ha qs s hs)).length≤qs.length*(20*n^2*2^n) := by
  simpa only [sparseProgram_length] using compileProgram_length hn (sparseProgram p a ha qs s hs)

theorem sparseProgram_fixes_zero {n : ℕ} (p : Bits n) (a : Bits n → ℝ)
    (ha : ∀ w,0≤a w) (qs : List {q : Bits n // q≠p}) (s : ℝ) (hs : 0≤s)
    (v : Bits n → ℂ) (hp : v p=0) (hq : ∀ q∈qs,v q.1=0) :
    rawRun (sparseProgram p a ha qs s hs) v=v := by
  induction qs generalizing s with
  | nil => simp [sparseProgram,rawRun,rawDenote]
  | cons q qs ih =>
    simp only [sparseProgram,rawRun_cons,TwoLevel.denote]
    rw [mergeAt_fixes_zero _ _ _ _ _ _ _ v hp (hq q (by simp))]
    apply ih
    intro r hr
    exact hq r (by simp [hr])

theorem compiled_sparse_fixes_zero {n : ℕ} (hn : 0<n) (p : Bits n) (a : Bits n → ℝ)
    (ha : ∀ w,0≤a w) (qs : List {q : Bits n // q≠p}) (s : ℝ) (hs : 0≤s)
    (v : Bits n → ℂ) (hp : v p=0) (hq : ∀ q∈qs,v q.1=0) :
    run (compileProgram hn (sparseProgram p a ha qs s hs)) v=v := by
  simp only [run,compileProgram_denote]
  exact sparseProgram_fixes_zero p a ha qs s hs v hp hq

end CircuitCompletion
