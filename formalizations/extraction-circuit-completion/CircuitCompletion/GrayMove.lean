import CircuitCompletion.SwapSemantics

open scoped BigOperators
namespace CircuitCompletion

def clearBits {n : ℕ} (x : Bits n) (cs : List (Fin n)) (y : Bits n) : Bits n :=
  cs.foldl (fun p j => Function.update p j (x j)) y

theorem clearBits_apply {n : ℕ} (x : Bits n) (cs : List (Fin n)) (y : Bits n) (j : Fin n) :
    clearBits x cs y j=if j∈cs then x j else y j := by
  induction cs generalizing y with
  | nil => simp [clearBits]
  | cons c cs ih =>
    change clearBits x cs (Function.update y c (x c)) j=_
    rw [ih]
    by_cases hj : j∈cs <;> by_cases hjc : j=c <;> simp_all

theorem flipBit_eq_update {n : ℕ} (j : Fin n) (x y : Bits n) (h : y j≠x j) :
    flipBit j y=Function.update y j (x j) := by
  unfold flipBit
  congr 1
  cases hy : y j <;> cases hx : x j <;> simp_all

noncomputable def moveWord {n : ℕ} (hn : 0<n) (x : Bits n) :
    List (Fin n) → Bits n → Circuit n
  | [],_ => []
  | j::js,y => if y j=x j then moveWord hn x js y else
      adjacentSwapWord hn j y++moveWord hn x js (Function.update y j (x j))

noncomputable def moveEquiv {n : ℕ} (x : Bits n) :
    List (Fin n) → Bits n → Equiv.Perm (Bits n)
  | [],_ => Equiv.refl _
  | j::js,y => if y j=x j then moveEquiv x js y else
      (Equiv.swap y (flipBit j y)).trans (moveEquiv x js (Function.update y j (x j)))

theorem moveEquiv_source {n : ℕ} (x : Bits n) (cs : List (Fin n)) (y : Bits n) :
    moveEquiv x cs y y=clearBits x cs y := by
  induction cs generalizing y with
  | nil => rfl
  | cons j js ih =>
    by_cases h : y j=x j
    · have hu : Function.update y j (x j)=y := by
        rw [← h];exact Function.update_eq_self j y
      simp only [moveEquiv,if_pos h,clearBits,List.foldl_cons,hu]
      exact ih y
    · simp only [moveEquiv,if_neg h,Equiv.trans_apply,Equiv.swap_apply_left]
      rw [flipBit_eq_update j x y h,ih]
      rfl

theorem moveEquiv_fixes {n : ℕ} (x : Bits n) (cs : List (Fin n)) (y : Bits n)
    (t : Fin n) (ht : y t≠x t) (hcs : ∀ j∈cs,j≠t) : moveEquiv x cs y x=x := by
  induction cs generalizing y with
  | nil => rfl
  | cons j js ih =>
    have hjt : j≠t := hcs j (by simp)
    have htail : ∀ q∈js,q≠t := by intro q hq;exact hcs q (by simp [hq])
    by_cases h : y j=x j
    · simp only [moveEquiv,if_pos h]
      exact ih y ht htail
    · have hxy : x≠y := by intro hxy;exact ht (by rw [← hxy])
      have hxf : x≠flipBit j y := by
        intro hxf
        have h' := congrFun hxf t
        simp only [flipBit,Function.update_of_ne (Ne.symm hjt)] at h'
        exact ht h'.symm
      simp only [moveEquiv,if_neg h,Equiv.trans_apply]
      rw [Equiv.swap_apply_of_ne_of_ne hxy hxf]
      apply ih _ _ htail
      simpa [Function.update_of_ne (Ne.symm hjt)] using ht

theorem run_moveWord {n : ℕ} (hn : 0<n) (x : Bits n) (cs : List (Fin n)) (y : Bits n)
    (v : Bits n → ℂ) :
    run (moveWord hn x cs y) v=fun w => v ((moveEquiv x cs y).symm w) := by
  induction cs generalizing y v with
  | nil => simp [moveWord,moveEquiv,run,denote]
  | cons j js ih =>
    by_cases h : y j=x j
    · simp only [moveWord,moveEquiv,if_pos h]
      exact ih y v
    · simp only [moveWord,moveEquiv,if_neg h,run_append,ih,adjacentSwapWord_swap,
        Equiv.symm_trans_apply]
      rfl

theorem moveWord_length {n : ℕ} (hn : 0<n) (x : Bits n) (cs : List (Fin n)) (y : Bits n) :
    (moveWord hn x cs y).length≤cs.length*(2^n*(2*n+1)+2) := by
  induction cs generalizing y with
  | nil => simp [moveWord]
  | cons j js ih =>
    by_cases h : y j=x j
    · simp only [moveWord,if_pos h,List.length_cons]
      exact (ih y).trans (Nat.mul_le_mul_right _ (Nat.le_succ _))
    · simp only [moveWord,if_neg h,List.length_append,List.length_cons]
      have h1 := adjacentSwapWord_length hn j y
      have h2 := ih (Function.update y j (x j))
      nlinarith

end CircuitCompletion
