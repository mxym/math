import EffectiveEncoding.Elementary

open CircuitCompletion CircuitRecursion Matrix
namespace EffectiveEncoding

theorem selectedCode_run_eq {n : ℕ} (hn : 0<n) (x : Bits n) (a : AngleCode)
    (v : Bits n → ℂ) :
    run (interpret (selectedCode hn x a)) v=run (selectedPhaseWord hn x a.value) v := by
  rw [selectedCode_action,selectedPhaseWord_action]

def adjacentSwapCode {n : ℕ} (hn : 0<n) (t : Fin n) (x : Bits n) : WordCode n :=
  [.single t .hadamard]++selectedCode hn (Function.update x t true) piCode++
    [.single t .hadamard]

theorem adjacentSwapCode_run_eq {n : ℕ} (hn : 0<n) (t : Fin n) (x : Bits n)
    (v : Bits n → ℂ) :
    run (interpret (adjacentSwapCode hn t x)) v=run (adjacentSwapWord hn t x) v := by
  unfold adjacentSwapCode adjacentSwapWord
  simp only [interpret_append,run_append,selectedCode_run_eq,piCode_value]
  rfl

theorem adjacentSwapCode_length {n : ℕ} (hn : 0<n) (t : Fin n) (x : Bits n) :
    (adjacentSwapCode hn t x).length≤2^n*(2*n+1)+2 := by
  have h := selectedCode_length hn (Function.update x t true) piCode
  simp only [adjacentSwapCode,List.length_append,List.length_singleton]
  omega

def adjacentRotationCode {n : ℕ} (hn : 0<n) (t : Fin n) (x : Bits n)
    (a : AngleCode) : WordCode n :=
  [.single t (.inverse .yBasis)]++
    selectedCode hn (Function.update x t false) a++
    selectedCode hn (Function.update x t true) a.neg++[.single t .yBasis]

theorem adjacentRotationCode_run_eq {n : ℕ} (hn : 0<n) (t : Fin n) (x : Bits n)
    (a : AngleCode) (v : Bits n → ℂ) :
    run (interpret (adjacentRotationCode hn t x a)) v=
      run (adjacentRotationWord hn t x a.value) v := by
  unfold adjacentRotationCode adjacentRotationWord
  simp only [interpret_append,run_append,selectedCode_run_eq,AngleCode.neg_value]
  rfl

theorem adjacentRotationCode_length {n : ℕ} (hn : 0<n) (t : Fin n) (x : Bits n)
    (a : AngleCode) :
    (adjacentRotationCode hn t x a).length≤2*(2^n*(2*n+1))+2 := by
  have h0 := selectedCode_length hn (Function.update x t false) a
  have h1 := selectedCode_length hn (Function.update x t true) a.neg
  simp only [adjacentRotationCode,List.length_append,List.length_singleton]
  omega

def orientedRotationCode {n : ℕ} (hn : 0<n) (t : Fin n) (x : Bits n)
    (a : AngleCode) : WordCode n :=
  adjacentRotationCode hn t x (signedCode a (x t))

theorem orientedRotationCode_run_eq {n : ℕ} (hn : 0<n) (t : Fin n) (x : Bits n)
    (a : AngleCode) (v : Bits n → ℂ) :
    run (interpret (orientedRotationCode hn t x a)) v=
      run (orientedRotationWord hn t x a.value) v := by
  rw [orientedRotationCode,adjacentRotationCode_run_eq]
  unfold orientedRotationWord
  cases hx : x t <;> simp [signedCode,hx]

def otherWires {n : ℕ} (t : Fin n) : List (Fin n) :=
  ((Finset.univ : Finset (Fin n)).erase t).sort (·≤·)

@[simp] theorem mem_otherWires {n : ℕ} (t j : Fin n) :
    j∈otherWires t ↔ j≠t := by simp [otherWires]

theorem otherWires_length {n : ℕ} (t : Fin n) : (otherWires t).length≤n := by
  simp only [otherWires,Finset.length_sort]
  exact (Finset.card_le_card (Finset.erase_subset _ _)).trans_eq (by simp)

theorem differing_exists {n : ℕ} (x y : Bits n) (h : x≠y) :
    (Finset.univ.filter (fun j : Fin n => y j≠x j)).Nonempty := by
  by_contra hn
  apply h
  funext j
  by_contra hj
  exact hn ⟨j,by simp [Ne.symm hj]⟩

def differingWire {n : ℕ} (x y : Bits n) (h : x≠y) : Fin n :=
  (Finset.univ.filter (fun j : Fin n => y j≠x j)).min' (differing_exists x y h)

theorem differingWire_spec {n : ℕ} (x y : Bits n) (h : x≠y) :
    y (differingWire x y h)≠x (differingWire x y h) :=
  (Finset.mem_filter.mp (Finset.min'_mem
    (Finset.univ.filter (fun j : Fin n => y j≠x j)) (differing_exists x y h))).2

theorem clearBits_otherWires {n : ℕ} (x y : Bits n) (t : Fin n) (ht : y t≠x t) :
    clearBits x (otherWires t) y=flipBit t x := by
  funext j
  rw [clearBits_apply]
  by_cases hj : j=t
  · subst j
    simp only [mem_otherWires,ne_eq,not_true_eq_false,if_false,flipBit,
      Function.update_self]
    cases hy : y t <;> cases hx : x t <;> simp_all
  · simp [hj,flipBit,Function.update_of_ne hj]

def moveCode {n : ℕ} (hn : 0<n) (x : Bits n) :
    List (Fin n) → Bits n → WordCode n
  | [],_ => []
  | j::js,y => if y j=x j then moveCode hn x js y else
      adjacentSwapCode hn j y++moveCode hn x js (Function.update y j (x j))

theorem moveCode_run_eq {n : ℕ} (hn : 0<n) (x : Bits n) (cs : List (Fin n))
    (y : Bits n) (v : Bits n → ℂ) :
    run (interpret (moveCode hn x cs y)) v=run (moveWord hn x cs y) v := by
  induction cs generalizing y v with
  | nil => rfl
  | cons j js ih =>
    by_cases h : y j=x j
    · simp only [moveCode,moveWord,if_pos h,ih]
    · simp only [moveCode,moveWord,if_neg h,interpret_append,run_append,
        ih,adjacentSwapCode_run_eq]

theorem moveCode_length {n : ℕ} (hn : 0<n) (x : Bits n) (cs : List (Fin n))
    (y : Bits n) :
    (moveCode hn x cs y).length≤cs.length*(2^n*(2*n+1)+2) := by
  induction cs generalizing y with
  | nil => simp [moveCode]
  | cons j js ih =>
    by_cases h : y j=x j
    · simp only [moveCode,if_pos h,List.length_cons]
      exact (ih y).trans (Nat.mul_le_mul_right _ (Nat.le_succ _))
    · simp only [moveCode,if_neg h,List.length_append,List.length_cons]
      have h1 := adjacentSwapCode_length hn j y
      have h2 := ih (Function.update y j (x j))
      nlinarith

def swapCode {n : ℕ} (hn : 0<n) (x y : Bits n) : WordCode n :=
  if h : x=y then [] else
    let t := differingWire x y h
    let a := moveCode hn x (otherWires t) y
    a++adjacentSwapCode hn t x++reverseCode a

theorem swapCode_action {n : ℕ} (hn : 0<n) (x y : Bits n) (v : Bits n → ℂ) :
    run (interpret (swapCode hn x y)) v=fun w => v ((Equiv.swap x y) w) := by
  by_cases h : x=y
  · subst y
    simp [swapCode,interpret,run,denote]
  · let t := differingWire x y h
    have ht : y t≠x t := differingWire_spec x y h
    let cs := otherWires t
    let e := moveEquiv x cs y
    have hcs : ∀ j∈cs,j≠t := by intro j hj;exact (mem_otherWires t j).mp hj
    have hx : e x=x := moveEquiv_fixes x cs y t ht hcs
    have hy : e y=flipBit t x :=
      (moveEquiv_source x cs y).trans (clearBits_otherWires x y t ht)
    have hm (u : Bits n → ℂ) :
        run (interpret (moveCode hn x cs y)) u=fun w => u (e.symm w) := by
      rw [moveCode_run_eq,run_moveWord]
    change run (interpret (if h : x=y then [] else
      moveCode hn x (otherWires (differingWire x y h)) y++
        adjacentSwapCode hn (differingWire x y h) x++
        reverseCode (moveCode hn x (otherWires (differingWire x y h)) y))) v=_
    rw [dif_neg h]
    change run (interpret (moveCode hn x cs y++adjacentSwapCode hn t x++
      reverseCode (moveCode hn x cs y))) v=_
    simp only [interpret_append,interpret_reverse,run_append,hm,
      adjacentSwapCode_run_eq,adjacentSwapWord_swap,
      run_reverse_of_equiv _ e hm]
    funext w
    change v (e.symm ((Equiv.swap x (flipBit t x)) (e w)))=_
    have heq : Equiv.swap x (flipBit t x)=Equiv.swap (e x) (e y) := by rw [hx,hy]
    rw [heq,swap_conjugation]

theorem swapCode_length {n : ℕ} (hn : 0<n) (x y : Bits n) :
    (swapCode hn x y).length≤(2*n+1)*(2^n*(2*n+1)+2) := by
  by_cases h : x=y
  · simp [swapCode,h]
  · rw [swapCode,dif_neg h]
    simp only [List.length_append,reverseCode_length]
    have hm := moveCode_length hn x (otherWires (differingWire x y h)) y
    have hc := otherWires_length (differingWire x y h)
    have ha := adjacentSwapCode_length hn (differingWire x y h) x
    nlinarith

def rotationCode {n : ℕ} (hn : 0<n) (x y : Bits n) (h : x≠y)
    (a : AngleCode) : WordCode n :=
  let t := differingWire x y h
  let b := moveCode hn x (otherWires t) y
  b++orientedRotationCode hn t x a++reverseCode b

theorem rotationCode_action {n : ℕ} (hn : 0<n) (x y : Bits n) (h : x≠y)
    (a : AngleCode) (v : Bits n → ℂ) :
    run (interpret (rotationCode hn x y h a)) v=fun w =>
      if w=x then (Real.cos a.value : ℂ)*v x+(Real.sin a.value : ℂ)*v y
      else if w=y then -(Real.sin a.value : ℂ)*v x+(Real.cos a.value : ℂ)*v y
      else v w := by
  let t := differingWire x y h
  have ht : y t≠x t := differingWire_spec x y h
  let cs := otherWires t
  let e := moveEquiv x cs y
  have hcs : ∀ j∈cs,j≠t := by intro j hj;exact (mem_otherWires t j).mp hj
  have hx : e x=x := moveEquiv_fixes x cs y t ht hcs
  have hy : e y=flipBit t x :=
    (moveEquiv_source x cs y).trans (clearBits_otherWires x y t ht)
  have hsx : e.symm x=x := by
    have h := congrArg e.symm hx
    simpa using h.symm
  have hsy : e.symm (flipBit t x)=y := by rw [← hy];simp
  have hm (u : Bits n → ℂ) :
      run (interpret (moveCode hn x cs y)) u=fun w => u (e.symm w) := by
    rw [moveCode_run_eq,run_moveWord]
  change run (interpret (moveCode hn x cs y++orientedRotationCode hn t x a++
    reverseCode (moveCode hn x cs y))) v=_
  simp only [interpret_append,interpret_reverse,run_append,hm,
    orientedRotationCode_run_eq,orientedRotationWord_action,
    run_reverse_of_equiv _ e hm]
  funext w
  change (if e w=x then (Real.cos a.value : ℂ)*v (e.symm x)+
      (Real.sin a.value : ℂ)*v (e.symm (flipBit t x))
    else if e w=flipBit t x then -(Real.sin a.value : ℂ)*v (e.symm x)+
      (Real.cos a.value : ℂ)*v (e.symm (flipBit t x))
    else v (e.symm (e w)))=_
  rw [hsx,hsy,Equiv.symm_apply_apply]
  by_cases hw : w=x
  · subst w
    simp [hx]
  · by_cases hwy : w=y
    · subst w
      simp [hy,flipBit_ne t x,Ne.symm h]
    · have h1 : e w≠x := by rw [← hx];simpa using hw
      have h2 : e w≠flipBit t x := by rw [← hy];simpa using hwy
      simp [h1,h2,hw,hwy]

theorem rotationCode_length {n : ℕ} (hn : 0<n) (x y : Bits n) (h : x≠y)
    (a : AngleCode) :
    (rotationCode hn x y h a).length≤
      2*n*(2^n*(2*n+1)+2)+2*(2^n*(2*n+1))+2 := by
  unfold rotationCode
  simp only [List.length_append,reverseCode_length]
  have hm := moveCode_length hn x (otherWires (differingWire x y h)) y
  have hc := otherWires_length (differingWire x y h)
  have ha := adjacentRotationCode_length hn (differingWire x y h) x
    (signedCode a (x (differingWire x y h)))
  change (orientedRotationCode hn (differingWire x y h) x a).length≤_ at ha
  nlinarith

end EffectiveEncoding

