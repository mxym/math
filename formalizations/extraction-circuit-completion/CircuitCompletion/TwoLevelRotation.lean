import CircuitCompletion.AdjacentRotation
import CircuitCompletion.GraySwap

namespace CircuitCompletion

theorem sameOutside_cases {n : ℕ} (t : Fin n) (w x : Bits n)
    (h : sameOutside t w x) : w=x ∨ w=flipBit t x := by
  by_cases ht : w t=x t
  · exact Or.inl (eq_of_sameOutside t w x h ht)
  · right
    apply eq_of_sameOutside t w (flipBit t x)
    · intro j hj;simpa [flipBit,Function.update_of_ne hj] using h j hj
    · simp only [flipBit,Function.update_self]
      cases hw : w t <;> cases hx : x t <;> simp_all

noncomputable def orientedRotationWord {n : ℕ} (hn : 0<n) (t : Fin n) (x : Bits n)
    (θ : ℝ) : Circuit n := adjacentRotationWord hn t x (if x t then -θ else θ)

theorem orientedRotationWord_action {n : ℕ} (hn : 0<n) (t : Fin n) (x : Bits n)
    (θ : ℝ) (v : Bits n → ℂ) :
    run (orientedRotationWord hn t x θ) v=fun w =>
      if w=x then (Real.cos θ : ℂ)*v x+(Real.sin θ : ℂ)*v (flipBit t x)
      else if w=flipBit t x then -(Real.sin θ : ℂ)*v x+(Real.cos θ : ℂ)*v (flipBit t x)
      else v w := by
  classical
  rw [orientedRotationWord,adjacentRotationWord_action]
  funext w
  have hne := flipBit_ne t x
  have hup : Function.update x t (x t)=x := Function.update_eq_self t x
  by_cases hw : w=x
  · subst w
    have ho : sameOutside t x x := by intro j hj;rfl
    rw [if_pos ho,if_pos rfl]
    cases hx : x t <;> simp only [hx] at hup
    all_goals simp [hx,Real.cos_neg,Real.sin_neg,flipBit,hup]
    all_goals ring
  · by_cases hwf : w=flipBit t x
    · subst w
      rw [if_pos (sameOutside_flipBit t x),if_neg hne,if_pos rfl]
      cases hx : x t <;> simp only [hx] at hup
      all_goals simp [hx,Real.cos_neg,Real.sin_neg,flipBit,hup]
      all_goals ring
    · have ho : ¬sameOutside t w x := by
        intro ho
        rcases sameOutside_cases t w x ho with h|h
        · exact hw h
        · exact hwf h
      simp [ho,hw,hwf]

theorem orientedRotationWord_length {n : ℕ} (hn : 0<n) (t : Fin n) (x : Bits n) (θ : ℝ) :
    (orientedRotationWord hn t x θ).length≤2*(2^n*(2*n+1))+2 :=
  adjacentRotationWord_length hn t x _

/-- Selected real plane rotation, compiled via a Gray path and actual
ancilla-free Pauli phase words. It fixes every other computational string. -/
noncomputable def rotationWord {n : ℕ} (hn : 0<n) (x y : Bits n) (h : x≠y) (θ : ℝ) : Circuit n :=
  let t := Classical.choose (show ∃ t,y t≠x t from by
    by_contra h'
    apply h
    funext j
    by_contra hj
    exact h' ⟨j,Ne.symm hj⟩)
  let cs := ((Finset.univ : Finset (Fin n)).erase t).toList
  let a := moveWord hn x cs y
  a++orientedRotationWord hn t x θ++reverseCircuit a

theorem rotationWord_action {n : ℕ} (hn : 0<n) (x y : Bits n) (h : x≠y) (θ : ℝ)
    (v : Bits n → ℂ) :
    run (rotationWord hn x y h θ) v=fun w =>
      if w=x then (Real.cos θ : ℂ)*v x+(Real.sin θ : ℂ)*v y
      else if w=y then -(Real.sin θ : ℂ)*v x+(Real.cos θ : ℂ)*v y
      else v w := by
  classical
  let hex : ∃ t,y t≠x t := by
    by_contra h'
    apply h
    funext j
    by_contra hj
    exact h' ⟨j,Ne.symm hj⟩
  let t := Classical.choose hex
  have ht : y t≠x t := Classical.choose_spec hex
  let cs := ((Finset.univ : Finset (Fin n)).erase t).toList
  let e := moveEquiv x cs y
  have hcs : ∀ j∈cs,j≠t := by
    intro j hj
    exact (Finset.mem_erase.mp (Finset.mem_toList.mp hj)).1
  have hx : e x=x := moveEquiv_fixes x cs y t ht hcs
  have hy : e y=flipBit t x := (moveEquiv_source x cs y).trans (clearBits_except x y t ht)
  have hsx : e.symm x=x := by
    have h := congrArg e.symm hx
    simpa using h.symm
  have hsy : e.symm (flipBit t x)=y := by rw [← hy];simp
  change run (moveWord hn x cs y++orientedRotationWord hn t x θ++
    reverseCircuit (moveWord hn x cs y)) v=_
  simp only [run_append,run_moveWord,orientedRotationWord_action,
    run_reverse_of_equiv _ e (run_moveWord hn x cs y)]
  funext w
  change (if e w=x then (Real.cos θ : ℂ)*v (e.symm x)+
      (Real.sin θ : ℂ)*v (e.symm (flipBit t x))
    else if e w=flipBit t x then -(Real.sin θ : ℂ)*v (e.symm x)+
      (Real.cos θ : ℂ)*v (e.symm (flipBit t x))
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

theorem rotationWord_length {n : ℕ} (hn : 0<n) (x y : Bits n) (h : x≠y) (θ : ℝ) :
    (rotationWord hn x y h θ).length≤
      2*n*(2^n*(2*n+1)+2)+2*(2^n*(2*n+1))+2 := by
  unfold rotationWord
  simp only [List.length_append,reverseCircuit_length]
  have hm := moveWord_length hn x
    ((Finset.univ : Finset (Fin n)).erase
      (Classical.choose (show ∃ t,y t≠x t from by
        by_contra h'
        apply h
        funext j
        by_contra hj
        exact h' ⟨j,Ne.symm hj⟩))).toList y
  have hc : (((Finset.univ : Finset (Fin n)).erase
      (Classical.choose (show ∃ t,y t≠x t from by
        by_contra h'
        apply h
        funext j
        by_contra hj
        exact h' ⟨j,Ne.symm hj⟩))).toList).length≤n := by
    simp only [Finset.length_toList]
    exact (Finset.card_le_card (Finset.erase_subset _ _)).trans_eq (by simp)
  have ha := orientedRotationWord_length hn
    (Classical.choose (show ∃ t,y t≠x t from by
      by_contra h'
      apply h
      funext j
      by_contra hj
      exact h' ⟨j,Ne.symm hj⟩)) x θ
  nlinarith

end CircuitCompletion
