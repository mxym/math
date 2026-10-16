import CircuitCompletion.GrayMove

namespace CircuitCompletion

theorem clearBits_except {n : ℕ} (x y : Bits n) (t : Fin n) (ht : y t≠x t) :
    clearBits x ((Finset.univ : Finset (Fin n)).erase t).toList y=flipBit t x := by
  funext j
  rw [clearBits_apply]
  by_cases hj : j=t
  · subst j
    simp only [Finset.mem_toList,Finset.mem_erase,ne_eq,not_true_eq_false,false_and,
      if_false,flipBit,Function.update_self]
    cases hy : y t <;> cases hx : x t <;> simp_all
  · simp [Finset.mem_toList,hj,flipBit,Function.update_of_ne hj]

theorem run_reverse_of_equiv {n : ℕ} (a : Circuit n) (e : Equiv.Perm (Bits n))
    (ha : ∀ v,run a v=fun w => v (e.symm w)) (v : Bits n → ℂ) :
    run (reverseCircuit a) v=fun w => v (e w) := by
  have hf : run a (fun w => v (e w))=v := by
    rw [ha]
    funext w
    simp
  have h := run_reverseCircuit a (fun w => v (e w))
  rwa [hf] at h

theorem swap_conjugation {ι : Type*} [DecidableEq ι] (e : Equiv.Perm ι) (x y w : ι) :
    e.symm ((Equiv.swap (e x) (e y)) (e w))=(Equiv.swap x y) w := by
  by_cases hw : w=x
  · subst w;simp
  · by_cases hwy : w=y
    · subst w;simp
    · have h1 : e w≠e x := by simpa using hw
      have h2 : e w≠e y := by simpa using hwy
      simp [Equiv.swap_apply_def,hw,hwy,h1,h2]

/-- A literal Gray-path circuit for an arbitrary computational transposition.
The recursive path keeps one differing wire untouched so it never meets the
fixed endpoint before the final adjacent transposition. -/
noncomputable def swapWord {n : ℕ} (hn : 0<n) (x y : Bits n) : Circuit n :=
  if h : x=y then [] else
    let t := Classical.choose (show ∃ t,y t≠x t from by
      by_contra h'
      apply h
      funext j
      by_contra hj
      exact h' ⟨j,Ne.symm hj⟩)
    let cs := ((Finset.univ : Finset (Fin n)).erase t).toList
    let a := moveWord hn x cs y
    a++adjacentSwapWord hn t x++reverseCircuit a

theorem swapWord_action {n : ℕ} (hn : 0<n) (x y : Bits n) (v : Bits n → ℂ) :
    run (swapWord hn x y) v=fun w => v ((Equiv.swap x y) w) := by
  classical
  by_cases h : x=y
  · subst y;simp [swapWord,run,denote]
  · simp only [swapWord,dif_neg h]
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
    change run (moveWord hn x cs y++adjacentSwapWord hn t x++
      reverseCircuit (moveWord hn x cs y)) v=_
    simp only [run_append,run_moveWord,adjacentSwapWord_swap,
      run_reverse_of_equiv _ e (run_moveWord hn x cs y)]
    funext w
    change v (e.symm ((Equiv.swap x (flipBit t x)) (e w)))=_
    have heq : Equiv.swap x (flipBit t x)=Equiv.swap (e x) (e y) := by rw [hx,hy]
    rw [heq,swap_conjugation]

theorem swapWord_length {n : ℕ} (hn : 0<n) (x y : Bits n) :
    (swapWord hn x y).length≤(2*n+1)*(2^n*(2*n+1)+2) := by
  classical
  by_cases h : x=y
  · simp [swapWord,h]
  · simp only [swapWord,dif_neg h,List.length_append,reverseCircuit_length]
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
    have ha := adjacentSwapWord_length hn
      (Classical.choose (show ∃ t,y t≠x t from by
        by_contra h'
        apply h
        funext j
        by_contra hj
        exact h' ⟨j,Ne.symm hj⟩)) x
    nlinarith

end CircuitCompletion
