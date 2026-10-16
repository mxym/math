import CircuitCompletion.AdjacentSwap

open Matrix
namespace CircuitCompletion

def flipBit {n : ℕ} (t : Fin n) (x : Bits n) : Bits n :=
  Function.update x t (!x t)

theorem flipBit_ne {n : ℕ} (t : Fin n) (x : Bits n) : flipBit t x≠x := by
  intro h
  have ht := congrFun h t
  simp only [flipBit,Function.update_self] at ht
  cases x t <;> simp_all

theorem eq_of_sameOutside {n : ℕ} (t : Fin n) (w x : Bits n)
    (h : sameOutside t w x) (ht : w t=x t) : w=x := by
  funext j
  by_cases hj : j=t
  · subst j;exact ht
  · exact h j hj

theorem flipBit_involutive {n : ℕ} (t : Fin n) : Function.Involutive (flipBit t) := by
  intro x
  ext j
  by_cases hj : j=t <;> simp [flipBit,hj]

theorem sameOutside_flipBit {n : ℕ} (t : Fin n) (x : Bits n) :
    sameOutside t (flipBit t x) x := by
  intro j hj
  simp [flipBit,Function.update_of_ne hj]

theorem adjacentSwapWord_swap {n : ℕ} (hn : 0<n) (t : Fin n) (x : Bits n)
    (v : Bits n → ℂ) :
    run (adjacentSwapWord hn t x) v=fun w => v ((Equiv.swap x (flipBit t x)) w) := by
  classical
  rw [adjacentSwapWord_action]
  funext w
  by_cases hw : w=x
  · subst w
    simp [Equiv.swap_apply_def,sameOutside,flipBit]
  · by_cases hwf : w=flipBit t x
    · subst w
      rw [if_pos (sameOutside_flipBit t x)]
      change v (flipBit t (flipBit t x))=_
      rw [flipBit_involutive t x]
      simp [Equiv.swap_apply_def,flipBit_ne t x]
    · have ho : ¬sameOutside t w x := by
        intro h
        by_cases ht : w t=x t
        · exact hw (eq_of_sameOutside t w x h ht)
        · apply hwf
          apply eq_of_sameOutside t w (flipBit t x)
          · intro j hj
            simpa [flipBit,Function.update_of_ne hj] using h j hj
          · simp only [flipBit,Function.update_self]
            cases hw' : w t <;> cases hx' : x t <;> simp_all
      simp [ho,Equiv.swap_apply_def,hw,hwf]

theorem run_singleton_swap {n : ℕ} (hn : 0<n) (t : Fin n) (x : Bits n)
    (v : Bits n → ℂ) :
    run (adjacentSwapWord hn t x) v=
      (permutationUnitary (Equiv.swap x (flipBit t x)) : Matrix (Bits n) (Bits n) ℂ)*ᵥv := by
  rw [adjacentSwapWord_swap,permutationUnitary_action]
  rfl

end CircuitCompletion
