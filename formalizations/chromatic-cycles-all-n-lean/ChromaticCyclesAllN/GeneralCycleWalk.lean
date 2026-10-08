import ChromaticCyclesAllN.GeneralCycleColoring

namespace ChromaticCycleAll

 def colorSupport {n : ℕ} [NeZero n] {α : Type*}
    (f : Fin n → α) : List α :=
  List.ofFn f ++ [f 0]

 theorem colorSupport_length {n : ℕ} [NeZero n] {α : Type*}
    (f : Fin n → α) :
    (colorSupport f).length = n + 1 := by
  simp [colorSupport]

 theorem colorSupport_get {n : ℕ} [NeZero n] {α : Type*}
    (f : Fin n → α) (i : ℕ) (hi : i < n) :
    (colorSupport f)[i]'(by rw [colorSupport_length]; omega) = f ⟨i,hi⟩ := by
  simp only [colorSupport]
  rw [List.getElem_append_left (by simpa using hi)]
  exact List.getElem_ofFn (by simpa using hi)

 theorem colorSupport_get_last {n : ℕ} [NeZero n] {α : Type*}
    (f : Fin n → α) :
    (colorSupport f)[n]'(by rw [colorSupport_length]; omega) = f 0 := by
  simp [colorSupport, List.getElem_append_right]

 theorem colorSupport_chain {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    {α : Type*} (f : Fin n → α)
    (h : ∀ i, f i ≠ f (i + 1)) :
    List.IsChain (SimpleGraph.completeGraph α).Adj (colorSupport f) := by
  rw [List.isChain_iff_getElem]
  intro i hi
  have hib : i + 1 < n + 1 := by simpa [colorSupport_length] using hi
  by_cases hnext : i + 1 < n
  · have hip : i < n := by omega
    have hfa : (⟨i,hip⟩ : Fin n) + 1 = ⟨i+1,hnext⟩ := by
      apply Fin.ext
      exact Fin.val_add_one_of_lt' (i := ⟨i,hip⟩) hnext
    have hneq : f ⟨i,hip⟩ ≠ f ⟨i+1,hnext⟩ := by
      simpa [hfa] using h ⟨i,hip⟩
    simpa [colorSupport_get f i hip, colorSupport_get f (i+1) hnext,
      SimpleGraph.completeGraph_eq_top] using hneq
  · have hlast : i + 1 = n := by omega
    have hip : i < n := by omega
    have hwrap : (⟨i,hip⟩ : Fin n) + 1 = 0 := by
      apply Fin.ext
      simp [Fin.val_add, Fin.val_one, hlast, Nat.mod_eq_of_lt (show 1 < n by omega)]
    have hneq : f ⟨i,hip⟩ ≠ f 0 := by simpa [hwrap] using h ⟨i,hip⟩
    simpa [colorSupport_get f i hip, hlast, colorSupport_get_last,
      SimpleGraph.completeGraph_eq_top] using hneq

end ChromaticCycleAll
