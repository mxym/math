import ChromaticCyclesAllN.GeneralCycleLoops

namespace ChromaticCycleAll
open SimpleGraph

theorem succClosedWalk_getVert {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    {α : Type*} (f : Fin n → α)
    (h : ∀ i, f i ≠ f (i + 1)) (i : Fin n) :
    (succClosedWalk hn f h).getVert i.val = f i := by
  have hi : i.val ≤ (succClosedWalk hn f h).length := by
    rw [succClosedWalk_length]
    omega
  rw [Walk.getVert_eq_support_getElem _ hi]
  simp only [succClosedWalk_support]
  simpa using colorSupport_get f i.val i.isLt

abbrev ColorLoops (n : ℕ) (α : Type*) :=
  Σ a : α, {p : (completeGraph α).Walk a a // p.length = n}

def toColorLoops {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    {α : Type*} (c : (cycleGraph n).Coloring α) : ColorLoops n α :=
  let f : Fin n → α := fun i => c i
  let h : ∀ i, f i ≠ f (i + 1) := fun i =>
    c.valid (cycle_succ_adj n hn i)
  ⟨f 0, ⟨succClosedWalk hn f h, succClosedWalk_length hn f h⟩⟩

def fromColorLoops {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    {α : Type*} (p : ColorLoops n α) : (cycleGraph n).Coloring α :=
  let f : Fin n → α := fun i => p.2.1.getVert i.val
  Coloring.mk f (proper_of_successor n hn f (by
    intro i
    have hAdj : (completeGraph α).Adj
      (p.2.1.getVert i.val) (p.2.1.getVert (i.val+1)) :=
      p.2.1.adj_getVert_succ (by rw [p.2.2]; exact i.isLt)
    have hNe : p.2.1.getVert i.val ≠ p.2.1.getVert (i.val+1) := by
      simpa [completeGraph_eq_top] using hAdj
    by_cases hi : i.val + 1 < n
    · have hv : ((i+1:Fin n):ℕ) = i.val + 1 :=
        Fin.val_add_one_of_lt' hi
      change p.2.1.getVert i.val ≠ p.2.1.getVert ((i+1:Fin n).val)
      simpa [hv] using hNe
    · have hlast : i.val+1=n := by omega
      have hwrap : (i+1:Fin n) = 0 := by
        apply Fin.ext
        simp [Fin.val_add, hlast]
      have hEnd : p.2.1.getVert n = p.1 := by
        simpa [p.2.2] using p.2.1.getVert_length
      change p.2.1.getVert i.val ≠ p.2.1.getVert ((i+1:Fin n).val)
      simpa [hwrap, hlast, hEnd] using hNe))

end ChromaticCycleAll
