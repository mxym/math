import ChromaticCyclesAllN.GeneralColorLoopCard

namespace ChromaticCycleAll
open SimpleGraph

theorem toColorLoops_injective {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    {α : Type*} : Function.Injective
      (toColorLoops hn (α := α)) := by
  intro c₁ c₂ he
  ext i
  have hh := congrArg (fun z : ColorLoops n α => z.2.1.getVert i.val) he
  have h₁ : (toColorLoops hn c₁).2.1.getVert i.val = c₁ i :=
    succClosedWalk_getVert hn (fun j => c₁ j)
       (fun j => c₁.valid (cycle_succ_adj n hn j)) i
  have h₂ : (toColorLoops hn c₂).2.1.getVert i.val = c₂ i :=
    succClosedWalk_getVert hn (fun j => c₂ j)
       (fun j => c₂.valid (cycle_succ_adj n hn j)) i
  simpa [h₁, h₂] using hh

theorem fromColorLoops_injective {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    {α : Type*} : Function.Injective
      (fromColorLoops hn (α := α)) := by
  rintro ⟨a, ⟨p, hp⟩⟩ ⟨b, ⟨q, hq⟩⟩ he
  have hfirst : a = b := by
    have hh := congrArg (fun c : (cycleGraph n).Coloring α => c 0) he
    dsimp [fromColorLoops] at hh
    change p.getVert 0 = q.getVert 0 at hh
    simpa using hh
  subst b
  have hpq : p = q := by
    apply Walk.ext_getVert_le_length
    · exact hp.trans hq.symm
    · intro k hk
      by_cases hklt : k < n
      · have hh := congrArg
           (fun c : (cycleGraph n).Coloring α => c ⟨k,hklt⟩) he
        dsimp [fromColorLoops] at hh
        change p.getVert k = q.getVert k at hh
        exact hh
      · have hkeq : k = n := by rw [hp] at hk; omega
        subst k
        simpa [hp,hq] using (show p.getVert p.length = q.getVert q.length by
          simp [Walk.getVert_length])
  have hsub : (⟨p,hp⟩ : {w : (completeGraph α).Walk a a // w.length = n}) =
      ⟨q,hq⟩ := Subtype.ext hpq
  exact congrArg (fun z : {w : (completeGraph α).Walk a a // w.length = n} =>
      (⟨a,z⟩ : ColorLoops n α)) hsub

theorem coloring_card_eq_trace_all (n q : ℕ) [NeZero n] (hn : 3 ≤ n) :
    (Fintype.card ((cycleGraph n).Coloring (Fin q)) : ℤ) =
      Matrix.trace ((completeGraph (Fin q)).adjMatrix ℤ ^ n) := by
  have hc : Fintype.card ((cycleGraph n).Coloring (Fin q)) =
      Fintype.card (ColorLoops n (Fin q)) := by
    apply Nat.le_antisymm
    · exact Fintype.card_le_of_injective
        (toColorLoops hn) (toColorLoops_injective hn)
    · exact Fintype.card_le_of_injective
        (fromColorLoops hn) (fromColorLoops_injective hn)
  rw [hc, Fintype.card_sigma]
  simp only [Nat.cast_sum, Matrix.trace, Matrix.diag]
  apply Finset.sum_congr rfl
  intro a ha
  exact ((completeGraph (Fin q)).adjMatrix_pow_apply_eq_card_walk n a a).symm

end ChromaticCycleAll
