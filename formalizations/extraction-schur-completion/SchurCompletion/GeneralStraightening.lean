import SchurCompletion.WordStraightening

open scoped BigOperators
open Matrix

namespace ExtractionSchur
open SymmetricSupport ExtractionSpectrum ExtractionRankSupport
noncomputable section

def HasDescendingSubsequence (D k l : ℕ) (w : Word D k) : Prop :=
  ∃ p : Fin l ↪o Fin k, StrictAnti (w ∘ p)

def DescendingAvoider (D k s : ℕ) :=
  {w : Word D k // ¬ HasDescendingSubsequence D k (s+1) w}

instance descendingAvoider_finite (D k s : ℕ) : Finite (DescendingAvoider D k s) :=
  Subtype.finite

def descendingAvoiderCount (D k s : ℕ) : ℕ := Nat.card (DescendingAvoider D k s)

theorem strictly_descending_selected_perm_lex_lt (D k l : ℕ) (p : Fin l ↪ Fin k)
    (hp : StrictMono p) (w : Word D k) (hw : StrictAnti (w ∘ p))
    (σ : Equiv.Perm (Fin l)) (hσ : σ ≠ 1) :
    toLex (w ∘ selectedPositionPerm p σ) < toLex w := by
  have hn : {i : Fin l | σ i ≠ i}.Nonempty := by
    by_contra h
    have hh : ∀ i : Fin l, σ i = i := by
      intro i
      by_contra hne
      exact h ⟨i,hne⟩
    exact hσ (Equiv.ext hh)
  obtain ⟨i,hi,hmin⟩ := (wellFounded_lt (α := Fin l)).has_min _ hn
  change σ i ≠ i at hi
  have hfix (j : Fin l) (hj : j < i) : σ j = j := by
    by_contra hne
    exact hmin j hne hj
  have hmove : i < σ i := by
    have hnlt : ¬ σ i < i := by
      intro hlt
      have he := hfix (σ i) hlt
      exact hi (σ.injective he)
    exact lt_of_le_of_ne (le_of_not_gt hnlt) hi.symm
  refine ⟨p i, ?_, ?_⟩
  · intro j hj
    by_cases hjp : j ∈ Set.range p
    · obtain ⟨a,rfl⟩ := hjp
      have hai : a < i := (hp.lt_iff_lt).mp hj
      simp only [Pi.toLex_apply, Function.comp_apply, selectedPositionPerm_apply, hfix a hai]
    · simp only [Pi.toLex_apply, Function.comp_apply, selectedPositionPerm_of_notMem p σ j hjp]
  · simp only [Pi.toLex_apply, Function.comp_apply, selectedPositionPerm_apply]
    exact hw hmove

theorem rankBudget_general_coordinate_restriction_injective (D k s : ℕ)
    (v : Word D k → ℂ) (hv : v ∈ rankBudgetSpace D k s)
    (hz : ∀ w : DescendingAvoider D k s, v w.val = 0) : v = 0 := by
  classical
  have hall : ∀ w : Lex (Word D k), v (ofLex w) = 0 := by
    intro w
    induction w using (wellFounded_lt (α := Lex (Word D k))).induction with
    | h w ih =>
      by_cases hg : ¬ HasDescendingSubsequence D k (s+1) (ofLex w)
      · exact hz ⟨ofLex w,hg⟩
      · obtain ⟨p,hp⟩ := not_not.mp hg
        have hrel := selected_coordinate_relation D k (s+1) s p.toEmbedding (by omega) v hv
          (ofLex w)
        have he : (∑ σ : Equiv.Perm (Fin (s+1)), (Equiv.Perm.sign σ : ℤ) •
            v (ofLex w ∘ selectedPositionPerm p.toEmbedding σ)) = v (ofLex w) := by
          rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin (s+1)))]
          · simp [selectedPositionPerm_one]
          · intro σ hσ hne
            have hsmall := strictly_descending_selected_perm_lex_lt D k (s+1)
              p.toEmbedding p.strictMono (ofLex w) hp σ hne
            have hzero : v (ofLex w ∘ selectedPositionPerm p.toEmbedding σ) = 0 := by
              simpa using ih (toLex (ofLex w ∘ selectedPositionPerm p.toEmbedding σ)) hsmall
            rw [hzero]
            simp
          · simp
        rw [he] at hrel
        exact hrel
  funext w
  exact hall (toLex w)

/-- Actual all-rank support admits an injective restriction to words avoiding
every strict descending subsequence of length s+1. This is proved directly
from actual selected antisymmetrizers. -/
theorem rankBudget_general_rank_le_descendingAvoiderCount (D k s : ℕ) :
    (rankBudgetProjector D k s).rank ≤ descendingAvoiderCount D k s := by
  classical
  letI : Fintype (DescendingAvoider D k s) := Fintype.ofFinite _
  let restriction : rankBudgetSpace D k s →ₗ[ℂ] (DescendingAvoider D k s → ℂ) := {
    toFun := fun v w => v.val w.val
    map_add' := fun u v => rfl
    map_smul' := fun a v => rfl }
  have hinj : Function.Injective restriction := by
    intro u v huv
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply rankBudget_general_coordinate_restriction_injective D k s (u.val-v.val)
      ((rankBudgetSpace D k s).sub_mem u.property v.property)
    intro w
    exact sub_eq_zero.mpr (congrFun huv w)
  rw [rankBudgetProjector_rank]
  calc
    _ ≤ Module.finrank ℂ (DescendingAvoider D k s → ℂ) :=
      LinearMap.finrank_le_finrank_of_injective hinj
    _ = descendingAvoiderCount D k s := by
      rw [Module.finrank_fintype_fun_eq_card, descendingAvoiderCount, Nat.card_eq_fintype_card]

end
end ExtractionSchur
