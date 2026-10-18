import CircuitCompletion.PermutationCompiler
import Mathlib.Logic.Equiv.Fintype

open Matrix
namespace CircuitCompletion

noncomputable def embeddingPermutation {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq α] (e f : ι ↪ α) : Equiv.Perm α := by
  classical
  let c : ↥((Set.range e)ᶜ : Set α) ≃ ↥((Set.range f)ᶜ : Set α) := Fintype.equivOfCardEq (by
    rw [Fintype.card_compl_set,Fintype.card_compl_set]
    rw [← Fintype.card_congr e.toEquivRange,← Fintype.card_congr f.toEquivRange])
  exact ((Equiv.Set.sumCompl (Set.range e)).symm.trans
    (Equiv.sumCongr (e.toEquivRange.symm.trans f.toEquivRange) c)).trans
      (Equiv.Set.sumCompl (Set.range f))

theorem embeddingPermutation_apply {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq α] (e f : ι ↪ α) (i : ι) : embeddingPermutation e f (e i)=f i := by
  classical
  have hinput : e i=(Equiv.Set.sumCompl (Set.range e)) (Sum.inl (e.toEquivRange i)) := rfl
  rw [hinput]
  simp only [embeddingPermutation,Equiv.trans_apply,Equiv.symm_apply_apply,
    Equiv.sumCongr_apply,Sum.map_inl,Equiv.Set.sumCompl_apply_inl,
    Equiv.Set.sumCompl_symm_apply]
  rfl

theorem permutationUnitary_single {α : Type*} [Fintype α] [DecidableEq α]
    (e : Equiv.Perm α) (p : α) (c : ℂ) :
    (permutationUnitary e : Matrix α α ℂ)*ᵥPi.single p c=Pi.single (e p) c := by
  rw [permutationUnitary_action]
  ext w
  simp [Pi.single_apply,e.symm_apply_eq,eq_comm]

/-- Two arbitrary finite coordinate embeddings are related by an explicit
finite permutation completion, then by a genuine elementary circuit. -/
theorem embeddingPermutation_word {ι : Type*} [Fintype ι] {n : ℕ} (hn : 0<n)
    (e f : ι ↪ Bits n) (i : ι) (c : ℂ) :
    run (permutationWord hn (embeddingPermutation e f)) (Pi.single (e i) c)=Pi.single (f i) c := by
  rw [run,permutationWord_denote,permutationUnitary_single,embeddingPermutation_apply]

end CircuitCompletion
