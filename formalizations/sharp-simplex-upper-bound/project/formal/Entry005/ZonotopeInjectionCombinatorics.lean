import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.Basic.Real.Basic

noncomputable section
open scoped BigOperators

namespace Entry005

/-- Remove the unused zero index from the target of an embedding. -/
def zonotopeAvoidZeroEmbeddingEquiv (n m : ℕ) :
    {σ : Fin n ↪ Fin (m + 1) // ∀ i, σ i ≠ 0} ≃ (Fin n ↪ Fin m) where
  toFun σ := {
    toFun i := (σ.val i).pred (σ.property i)
    inj' i j h := σ.val.injective (by
      simpa only [Fin.succ_pred] using congrArg Fin.succ h) }
  invFun τ := ⟨τ.trans (Fin.succEmb m), fun i => Fin.succ_ne_zero (τ i)⟩
  left_inv σ := by
    apply Subtype.ext
    apply Function.Embedding.ext
    intro i
    change ((σ.val i).pred (σ.property i)).succ = σ.val i
    exact Fin.succ_pred _ _
  right_inv τ := by
    apply Function.Embedding.ext
    intro i
    change (τ i).succ.pred (Fin.succ_ne_zero (τ i)) = τ i
    exact Fin.pred_succ _

/-- Add the zero target index as the first entry of an injective tuple. -/
def zonotopeZeroFirstEmbedding {d m : ℕ} (τ : Fin d ↪ Fin m) :
    Fin (d + 1) ↪ Fin (m + 1) where
  toFun := Fin.cons 0 (fun k => (τ k).succ)
  inj' := Fin.cons_injective_iff.mpr ⟨by
    rintro ⟨k, hk⟩
    exact Fin.succ_ne_zero (τ k) hk,
    (Fin.succ_injective m).comp τ.injective⟩

private theorem zonotope_swap_tail_ne_zero {d m : ℕ}
    (i : Fin (d + 1)) (σ : Fin (d + 1) ↪ Fin (m + 1)) (hi : σ i = 0)
    (k : Fin d) : σ (Equiv.swap 0 i k.succ) ≠ 0 := by
  intro h
  have heq := σ.injective (h.trans hi.symm)
  have hswap := congrArg (Equiv.swap 0 i) heq
  simp at hswap

/-- Move the unique slot hitting zero to the first position, then remove it. -/
def zonotopeAtZeroEmbeddingEquiv (d m : ℕ) (i : Fin (d + 1)) :
    {σ : Fin (d + 1) ↪ Fin (m + 1) // σ i = 0} ≃ (Fin d ↪ Fin m) where
  toFun σ := {
    toFun k := (σ.val (Equiv.swap 0 i k.succ)).pred
      (zonotope_swap_tail_ne_zero i σ.val σ.property k)
    inj' k l h := Fin.succ_injective d ((Equiv.swap 0 i).injective
      (σ.val.injective (by simpa only [Fin.succ_pred] using congrArg Fin.succ h))) }
  invFun τ := ⟨(Equiv.swap 0 i).toEmbedding.trans (zonotopeZeroFirstEmbedding τ), by
    simp [zonotopeZeroFirstEmbedding]⟩
  left_inv σ := by
    apply Subtype.ext
    apply Function.Embedding.ext
    intro k
    obtain ⟨l, rfl⟩ := (Equiv.swap 0 i).surjective k
    induction l using Fin.cases with
    | zero => simpa [zonotopeZeroFirstEmbedding] using σ.property.symm
    | succ l =>
      simp only [Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
        Equiv.swap_apply_self, zonotopeZeroFirstEmbedding]
      exact Fin.succ_pred (σ.val (Equiv.swap 0 i l.succ))
        (zonotope_swap_tail_ne_zero i σ.val σ.property l)
  right_inv τ := by
    apply Function.Embedding.ext
    intro k
    simp [zonotopeZeroFirstEmbedding]

private theorem zonotope_sum_subtype_ite {α : Type*} [Fintype α]
    (p : α → Prop) [DecidablePred p] (F : α → ℝ) :
    (∑ x, if p x then F x else 0) = ∑ x : {x : α // p x}, F x.val := by
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

/-- Every embedding either avoids zero or hits it at a unique input slot. -/
theorem zonotope_embedding_sum_partition_zero (d m : ℕ)
    (F : (Fin (d + 1) ↪ Fin (m + 1)) → ℝ) :
    (∑ σ, F σ) =
      (∑ σ : {σ : Fin (d + 1) ↪ Fin (m + 1) // ∀ i, σ i ≠ 0}, F σ.val) +
        ∑ i : Fin (d + 1), ∑ σ : {σ : Fin (d + 1) ↪ Fin (m + 1) // σ i = 0},
          F σ.val := by
  classical
  have hpoint (σ : Fin (d + 1) ↪ Fin (m + 1)) : F σ =
      (if ∀ i, σ i ≠ 0 then F σ else 0) +
        ∑ i : Fin (d + 1), if σ i = 0 then F σ else 0 := by
    by_cases ha : ∀ i, σ i ≠ 0
    · simp [ha]
    · obtain ⟨i, hi⟩ := not_forall.mp ha
      have hi0 : σ i = 0 := not_not.mp hi
      rw [ite_eq_right ha, zero_add]
      symm
      calc
        (∑ j : Fin (d + 1), if σ j = 0 then F σ else 0) =
            if σ i = 0 then F σ else 0 := by
          apply Finset.sum_eq_single i
          · intro j _ hji
            have hj0 : σ j ≠ 0 := fun h => hji (σ.injective (h.trans hi0.symm))
            simp [hj0]
          · simp
        _ = F σ := by rw [ite_eq_left hi0]
  calc
    (∑ σ, F σ) = ∑ σ, ((if ∀ i, σ i ≠ 0 then F σ else 0) +
        ∑ i : Fin (d + 1), if σ i = 0 then F σ else 0) :=
      Finset.sum_congr rfl (fun σ _ => hpoint σ)
    _ = (∑ σ, if ∀ i, σ i ≠ 0 then F σ else 0) +
        ∑ i : Fin (d + 1), ∑ σ, if σ i = 0 then F σ else 0 := by
      rw [Finset.sum_add_distrib, Finset.sum_comm]
    _ = _ := by simp_rw [zonotope_sum_subtype_ite]

/-- Absolute values of alternating maps are unchanged by swapping two slots. -/
theorem zonotope_alternating_abs_swap {E : Type*} [AddCommGroup E] [Module ℝ E]
    {d : ℕ} (f : E [⋀^Fin (d + 1)]→ₗ[ℝ] ℝ) (u : Fin (d + 1) → E)
    (i : Fin (d + 1)) : |f (u ∘ Equiv.swap 0 i)| = |f u| := by
  by_cases hi : (0 : Fin (d + 1)) = i
  · subst i
    simp
  · rw [f.map_swap u hi, abs_neg]

theorem alternating_injection_sum_cons {E : Type*} [AddCommGroup E] [Module ℝ E]
    (d m : ℕ) (f : E [⋀^Fin (d + 1)]→ₗ[ℝ] ℝ) (v : E) (g : Fin m → E) :
    (∑ σ : Fin (d + 1) ↪ Fin (m + 1),
      |f (fun i => (Fin.cons v g : Fin (m + 1) → E) (σ i))|) =
      (∑ σ : Fin (d + 1) ↪ Fin m, |f (fun i => g (σ i))|) +
        (d + 1 : ℝ) * (∑ τ : Fin d ↪ Fin m, |f (Fin.cons v (fun i => g (τ i)))|) := by
  classical
  rw [zonotope_embedding_sum_partition_zero]
  have havoid :
      (∑ σ : {σ : Fin (d + 1) ↪ Fin (m + 1) // ∀ i, σ i ≠ 0},
        |f (fun i => (Fin.cons v g : Fin (m + 1) → E) (σ.val i))|) =
      ∑ σ : Fin (d + 1) ↪ Fin m, |f (fun i => g (σ i))| := by
    apply Fintype.sum_equiv (zonotopeAvoidZeroEmbeddingEquiv (d + 1) m)
    intro σ
    congr 2
    funext i
    change (Fin.cons v g : Fin (m + 1) → E) (σ.val i) =
      g ((σ.val i).pred (σ.property i))
    conv_lhs => rw [← Fin.succ_pred (σ.val i) (σ.property i)]
    rw [Fin.cons_succ]
  have hhit (i : Fin (d + 1)) :
      (∑ σ : {σ : Fin (d + 1) ↪ Fin (m + 1) // σ i = 0},
        |f (fun j => (Fin.cons v g : Fin (m + 1) → E) (σ.val j))|) =
      ∑ τ : Fin d ↪ Fin m, |f (Fin.cons v (fun j => g (τ j)))| := by
    apply Fintype.sum_equiv (zonotopeAtZeroEmbeddingEquiv d m i)
    intro σ
    let u : Fin (d + 1) → E := fun j => (Fin.cons v g : Fin (m + 1) → E) (σ.val j)
    have hnorm : u ∘ Equiv.swap 0 i =
        Fin.cons v (fun j => g ((zonotopeAtZeroEmbeddingEquiv d m i σ) j)) := by
      funext j
      induction j using Fin.cases with
      | zero => simp [u, σ.property]
      | succ j =>
        change (Fin.cons v g : Fin (m + 1) → E) (σ.val (Equiv.swap 0 i j.succ)) =
          g ((σ.val (Equiv.swap 0 i j.succ)).pred
            (zonotope_swap_tail_ne_zero i σ.val σ.property j))
        conv_lhs => rw [← Fin.succ_pred (σ.val (Equiv.swap 0 i j.succ))
          (zonotope_swap_tail_ne_zero i σ.val σ.property j)]
        rw [Fin.cons_succ]
    calc
      |f (fun j => (Fin.cons v g : Fin (m + 1) → E) (σ.val j))| =
          |f (u ∘ Equiv.swap 0 i)| :=
        (zonotope_alternating_abs_swap f u i).symm
      _ = _ := by rw [hnorm]
  rw [havoid]
  simp_rw [hhit]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one]

end Entry005
