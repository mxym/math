import SchurCompletion.WordPatternCount
import SchurCompletion.RankCentralSupport
import Mathlib.GroupTheory.Perm.ViaEmbedding

open scoped BigOperators
open Matrix

namespace ExtractionSchur
open SymmetricSupport ExtractionSpectrum ExtractionRankSupport
noncomputable section

def selectedPositionPerm {l k : ℕ} (p : Fin l ↪ Fin k)
    (σ : Equiv.Perm (Fin l)) : Equiv.Perm (Fin k) := σ.viaEmbedding p

theorem selectedPositionPerm_apply {l k : ℕ} (p : Fin l ↪ Fin k)
    (σ : Equiv.Perm (Fin l)) (i : Fin l) :
    selectedPositionPerm p σ (p i) = p (σ i) := Equiv.Perm.viaEmbedding_apply _ _ _

theorem selectedPositionPerm_of_notMem {l k : ℕ} (p : Fin l ↪ Fin k)
    (σ : Equiv.Perm (Fin l)) (i : Fin k) (hi : i ∉ Set.range p) :
    selectedPositionPerm p σ i = i := Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hi

theorem selectedPositionPerm_one {l k : ℕ} (p : Fin l ↪ Fin k) :
    selectedPositionPerm p 1 = 1 := (Equiv.Perm.viaEmbeddingHom p).map_one

theorem selectedPositionPerm_inv {l k : ℕ} (p : Fin l ↪ Fin k)
    (σ : Equiv.Perm (Fin l)) :
    selectedPositionPerm p σ⁻¹ = (selectedPositionPerm p σ)⁻¹ :=
  (Equiv.Perm.viaEmbeddingHom p).map_inv σ

theorem selectedPositionPerm_conjugate (l t : ℕ) (p : Fin l ↪ Fin (l+t))
    (τ : Equiv.Perm (Fin (l+t))) (hτ : ∀ i, τ (Fin.castAdd t i) = p i)
    (σ : Equiv.Perm (Fin l)) :
    selectedPositionPerm p σ = τ * prefixPositionPerm l t σ * τ⁻¹ := by
  apply Equiv.ext
  intro x
  obtain ⟨y,rfl⟩ := τ.surjective x
  induction y using Fin.addCases with
  | left i =>
    have hpre : τ.symm (p i) = Fin.castAdd t i := by rw [← hτ i, τ.symm_apply_apply]
    change selectedPositionPerm p σ (τ (Fin.castAdd t i)) =
      τ (prefixPositionPerm l t σ (τ.symm (τ (Fin.castAdd t i))))
    rw [τ.symm_apply_apply, prefixPositionPerm_left, hτ, hτ, selectedPositionPerm_apply]
  | right j =>
    have hn : τ (Fin.natAdd l j) ∉ Set.range p := by
      rintro ⟨i,hi⟩
      rw [← hτ i] at hi
      have he := congrArg Fin.val (τ.injective hi)
      simp only [Fin.val_castAdd, Fin.val_natAdd] at he
      omega
    rw [selectedPositionPerm_of_notMem p σ _ hn]
    change τ (Fin.natAdd l j) =
      τ (prefixPositionPerm l t σ (τ.symm (τ (Fin.natAdd l j))))
    rw [τ.symm_apply_apply, prefixPositionPerm_right]

def selectedAntisymmetrizer (D k l : ℕ) (p : Fin l ↪ Fin k) :
    Matrix (Word D k) (Word D k) ℂ :=
  ∑ σ : Equiv.Perm (Fin l), (Equiv.Perm.sign σ : ℤ) •
    copyPermutationMatrix D k (selectedPositionPerm p σ)⁻¹

theorem selectedAntisymmetrizer_conjugate (D l t : ℕ) (p : Fin l ↪ Fin (l+t))
    (τ : Equiv.Perm (Fin (l+t))) (hτ : ∀ i, τ (Fin.castAdd t i) = p i) :
    selectedAntisymmetrizer D (l+t) l p =
      copyPermutationMatrix D (l+t) τ * prefixAntisymmetrizer D l t *
        (copyPermutationMatrix D (l+t) τ)ᴴ := by
  simp only [selectedAntisymmetrizer, prefixAntisymmetrizer, Matrix.mul_sum,
    Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, copyPermutationMatrix_star,
    copyPermutationMatrix_mul]
  apply Finset.sum_congr rfl
  intro σ hσ
  congr 2
  rw [selectedPositionPerm_conjugate l t p τ hτ σ]
  simp [mul_assoc]

theorem selectedAntisymmetrizer_mul_rankBudgetProjector (D k l s : ℕ)
    (p : Fin l ↪ Fin k) (hsl : s < l) :
    selectedAntisymmetrizer D k l p * rankBudgetProjector D k s = 0 := by
  have hlk : l ≤ k := by simpa using Fintype.card_le_of_injective p p.injective
  obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le hlk
  obtain ⟨τ,hτ⟩ := Equiv.Perm.exists_extending_pair
    (Fin.castAdd t : Fin l → Fin (l+t)) p (Fin.castAdd_injective l t) p.injective
  rw [selectedAntisymmetrizer_conjugate D l t p τ hτ]
  exact conjugate_prefixAntisymmetrizer_mul_rankBudgetProjector D l t s hsl τ

theorem copyPermutation_mulVec_apply (D k : ℕ) (σ : Equiv.Perm (Fin k))
    (v : Word D k → ℂ) (w : Word D k) :
    (copyPermutationMatrix D k σ *ᵥ v) w = v (w ∘ σ) := by
  rw [copyPermutationMatrix, Matrix.permMatrix_mulVec]
  rfl

/-- Selected coordinate determinants vanish on the actual rank-budget space. -/
theorem selected_coordinate_relation (D k l s : ℕ) (p : Fin l ↪ Fin k)
    (hsl : s < l) (v : Word D k → ℂ) (hv : v ∈ rankBudgetSpace D k s)
    (w : Word D k) :
    (∑ σ : Equiv.Perm (Fin l), (Equiv.Perm.sign σ : ℤ) •
      v (w ∘ selectedPositionPerm p σ)) = 0 := by
  have hzero : selectedAntisymmetrizer D k l p *ᵥ v = 0 := by
    rw [← rankBudgetProjector_fixes D k s v hv, Matrix.mulVec_mulVec,
      selectedAntisymmetrizer_mul_rankBudgetProjector D k l s p hsl, Matrix.zero_mulVec]
  have h := congrFun hzero w
  simp only [selectedAntisymmetrizer, Matrix.sum_mulVec, Matrix.smul_mulVec,
    Finset.sum_apply, Pi.smul_apply, copyPermutation_mulVec_apply, Pi.zero_apply,
    ← selectedPositionPerm_inv] at h
  have hreindex := Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin l)))
    (fun σ => (Equiv.Perm.sign σ : ℤ) • v (w ∘ selectedPositionPerm p σ))
  have hr : (∑ σ : Equiv.Perm (Fin l), (Equiv.Perm.sign σ : ℤ) •
      v (w ∘ selectedPositionPerm p σ⁻¹)) =
      ∑ σ : Equiv.Perm (Fin l), (Equiv.Perm.sign σ : ℤ) •
        v (w ∘ selectedPositionPerm p σ) := by
    simpa only [Equiv.inv_apply, Equiv.Perm.sign_inv] using hreindex
  exact hr.symm.trans h

theorem descending_selected_perm_lex_lt (D k : ℕ) (p : Fin D ↪ Fin k)
    (hp : StrictMono p) (w : Word D k) (hw : ∀ i, w (p i) = Fin.rev i)
    (σ : Equiv.Perm (Fin D)) (hσ : σ ≠ 1) :
    toLex (w ∘ selectedPositionPerm p σ) < toLex w := by
  have hn : {i : Fin D | σ i ≠ i}.Nonempty := by
    by_contra h
    have hh : ∀ i : Fin D, σ i = i := by
      intro i
      by_contra hne
      exact h ⟨i,hne⟩
    exact hσ (Equiv.ext hh)
  obtain ⟨i,hi,hmin⟩ := (wellFounded_lt (α := Fin D)).has_min _ hn
  change σ i ≠ i at hi
  have hfix (j : Fin D) (hj : j < i) : σ j = j := by
    by_contra hne
    exact hmin j hne hj
  have hmove : i < σ i := by
    have hnlt : ¬ σ i < i := by
      intro hlt
      have he := hfix (σ i) hlt
      have hei := σ.injective he
      exact hi hei
    exact lt_of_le_of_ne (le_of_not_gt hnlt) hi.symm
  refine ⟨p i, ?_, ?_⟩
  · intro j hj
    by_cases hjp : j ∈ Set.range p
    · obtain ⟨a,rfl⟩ := hjp
      have hai : a < i := (hp.lt_iff_lt).mp hj
      simp only [Pi.toLex_apply, Function.comp_apply, selectedPositionPerm_apply, hfix a hai]
    · simp only [Pi.toLex_apply, Function.comp_apply, selectedPositionPerm_of_notMem p σ j hjp]
  · simp only [Pi.toLex_apply, Function.comp_apply, selectedPositionPerm_apply, hw]
    exact Fin.rev_lt_rev.mpr hmove


def descendingPattern (D : ℕ) : List (Fin D) := List.ofFn (Fin.rev : Fin D → Fin D)

theorem descendingPattern_occurrence (D k : ℕ) (w : Word D k) :
    (descendingPattern D).Sublist (List.ofFn w) ↔
      ∃ p : Fin D ↪o Fin k, ∀ i, w (p i) = Fin.rev i := by
  change (List.ofFn (Fin.rev : Fin D → Fin D)).Sublist (List.ofFn w) ↔ _
  rw [List.sublist_iff_exists_fin_orderEmbedding_get_eq]
  have hd : (List.ofFn (Fin.rev : Fin D → Fin D)).length = D := by simp
  have hk : (List.ofFn w).length = k := by simp
  constructor
  · rintro ⟨p,hp⟩
    let q : Fin D ↪o Fin k := OrderEmbedding.ofStrictMono
      (fun i => Fin.cast hk (p (Fin.cast hd.symm i))) (by
        intro i j hij
        exact p.strictMono hij)
    refine ⟨q,?_⟩
    intro i
    have hi := (hp (Fin.cast hd.symm i)).symm
    simp only [List.get_eq_getElem, List.getElem_ofFn] at hi
    convert hi using 1 <;> rfl
  · rintro ⟨p,hp⟩
    let q : Fin (List.ofFn (Fin.rev : Fin D → Fin D)).length ↪o Fin (List.ofFn w).length :=
      OrderEmbedding.ofStrictMono (fun i => Fin.cast hk.symm (p (Fin.cast hd i))) (by
        intro i j hij
        exact p.strictMono hij)
    refine ⟨q,?_⟩
    intro i
    have hi := (hp (Fin.cast hd i)).symm
    simp only [List.get_eq_getElem, List.getElem_ofFn]
    convert hi using 1 <;> rfl

theorem rankBudget_coordinate_restriction_injective (D k : ℕ) (hD : 0 < D)
    (v : Word D k → ℂ) (hv : v ∈ rankBudgetSpace D k (D-1))
    (hz : ∀ w : AvoidPattern D k (descendingPattern D), v w.val = 0) : v = 0 := by
  classical
  have hall : ∀ w : Lex (Word D k), v (ofLex w) = 0 := by
    intro w
    induction w using (wellFounded_lt (α := Lex (Word D k))).induction with
    | h w ih =>
      by_cases hg : ¬ (descendingPattern D).Sublist (List.ofFn (ofLex w))
      · exact hz ⟨ofLex w,hg⟩
      · obtain ⟨p,hp⟩ := (descendingPattern_occurrence D k (ofLex w)).mp (not_not.mp hg)
        have hrel := selected_coordinate_relation D k D (D-1) p.toEmbedding (by omega) v hv
          (ofLex w)
        have he : (∑ σ : Equiv.Perm (Fin D), (Equiv.Perm.sign σ : ℤ) •
            v (ofLex w ∘ selectedPositionPerm p.toEmbedding σ)) = v (ofLex w) := by
          rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin D))]
          · simp [selectedPositionPerm_one]
          · intro σ hσ hne
            have hsmall := descending_selected_perm_lex_lt D k p.toEmbedding p.strictMono
              (ofLex w) hp σ hne
            have hzero : v (ofLex w ∘ selectedPositionPerm p.toEmbedding σ) = 0 := by
              simpa using ih (toLex (ofLex w ∘ selectedPositionPerm p.toEmbedding σ)) hsmall
            rw [hzero]
            simp
          · simp
        rw [he] at hrel
        exact hrel
  funext w
  exact hall (toLex w)

/-- A genuine support-rank upper bound from actual alternating relations and
word straightening, with no decomposition or rank certificate as input. -/
theorem rankBudget_rank_le_descending_avoiders (D k : ℕ) (hD : 0 < D) :
    (rankBudgetProjector D k (D-1)).rank ≤
      avoidPatternCount D k (descendingPattern D) := by
  classical
  letI : Fintype (AvoidPattern D k (descendingPattern D)) := Fintype.ofFinite _
  let restriction : rankBudgetSpace D k (D-1) →ₗ[ℂ]
      (AvoidPattern D k (descendingPattern D) → ℂ) := {
    toFun := fun v w => v.val w.val
    map_add' := fun u v => rfl
    map_smul' := fun a v => rfl }
  have hinj : Function.Injective restriction := by
    intro u v huv
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply rankBudget_coordinate_restriction_injective D k hD (u.val-v.val)
      ((rankBudgetSpace D k (D-1)).sub_mem u.property v.property)
    intro w
    exact sub_eq_zero.mpr (congrFun huv w)
  rw [rankBudgetProjector_rank]
  calc
    _ ≤ Module.finrank ℂ (AvoidPattern D k (descendingPattern D) → ℂ) :=
      LinearMap.finrank_le_finrank_of_injective hinj
    _ = avoidPatternCount D k (descendingPattern D) := by
      rw [Module.finrank_fintype_fun_eq_card, avoidPatternCount, Nat.card_eq_fintype_card]

/-- The exact finite binomial upper bound has the sharp asymptotic constant
in codimension one. Lower bounds will use the actual Haar purity. -/
theorem rankBudget_codimension_one_rank_upper (s k : ℕ) :
    (rankBudgetProjector (s+1) k s).rank ≤ patternPolynomial s k (s+1) := by
  have h := rankBudget_rank_le_descending_avoiders (s+1) k (by omega)
  simpa only [Nat.add_sub_cancel, avoidPatternCount_eq_patternPolynomial,
    descendingPattern, List.length_ofFn] using h

end
end ExtractionSchur
