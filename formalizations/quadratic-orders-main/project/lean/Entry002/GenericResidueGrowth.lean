import Entry002.GenericBatchSelection
import Entry002.GenericTimeKernels

/-!
# Actual nested residue families on one shared time law

The finite dependent recursion follows upstream-028/GaussianMoat/BatchCertificate.lean
lines 71–90 (OpenAI math, adc7f1241b42e322a6451854ab7e4b4c146bf78a,
Apache-2.0). Here the induction invariant also records the actual selected label
weight and cardinality. No Gaussian lattice or certificate theorem is imported.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Entry002
open OAI.GaussianMoat
open scoped BigOperators Classical
variable {L : Type*} [AddCommGroup L]

noncomputable def residueLabelWeight (F : Finset (ℕ × Bool)) : ℝ :=
  F.sum (fun i => Real.log i.1)

noncomputable def residueGrowthWeight (S : ℕ → Finset ℕ) (j : ℕ) : ℝ :=
  2 * ∑ k ∈ Finset.range j, (S k).sum (fun p => Real.log p)

def residueGrowthCard (bcap : ℕ → ℕ) (j : ℕ) : ℕ :=
  ∑ k ∈ Finset.range j, bcap k

noncomputable def residueWordCharge (data : SignedResidueData L) (Q : TimeLaw)
    (z : ℕ → L) (len : ℕ) (F G : Finset (ℕ × Bool)) : ℝ :=
  Q.info (fun a => residueFamilyHom data G (z a)) (incrementWord z len)
    (fun a => residueFamilyHom data F (z a)) / len

/-- Factor the common time law without changing it. This identifies a
backward batch's anchor law and future kernel with the literal full schedule. -/
theorem commonSchedule_split_timeLaw (P : TimeLaw) (z : ℕ → L)
    (pre post : List ℕ) (N : ℕ) :
    (P.advance (commonSchedule z pre 0)).advance (commonSchedule z post N) =
      P.advance (commonSchedule z (pre ++ post) N) := by
  rw [commonSchedule_append, TimeLaw.advance_then]

/-- Conditional increment-word information is unchanged by the exact schedule
factorization, including the two dependent residue-family observation types. -/
theorem residueWordCharge_split_schedule (data : SignedResidueData L)
    (P : TimeLaw) (z : ℕ → L) (pre post : List ℕ) (N len : ℕ)
    (F G : Finset (ℕ × Bool)) :
    residueWordCharge data
      ((P.advance (commonSchedule z pre 0)).advance (commonSchedule z post N))
      z len F G =
    residueWordCharge data (P.advance (commonSchedule z (pre ++ post) N))
      z len F G := by
  rw [commonSchedule_split_timeLaw]

/-- Local genuine extension input; all costs and the information charge are
computed from the supplied actual families and common law. -/
def ResidueGrowthStep (data : SignedResidueData L) (Q : TimeLaw)
    (z : ℕ → L) (len : ℕ → ℕ) (pool : Finset ℕ)
    (S : ℕ → Finset ℕ) (bcap : ℕ → ℕ) (r : ℕ → ℝ) (n : ℕ) : Prop :=
  ∀ j ≤ n, ∀ F : Finset (ℕ × Bool),
    F ⊆ pool ×ˢ (Finset.univ : Finset Bool) →
    residueLabelWeight F ≤ residueGrowthWeight S j →
    F.card ≤ residueGrowthCard bcap j →
    ∃ G : Finset (ℕ × Bool), F ⊆ G ∧
      G ⊆ pool ×ˢ (Finset.univ : Finset Bool) ∧
      (G \ F).card ≤ bcap j ∧
      residueLabelWeight G ≤ residueLabelWeight F +
        2 * (S j).sum (fun p => Real.log p) ∧
      r j ≤ residueWordCharge data Q z (len j) F G

@[simp] theorem residueGrowthWeight_zero (S : ℕ → Finset ℕ) :
    residueGrowthWeight S 0 = 0 := by simp [residueGrowthWeight]

@[simp] theorem residueGrowthWeight_succ (S : ℕ → Finset ℕ) (j : ℕ) :
    residueGrowthWeight S (j+1) = residueGrowthWeight S j +
      2 * (S j).sum (fun p => Real.log p) := by
  simp only [residueGrowthWeight, Finset.sum_range_succ]; ring

@[simp] theorem residueGrowthCard_zero (bcap : ℕ → ℕ) :
    residueGrowthCard bcap 0 = 0 := by simp [residueGrowthCard]

@[simp] theorem residueGrowthCard_succ (bcap : ℕ → ℕ) (j : ℕ) :
    residueGrowthCard bcap (j+1) = residueGrowthCard bcap j + bcap j := by
  simp [residueGrowthCard, Finset.sum_range_succ]

lemma residueGrowthWeight_mono_step (S : ℕ → Finset ℕ) (j : ℕ) :
    residueGrowthWeight S j ≤ residueGrowthWeight S (j+1) := by
  rw [residueGrowthWeight_succ]
  have hlog (p : ℕ) : 0 ≤ Real.log (p : ℝ) := by
    by_cases hp : p=0
    · simp [hp]
    · exact Real.log_nonneg (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hp))
  have hsum := Finset.sum_nonneg (fun p (_ : p ∈ S j) => hlog p)
  linarith

/-- An actual finite growth witness, including the initially empty family and
all costs. Every charge observes the same time law `Q`. -/
structure ResidueGrowthWitness (data : SignedResidueData L) (Q : TimeLaw)
    (z : ℕ → L) (len : ℕ → ℕ) (pool : Finset ℕ)
    (S : ℕ → Finset ℕ) (bcap : ℕ → ℕ) (r : ℕ → ℝ) (n : ℕ) where
  family : ℕ → Finset (ℕ × Bool)
  initial : family 0 = ∅
  in_pool : ∀ j, family j ⊆ pool ×ˢ (Finset.univ : Finset Bool)
  prime_mem : ∀ j i, i ∈ family j → i.1 ∈ data.primes
  nested : ∀ j, family j ⊆ family (j+1)
  weight_le : ∀ j, residueLabelWeight (family j) ≤ residueGrowthWeight S j
  card_le : ∀ j, (family j).card ≤ residueGrowthCard bcap j
  fresh_card_le : ∀ j ≤ n, (family (j+1) \ family j).card ≤ bcap j
  weight_increment_le : ∀ j ≤ n, residueLabelWeight (family (j+1)) ≤
    residueLabelWeight (family j) + 2 * (S j).sum (fun p => Real.log p)
  charge_le : ∀ j ≤ n, r j ≤ residueWordCharge data Q z (len j)
    (family j) (family (j+1))

/-- Genuine finite induction. Its only information input is a per-step rate
for the actual old and new residue observations of the actual increment word.
The rate must hold uniformly for every family satisfying the accumulated costs. -/
theorem actual_residue_growth (data : SignedResidueData L) (Q : TimeLaw)
    (z : ℕ → L) (len : ℕ → ℕ) (pool : Finset ℕ)
    (hpool : ∀ p ∈ pool, p ∈ data.primes)
    (S : ℕ → Finset ℕ) (bcap : ℕ → ℕ) (r : ℕ → ℝ) (n : ℕ)
    (hstep : ∀ j ≤ n, ∀ F : Finset (ℕ × Bool),
      F ⊆ pool ×ˢ (Finset.univ : Finset Bool) →
      residueLabelWeight F ≤ residueGrowthWeight S j →
      F.card ≤ residueGrowthCard bcap j →
      ∃ G : Finset (ℕ × Bool), F ⊆ G ∧
        G ⊆ pool ×ˢ (Finset.univ : Finset Bool) ∧
        (G \ F).card ≤ bcap j ∧
        residueLabelWeight G ≤ residueLabelWeight F +
          2 * (S j).sum (fun p => Real.log p) ∧
        r j ≤ residueWordCharge data Q z (len j) F G) :
    Nonempty (ResidueGrowthWitness data Q z len pool S bcap r n) := by
  let Valid (j : ℕ) (F : Finset (ℕ × Bool)) : Prop :=
    F ⊆ pool ×ˢ (Finset.univ : Finset Bool) ∧
    residueLabelWeight F ≤ residueGrowthWeight S j ∧
    F.card ≤ residueGrowthCard bcap j
  let R (j : ℕ) (F G : Finset (ℕ × Bool)) : Prop :=
    (G \ F).card ≤ bcap j ∧
    residueLabelWeight G ≤ residueLabelWeight F +
      2 * (S j).sum (fun p => Real.log p) ∧
    r j ≤ residueWordCharge data Q z (len j) F G
  have step (j : ℕ) (F : {F : Finset (ℕ × Bool) // Valid j F}) :
      ∃ G : {G : Finset (ℕ × Bool) // Valid (j+1) G},
        F.val ⊆ G.val ∧ (j ≤ n → R j F.val G.val) := by
    by_cases hj : j ≤ n
    · obtain ⟨G,hFG,hG,hcard,hweight,hcharge⟩ :=
        hstep j hj F.val F.property.1 F.property.2.1 F.property.2.2
      have hGcard : G.card ≤ residueGrowthCard bcap (j+1) := by
        have heq := Finset.card_sdiff_of_subset hFG
        have hmono := Finset.card_le_card hFG
        have hFcard := F.property.2.2
        rw [residueGrowthCard_succ]
        omega
      have hGweight : residueLabelWeight G ≤ residueGrowthWeight S (j+1) := by
        rw [residueGrowthWeight_succ]
        have hFweight := F.property.2.1
        linarith
      exact ⟨⟨G,hG,hGweight,hGcard⟩,hFG,fun _ => ⟨hcard,hweight,hcharge⟩⟩
    · refine ⟨⟨F.val,F.property.1,?_,?_⟩,Finset.Subset.refl _,fun h => (hj h).elim⟩
      · exact F.property.2.1.trans (residueGrowthWeight_mono_step S j)
      · exact F.property.2.2.trans (by rw [residueGrowthCard_succ]; omega)
  let f (j : ℕ) (F : {F : Finset (ℕ × Bool) // Valid j F}) := (step j F).choose
  let F : (j : ℕ) → {F : Finset (ℕ × Bool) // Valid j F} :=
    @Nat.rec (fun j => {F : Finset (ℕ × Bool) // Valid j F})
      ⟨∅,Finset.empty_subset _,by simp [residueLabelWeight],by simp⟩ f
  refine ⟨{ family := fun j => (F j).val
            initial := rfl
            in_pool := fun j => (F j).property.1
            prime_mem := ?_
            nested := fun j => (step j (F j)).choose_spec.1
            weight_le := fun j => (F j).property.2.1
            card_le := fun j => (F j).property.2.2
            fresh_card_le := fun j hj => ((step j (F j)).choose_spec.2 hj).1
            weight_increment_le := fun j hj => ((step j (F j)).choose_spec.2 hj).2.1
            charge_le := fun j hj => ((step j (F j)).choose_spec.2 hj).2.2 }⟩
  intro j i hi
  exact hpool i.1 (Finset.mem_product.mp ((F j).property.1 hi)).1

end Entry002
