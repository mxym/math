import CircuitRecursion.Encoding
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.Nat.Bitwise

open scoped BigOperators
open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

abbrev Triple := ℕ × ℕ × ℕ

def total (t : Triple) : ℕ := t.1+t.2.1+t.2.2

/-- A bounded triple loop, in lexicographic list order. -/
def triples (k : ℕ) : List Triple :=
  ((List.range (k+1)) ×ˢ
    ((List.range (k+1)) ×ˢ (List.range (k+1)))).filter
      (fun t => decide (total t≤k))

theorem mem_triples {k : ℕ} {t : Triple} :
    t∈triples k ↔ total t≤k := by
  rcases t with ⟨a,b,c⟩
  simp only [triples,List.mem_filter,decide_eq_true_eq]
  change ((a,b,c)∈(List.range (k+1)) ×ˢ
    ((List.range (k+1)) ×ˢ (List.range (k+1))) ∧ total (a,b,c)≤k) ↔ _
  simp only [List.mem_product,List.mem_range,total]
  omega

theorem triples_nodup (k : ℕ) : (triples k).Nodup := by
  exact ((List.nodup_range (n:=k+1)).product
    ((List.nodup_range (n:=k+1)).product (List.nodup_range (n:=k+1)))).filter _

def fromTriple (k : ℕ) (t : Triple) (h : total t≤k) : Sym (Fin 4) k :=
  ⟨Multiset.replicate t.1 0+Multiset.replicate t.2.1 1+
    Multiset.replicate t.2.2 2+Multiset.replicate (k-total t) 3,by
      simp only [Multiset.card_add,Multiset.card_replicate]
      unfold total at *
      omega⟩

@[simp] theorem fromTriple_count_zero (k : ℕ) (t : Triple) (h : total t≤k) :
    ((fromTriple k t h : Sym (Fin 4) k) : Multiset (Fin 4)).count 0=t.1 := by
  simp [fromTriple,Multiset.count_replicate]

@[simp] theorem fromTriple_count_one (k : ℕ) (t : Triple) (h : total t≤k) :
    ((fromTriple k t h : Sym (Fin 4) k) : Multiset (Fin 4)).count 1=t.2.1 := by
  simp [fromTriple,Multiset.count_replicate]

@[simp] theorem fromTriple_count_two (k : ℕ) (t : Triple) (h : total t≤k) :
    ((fromTriple k t h : Sym (Fin 4) k) : Multiset (Fin 4)).count 2=t.2.2 := by
  simp [fromTriple,Multiset.count_replicate]

@[simp] theorem fromTriple_count_three (k : ℕ) (t : Triple) (h : total t≤k) :
    ((fromTriple k t h : Sym (Fin 4) k) : Multiset (Fin 4)).count 3=k-total t := by
  simp [fromTriple,Multiset.count_replicate]

def toTriple {k : ℕ} (ν : Sym (Fin 4) k) : Triple :=
  (ν.val.count 0,ν.val.count 1,ν.val.count 2)

theorem count_total {k : ℕ} (ν : Sym (Fin 4) k) :
    ν.val.count 0+ν.val.count 1+ν.val.count 2+ν.val.count 3=k := by
  have h : (∑ i : Fin 4,ν.val.count i)=k := by
    simpa only [ν.property] using
      (Multiset.sum_count_eq_card (m:=ν.val)
        (s:=Finset.univ) (by simp))
  simpa only [Fin.sum_univ_four] using h

theorem toTriple_le {k : ℕ} (ν : Sym (Fin 4) k) : total (toTriple ν)≤k := by
  have h := count_total ν
  simp only [toTriple,total]
  omega

@[simp] theorem toTriple_fromTriple (k : ℕ) (t : Triple) (h : total t≤k) :
    toTriple (fromTriple k t h)=t := by
  simp [toTriple]

@[simp] theorem fromTriple_toTriple {k : ℕ} (ν : Sym (Fin 4) k) :
    fromTriple k (toTriple ν) (toTriple_le ν)=ν := by
  apply Subtype.ext
  apply Multiset.ext.mpr
  intro i
  have h := count_total ν
  fin_cases i <;> norm_num [fromTriple,Multiset.count_replicate,toTriple,total] at * <;> omega

def occupations (k : ℕ) : List (Sym (Fin 4) k) :=
  (triples k).attach.map fun t => fromTriple k t.1 (mem_triples.mp t.2)

theorem occupations_nodup (k : ℕ) : (occupations k).Nodup := by
  apply List.Nodup.map _ (List.nodup_attach.mpr (triples_nodup k))
  intro t u h
  apply Subtype.ext
  simpa only [toTriple_fromTriple] using congrArg toTriple h

theorem mem_occupations {k : ℕ} (ν : Sym (Fin 4) k) : ν∈occupations k := by
  apply List.mem_map.mpr
  refine ⟨⟨toTriple ν,mem_triples.mpr (toTriple_le ν)⟩,by simp,?_⟩
  exact fromTriple_toTriple ν

theorem occupations_length (k : ℕ) : (occupations k).length=occupationRank k := by
  have hu : (occupations k).toFinset=Finset.univ := by
    ext ν
    simp [mem_occupations]
  have hc := congrArg Finset.card hu
  rw [List.toFinset_card_of_nodup (occupations_nodup k),Finset.card_univ,
    occupationRank_card] at hc
  exact hc

/-- The index is obtained by a finite equality scan of the explicit loop. -/
def rank {k : ℕ} (ν : Sym (Fin 4) k) : Fin (occupationRank k) :=
  ⟨(occupations k).idxOf ν,by
    rw [← occupations_length k]
    exact List.idxOf_lt_length_iff.mpr (mem_occupations ν)⟩

def unrank (k : ℕ) (i : Fin (occupationRank k)) : Sym (Fin 4) k :=
  (occupations k)[i.val]'(by rw [occupations_length];exact i.isLt)

@[simp] theorem unrank_rank {k : ℕ} (ν : Sym (Fin 4) k) : unrank k (rank ν)=ν := by
  exact List.getElem_idxOf (by
    exact List.idxOf_lt_length_iff.mpr (mem_occupations ν))

@[simp] theorem rank_unrank (k : ℕ) (i : Fin (occupationRank k)) :
    rank (unrank k i)=i := by
  apply Fin.ext
  exact (occupations_nodup k).idxOf_getElem _ _

def rankEquiv (k : ℕ) : Sym (Fin 4) k ≃ Fin (occupationRank k) where
  toFun := rank
  invFun := unrank k
  left_inv := unrank_rank
  right_inv := rank_unrank k

def boundedBits (q : ℕ) (i : Fin (2^q)) : Bits q :=
  fun j => i.val.testBit j.val

theorem boundedBits_injective (q : ℕ) : Function.Injective (boundedBits q) := by
  intro x y h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<q
  · exact congrFun h ⟨j,hj⟩
  · have hq : q≤j := by omega
    rw [Nat.testBit_eq_false_of_lt
        (x.isLt.trans_le (Nat.pow_le_pow_right (by decide) hq)),
      Nat.testBit_eq_false_of_lt
        (y.isLt.trans_le (Nat.pow_le_pow_right (by decide) hq))]

theorem rank_fits (k : ℕ) : occupationRank k≤2^codeWires k := by
  have h := Nat.le_pow_clog (by decide : 1<4) (occupationRank k)
  simpa only [codeWires,encodingPairs,Nat.pow_mul] using h

/-- A fully computable replacement for the choice-based finite embedding.
It occupies exactly the existing pair-aligned code width. -/
def compactEncoding (k : ℕ) : Sym (Fin 4) k ↪ Bits (codeWires k) where
  toFun ν := boundedBits (codeWires k)
    ⟨(rank ν).val,(rank ν).isLt.trans_le (rank_fits k)⟩
  inj' := by
    intro ν μ h
    have he := boundedBits_injective (codeWires k) h
    apply (rankEquiv k).injective
    apply Fin.ext
    change (rank ν).val=(rank μ).val
    exact congrArg (fun i : Fin (2^codeWires k) => i.val) he

def originalEncoding (k : ℕ) : Sym (Fin 4) k ↪ Bits (originalWireCount k) :=
  extendEmbedding (codeWires_available k) (compactEncoding k)

def nextEncoding (k : ℕ) : Sym (Fin 4) (k+1) ↪ Bits (2+codeWires k) :=
  extendEmbedding (codeWires_step k) (compactEncoding (k+1))


def decode (k : ℕ) (b : Bits (codeWires k)) : Option (Sym (Fin 4) k) :=
  (occupations k).find? (fun ν => decide (compactEncoding k ν=b))

theorem find_unique {α : Type*} (p : α → Bool) (xs : List α) (x : α)
    (hx : x∈xs) (hpx : p x=true) (hu : ∀ y,p y=true → y=x) :
    xs.find? p=some x := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    by_cases hy : p y=true
    · rw [List.find?_cons_of_pos hy,hu y hy]
    · rw [List.find?_cons_of_neg hy]
      apply ih
      rcases List.mem_cons.mp hx with h|h
      · subst y
        exact False.elim (hy hpx)
      · exact h

@[simp] theorem decode_encode {k : ℕ} (ν : Sym (Fin 4) k) :
    decode k (compactEncoding k ν)=some ν := by
  apply find_unique _ _ ν (mem_occupations ν) (by simp)
  intro μ hμ
  apply (compactEncoding k).injective
  exact of_decide_eq_true hμ

theorem decode_some_iff {k : ℕ} (b : Bits (codeWires k)) (ν : Sym (Fin 4) k) :
    decode k b=some ν ↔ compactEncoding k ν=b := by
  constructor
  · intro h
    have he : decide (compactEncoding k ν=b)=true :=
      List.find?_some (p:=fun μ => decide (compactEncoding k μ=b)) h
    exact of_decide_eq_true he
  · intro h
    rw [← h,decode_encode]

theorem enumeration_candidate_bound (k : ℕ) :
    (occupations k).length≤(k+1)^3 := by
  simp only [occupations,List.length_map,List.length_attach]
  exact (List.length_filter_le _ _).trans_eq (by
    change ((List.range (k+1)) ×ˢ
      ((List.range (k+1)) ×ˢ (List.range (k+1)))).length=(k+1)^3
    simp [List.length_product,pow_succ,Nat.mul_assoc])

theorem compactEncoding_testBit {k : ℕ} (ν : Sym (Fin 4) k)
    (j : Fin (codeWires k)) :
    compactEncoding k ν j=(rank ν).val.testBit j.val := rfl

theorem originalEncoding_high_zero {k : ℕ} (ν : Sym (Fin 4) k)
    (j : Fin (originalWireCount k)) (hj : codeWires k≤j.val) :
    originalEncoding k ν j=false := by
  simp [originalEncoding,extendEmbedding,extendBits,Nat.not_lt.mpr hj]

end EffectiveEncoding

