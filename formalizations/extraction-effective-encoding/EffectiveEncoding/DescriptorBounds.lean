import EffectiveEncoding.NumericalTerminal

open scoped BigOperators
open CircuitCompletion CircuitRecursion SymmetricSupport Matrix
namespace EffectiveEncoding

/-- Bounds on the literal integer fields and half-angle depth of a descriptor. -/
def AngleCode.Fits (M H : ℕ) (a : AngleCode) : Prop :=
  (match a.atom with | .pi => True | .merge A B j => A+B≤M ∧ j≤M) ∧ a.halvings≤H

def SingleCode.Fits (M H : ℕ) : SingleCode → Prop
  | .hadamard | .yBasis => True
  | .phase a b => a.Fits M H ∧ b.Fits M H
  | .inverse u => u.Fits M H

def SingleCode.inverseDepth : SingleCode → ℕ
  | .inverse u => u.inverseDepth+1
  | _ => 0

def GateCode.Fits {n : ℕ} (M H D : ℕ) : GateCode n → Prop
  | .single _ u => u.Fits M H ∧ u.inverseDepth≤D
  | .cnot _ _ _ => True

def WordFits {n : ℕ} (M H D : ℕ) (w : WordCode n) : Prop :=
  ∀ g∈w,g.Fits M H D

theorem AngleCode.Fits.mono {M H M' H' : ℕ} {a : AngleCode}
    (h : a.Fits M H) (hM : M≤M') (hH : H≤H') : a.Fits M' H' := by
  rcases h with ⟨h,hhalf⟩
  refine ⟨?_,hhalf.trans hH⟩
  cases he : a.atom with
  | pi => trivial
  | merge A B j =>
    rw [he] at h
    exact ⟨h.1.trans hM,h.2.trans hM⟩

theorem AngleCode.Fits.neg {M H : ℕ} {a : AngleCode} (h : a.Fits M H) :
    a.neg.Fits M H := h

theorem AngleCode.Fits.half {M H : ℕ} {a : AngleCode} (h : a.Fits M H) (n : ℕ) :
    (a.half n).Fits M (H+n) := ⟨h.1,Nat.add_le_add_right h.2 n⟩

theorem SingleCode.Fits.mono {M H M' H' : ℕ} {u : SingleCode}
    (h : u.Fits M H) (hM : M≤M') (hH : H≤H') : u.Fits M' H' := by
  induction u with
  | hadamard => trivial
  | yBasis => trivial
  | phase a b => exact ⟨h.1.mono hM hH,h.2.mono hM hH⟩
  | inverse u ih => exact ih h

theorem GateCode.Fits.mono {n M H D M' H' D' : ℕ} {g : GateCode n}
    (h : g.Fits M H D) (hM : M≤M') (hH : H≤H') (hD : D≤D') : g.Fits M' H' D' := by
  cases g with
  | single i u => exact ⟨h.1.mono hM hH,h.2.trans hD⟩
  | cnot c t h => trivial

theorem WordFits.mono {n M H D M' H' D' : ℕ} {w : WordCode n}
    (h : WordFits M H D w) (hM : M≤M') (hH : H≤H') (hD : D≤D') :
    WordFits M' H' D' w := fun g hg => (h g hg).mono hM hH hD

@[simp] theorem wordFits_nil (n M H D : ℕ) : WordFits M H D ([] : WordCode n) := by
  intro g hg;cases hg

@[simp] theorem wordFits_append {n M H D : ℕ} (w v : WordCode n) :
    WordFits M H D (w++v) ↔ WordFits M H D w ∧ WordFits M H D v := by
  simp only [WordFits,List.mem_append,or_imp,forall_and]

theorem WordFits.reverse {n M H D : ℕ} {w : WordCode n} (h : WordFits M H D w) :
    WordFits M H (D+1) (reverseCode w) := by
  intro g hg
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
  have h' := h a (List.mem_reverse.mp ha)
  cases a with
  | single i u => exact ⟨h'.1,Nat.add_le_add_right h'.2 1⟩
  | cnot c t hc => trivial

theorem cnotCode_fits {n : ℕ} (t : Fin n) (cs : List (Control t)) (M H D : ℕ) :
    WordFits M H D (cnotCode t cs) := by
  intro g hg
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hg
  trivial

theorem parityCode_fits {n M H : ℕ} (t : Fin n) (cs : List (Control t))
    (a b : AngleCode) (ha : a.Fits M H) (hb : b.Fits M H) :
    WordFits M H 0 (parityCode t cs a b) := by
  unfold parityCode
  rw [wordFits_append,wordFits_append]
  refine ⟨⟨cnotCode_fits t cs M H 0,?_⟩,?_⟩
  · intro g hg
    simp only [List.mem_singleton] at hg
    subst g
    exact ⟨⟨ha,hb⟩,le_refl 0⟩
  · intro g hg
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hg
    have hc' := (cnotCode_fits t cs M H 0) c (List.mem_reverse.mp hc)
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hc)
    trivial

theorem pauliCode_fits {n M H : ℕ} (hn : 0<n) (S : Finset (Fin n))
    (a : AngleCode) (ha : a.Fits M H) : WordFits M H 0 (pauliCode hn S a) := by
  by_cases hS : S.Nonempty
  · rw [pauliCode,dif_pos hS]
    exact parityCode_fits _ _ a a.neg ha ha.neg
  · rw [pauliCode,dif_neg hS]
    intro g hg
    simp only [List.mem_singleton] at hg
    subst g
    exact ⟨⟨ha,ha⟩,le_refl 0⟩

theorem signedCode_fits {M H : ℕ} (a : AngleCode) (b : Bool) (ha : a.Fits M H) :
    (signedCode a b).Fits M H := by
  cases b
  · exact ha
  · exact ha.neg

theorem selectedCode_fits {n M H : ℕ} (hn : 0<n) (x : Bits n) (a : AngleCode)
    (ha : a.Fits M H) : WordFits M (H+n) 0 (selectedCode hn x a) := by
  intro g hg
  obtain ⟨S,hS,hg⟩ := List.mem_flatMap.mp hg
  exact pauliCode_fits hn S _ (signedCode_fits _ _ (ha.half n)) g hg

theorem piCode_fits (M : ℕ) : piCode.Fits M 0 := ⟨trivial,le_refl 0⟩

theorem hadamardCode_fits {n : ℕ} (t : Fin n) (M H D : ℕ) :
    WordFits M H D [.single t .hadamard] := by
  intro g hg
  simp only [List.mem_singleton] at hg
  subst g
  exact ⟨trivial,Nat.zero_le _⟩

theorem adjacentSwapCode_fits {n : ℕ} (hn : 0<n) (t : Fin n) (x : Bits n) (M : ℕ) :
    WordFits M n 0 (adjacentSwapCode hn t x) := by
  unfold adjacentSwapCode
  rw [wordFits_append,wordFits_append]
  exact ⟨⟨hadamardCode_fits _ _ _ _,by simpa using selectedCode_fits hn _ piCode (piCode_fits M)⟩,
    hadamardCode_fits _ _ _ _⟩

theorem adjacentRotationCode_fits {n M H : ℕ} (hn : 0<n) (t : Fin n) (x : Bits n)
    (a : AngleCode) (ha : a.Fits M H) :
    WordFits M (H+n) 1 (adjacentRotationCode hn t x a) := by
  unfold adjacentRotationCode
  simp only [wordFits_append]
  refine ⟨⟨⟨?_,(selectedCode_fits hn _ a ha).mono le_rfl le_rfl (by decide)⟩,
    (selectedCode_fits hn _ a.neg ha.neg).mono le_rfl le_rfl (by decide)⟩,?_⟩
  all_goals intro g hg; simp only [List.mem_singleton] at hg; subst g; constructor <;> trivial

theorem orientedRotationCode_fits {n M H : ℕ} (hn : 0<n) (t : Fin n) (x : Bits n)
    (a : AngleCode) (ha : a.Fits M H) :
    WordFits M (H+n) 1 (orientedRotationCode hn t x a) :=
  adjacentRotationCode_fits hn t x _ (signedCode_fits a _ ha)

theorem moveCode_fits {n : ℕ} (hn : 0<n) (x : Bits n) (cs : List (Fin n))
    (y : Bits n) (M : ℕ) : WordFits M n 0 (moveCode hn x cs y) := by
  induction cs generalizing y with
  | nil => exact wordFits_nil _ _ _ _
  | cons j js ih =>
    by_cases h : y j=x j
    · simpa only [moveCode,if_pos h] using ih y
    · rw [moveCode,if_neg h,wordFits_append]
      exact ⟨adjacentSwapCode_fits hn j y M,ih _⟩

theorem swapCode_fits {n : ℕ} (hn : 0<n) (x y : Bits n) (M : ℕ) :
    WordFits M n 1 (swapCode hn x y) := by
  by_cases h : x=y
  · simp [swapCode,h]
  · rw [swapCode,dif_neg h,wordFits_append,wordFits_append]
    exact ⟨⟨(moveCode_fits hn x _ y M).mono le_rfl le_rfl (by decide),
      (adjacentSwapCode_fits hn _ x M).mono le_rfl le_rfl (by decide)⟩,
      (moveCode_fits hn x _ y M).reverse⟩

theorem rotationCode_fits {n M H : ℕ} (hn : 0<n) (x y : Bits n) (h : x≠y)
    (a : AngleCode) (ha : a.Fits M H) : WordFits M (H+n) 1 (rotationCode hn x y h a) := by
  unfold rotationCode
  rw [wordFits_append,wordFits_append]
  exact ⟨⟨(moveCode_fits hn x _ y M).mono le_rfl (by omega) (by decide),
    orientedRotationCode_fits hn _ x a ha⟩,
    ((moveCode_fits hn x _ y M).reverse).mono le_rfl (by omega) le_rfl⟩

def RawCode.Fits {n : ℕ} (M : ℕ) : RawCode n → Prop
  | .swap _ _ => True
  | .merge _ _ _ A B j => A+B≤M ∧ j≤M

theorem RawCode.compile_fits {n M : ℕ} (hn : 0<n) (g : RawCode n) (h : g.Fits M) :
    WordFits M n 1 (g.compile hn) := by
  cases g with
  | swap x y => exact swapCode_fits hn x y M
  | merge x y he A B j =>
    have ha : (mergeCode A B j).Fits M 0 := ⟨h,le_refl 0⟩
    simpa only [Nat.zero_add,RawCode.compile] using rotationCode_fits hn x y he _ ha

theorem compileRaw_fits {n M : ℕ} (hn : 0<n) (xs : List (RawCode n))
    (h : ∀ g∈xs,g.Fits M) : WordFits M n 1 (compileRaw hn xs) := by
  intro g hg
  obtain ⟨a,ha,hg⟩ := List.mem_flatMap.mp hg
  exact a.compile_fits hn (h a ha) g hg

theorem alignmentCode_fits {ι : Type*} {n : ℕ} (hn : 0<n) (e f : ι ↪ Bits n)
    (xs : List ι) (p : Equiv.Perm (Bits n)) (M : ℕ) :
    WordFits M n 1 (alignmentCode hn e f xs p) := by
  induction xs generalizing p with
  | nil => exact wordFits_nil _ _ _ _
  | cons i xs ih =>
    rw [alignmentCode,wordFits_append]
    exact ⟨swapCode_fits hn _ _ M,ih _⟩

theorem countProgram_fits {n : ℕ} (p : Bits n) (c : Bits n → ℕ)
    (qs : List {q : Bits n // q≠p}) (A j B M : ℕ)
    (hc : ∀ q∈qs,c q.1≤B) (ha : A+qs.length*B≤M) (hj : j≤M) :
    ∀ g∈countProgram p c qs A j,g.Fits M := by
  induction qs generalizing A with
  | nil => intro g hg;cases hg
  | cons q qs ih =>
    have hq := hc q (by simp)
    have ha' : A+c q.1+qs.length*B≤M := by simp only [List.length_cons] at ha;nlinarith
    intro g hg
    simp only [countProgram,List.mem_cons] at hg
    rcases hg with rfl|hg
    · exact ⟨by omega,hj⟩
    · exact ih (A+c q.1) (fun r hr => hc r (by simp [hr])) ha' g hg

theorem branchCode_fits {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q)
    (ν : Sym (Fin 4) (k+1)) : WordFits (4*(k+1)) (2+q) 1 (branchCode enc ν) := by
  unfold branchCode integerIndexedCode
  apply compileRaw_fits
  apply countProgram_fits _ _ _ _ _ (k+1) (4*(k+1))
  · intro r hr
    obtain ⟨i,hi,he⟩ := List.mem_map.mp hr
    subst r
    rw [indexedCount_image]
    exact (Multiset.count_le_card i.1.1 ν.val).trans_eq ν.property
  · have hp : ν.val.count (occupiedPivot ν).1≤k+1 := (Multiset.count_le_card _ ν.val).trans_eq ν.property
    have hl : (explicitOthers (branchEmbedding enc ν) (occupiedPivot ν)).length≤3 := by
      rw [explicitOthers_length]
      have h := Fintype.card_le_of_injective
        (fun i : {i : Fin 4 // i∈ν} => i.1) Subtype.val_injective
      simp only [Fintype.card_fin] at h
      omega
    nlinarith
  · omega

theorem occupationStepCode_fits {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q)
    (next : Sym (Fin 4) (k+1) ↪ Bits (2+q)) :
    WordFits (4*(k+1)) (2+q) 1 (occupationStepCode enc next) := by
  rw [occupationStepCode,wordFits_append]
  refine ⟨?_,alignmentCode_fits _ _ _ _ _ _⟩
  intro g hg
  obtain ⟨ν,hν,hg⟩ := List.mem_flatMap.mp hg
  exact branchCode_fits enc ν g hg

def halvingBudget (k : ℕ) : ℕ := 6*Nat.clog 2 (k+3)+2

theorem halvingBudget_mono {j k : ℕ} (h : j≤k) : halvingBudget j≤halvingBudget k := by
  have hc := Nat.clog_mono_right 2 (show j+3≤k+3 by omega)
  unfold halvingBudget
  omega

theorem stageCode_fits (k : ℕ) : WordFits (4*(k+1)) (halvingBudget k) 1 (stageCode k) := by
  intro g hg
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
  have hf := occupationStepCode_fits (compactEncoding k) (nextEncoding k) a ha
  have hW : 2+codeWires k≤halvingBudget k := by
    have hw := activeWires_log_bound k
    unfold activeWires at hw
    unfold codeWires halvingBudget
    omega
  cases a with
  | single i u => exact ⟨hf.1.mono le_rfl hW,hf.2⟩
  | cnot c t h => trivial

theorem WordFits.shift {n M H D : ℕ} {w : WordCode n} (h : WordFits M H D w) (s : ℕ) :
    WordFits M H D (shiftCode s w) := by
  intro g hg
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
  have hf := h a ha
  cases a <;> exact hf

theorem WordFits.prefix {n q M H D : ℕ} {w : WordCode q} (h : WordFits M H D w) (hqn : q≤n) :
    WordFits M H D (prefixCode hqn w) := by
  intro g hg
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
  have hf := h a ha
  cases a <;> exact hf

theorem WordFits.cast {n q M H D : ℕ} {w : WordCode q} (h : WordFits M H D w) (hqn : q=n) :
    WordFits M H D (castCode hqn w) := by subst n;exact h

theorem compressionCode_fits (k : ℕ) : WordFits (4*k) (halvingBudget k) 1 (compressionCode k) := by
  induction k with
  | zero => exact wordFits_nil _ _ _ _
  | succ k ih =>
    rw [compressionCode,wordFits_append]
    exact ⟨(ih.shift 2).mono (by omega) (halvingBudget_mono (by omega)) le_rfl,
      (stageCode_fits k).mono le_rfl (halvingBudget_mono (by omega)) le_rfl⟩

theorem bellPairsCode_fits (h M H D : ℕ) : WordFits M H D (bellPairsCode h) := by
  induction h with
  | zero => exact wordFits_nil _ _ _ _
  | succ h ih =>
    rw [bellPairsCode,wordFits_append]
    refine ⟨?_,ih.shift 2⟩
    apply WordFits.prefix
    intro g hg
    simp only [bellPreparationCode,List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with rfl|rfl
    · exact ⟨trivial,Nat.zero_le _⟩
    · trivial

/-- Every actual generated descriptor has polynomially bounded literal
masses, logarithmic half-angle depth, and at most one inverse wrapper. -/
theorem extractionCode_fits (k : ℕ) : WordFits (4*k) (halvingBudget k) 1 (extractionCode k) := by
  rw [extractionCode,wordFits_append]
  exact ⟨compressionCode_fits k,((bellPairsCode_fits _ _ _ _).shift _).cast _⟩

/-- A concrete binary-field description weight, including constructor and
sign tags. This is independent of Lean's internal object allocation. -/
def binaryWidth (n : ℕ) : ℕ := Nat.clog 2 (n+1)

def AngleCode.descriptionWeight (a : AngleCode) : ℕ :=
  (match a.atom with
    | .pi => 1
    | .merge A B j => binaryWidth A+binaryWidth B+binaryWidth j+1)+
      binaryWidth a.halvings+2

def angleWeightBudget (M H : ℕ) : ℕ := 3*binaryWidth M+binaryWidth H+3

theorem binaryWidth_mono {a b : ℕ} (h : a≤b) : binaryWidth a≤binaryWidth b :=
  Nat.clog_mono_right 2 (Nat.add_le_add_right h 1)

theorem AngleCode.descriptionWeight_bound {M H : ℕ} (a : AngleCode) (h : a.Fits M H) :
    a.descriptionWeight≤angleWeightBudget M H := by
  have hh := binaryWidth_mono h.2
  have hm := h.1
  cases he : a.atom with
  | pi => simp only [descriptionWeight,he,angleWeightBudget];omega
  | merge A B j =>
    rw [he] at hm
    have hA := binaryWidth_mono (show A≤M by omega)
    have hB := binaryWidth_mono (show B≤M by omega)
    have hj := binaryWidth_mono hm.2
    simp only [descriptionWeight,he,angleWeightBudget]
    omega

def SingleCode.descriptionWeight : SingleCode → ℕ
  | .hadamard | .yBasis => 1
  | .phase a b => a.descriptionWeight+b.descriptionWeight+1
  | .inverse u => u.descriptionWeight+1

theorem SingleCode.descriptionWeight_bound {M H : ℕ} (u : SingleCode) (h : u.Fits M H) :
    u.descriptionWeight≤2*angleWeightBudget M H+1+u.inverseDepth := by
  induction u with
  | hadamard => simp [descriptionWeight,inverseDepth]
  | yBasis => simp [descriptionWeight,inverseDepth]
  | phase a b =>
    have ha := a.descriptionWeight_bound h.1
    have hb := b.descriptionWeight_bound h.2
    simp only [descriptionWeight,inverseDepth]
    omega
  | inverse u ih =>
    have hu := ih h
    simp only [descriptionWeight,inverseDepth]
    omega

def GateCode.descriptionWeight {n : ℕ} : GateCode n → ℕ
  | .single i u => binaryWidth i.val+u.descriptionWeight+1
  | .cnot c t _ => binaryWidth c.val+binaryWidth t.val+1

def codeDescriptionWeight {n : ℕ} (w : WordCode n) : ℕ := (w.map GateCode.descriptionWeight).sum

theorem GateCode.descriptionWeight_bound {n M H D : ℕ} (g : GateCode n) (h : g.Fits M H D) :
    g.descriptionWeight≤2*binaryWidth n+2*angleWeightBudget M H+D+2 := by
  cases g with
  | single i u =>
    have hi := binaryWidth_mono i.isLt.le
    have hu := u.descriptionWeight_bound h.1
    have hd := h.2
    simp only [descriptionWeight]
    omega
  | cnot c t hc =>
    have hc := binaryWidth_mono c.isLt.le
    have ht := binaryWidth_mono t.isLt.le
    simp only [descriptionWeight]
    omega

theorem codeDescriptionWeight_bound {n M H D : ℕ} (w : WordCode n) (h : WordFits M H D w) :
    codeDescriptionWeight w≤w.length*(2*binaryWidth n+2*angleWeightBudget M H+D+2) := by
  unfold codeDescriptionWeight
  calc
    _ ≤ (w.map (fun _ => 2*binaryWidth n+2*angleWeightBudget M H+D+2)).sum := by
      apply List.sum_le_sum
      intro g hg
      exact g.descriptionWeight_bound (h g hg)
    _ = _ := by simp

theorem extractionCode_descriptionWeight (k : ℕ) :
    codeDescriptionWeight (extractionCode k)≤(extractionCode k).length*
      (2*binaryWidth (originalWireCount k)+2*angleWeightBudget (4*k) (halvingBudget k)+3) :=
  codeDescriptionWeight_bound _ (extractionCode_fits k)

end EffectiveEncoding
