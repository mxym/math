import EffectiveEncoding.Enumeration
import CircuitRecursion.HalfAngleEvaluation
import Mathlib.Data.Finset.Sort

open scoped BigOperators
open CircuitCompletion CircuitRecursion Matrix
namespace EffectiveEncoding

/-- The only nonrational angle atoms used by the elementary compiler. -/
inductive AngleAtom where
  | pi
  | merge (A B denominator : ℕ)
  deriving DecidableEq, Repr

/-- A finite description of a signed iterated half-angle. -/
structure AngleCode where
  atom : AngleAtom
  negative : Bool := false
  halvings : ℕ := 0
  deriving DecidableEq, Repr

noncomputable def AngleAtom.value : AngleAtom → ℝ
  | .pi => Real.pi
  | .merge A B j => mergeAngle ((A:ℝ)/j) ((B:ℝ)/j)

noncomputable def AngleCode.value (a : AngleCode) : ℝ :=
  (if a.negative then -a.atom.value else a.atom.value)/(2:ℝ)^a.halvings

def AngleCode.neg (a : AngleCode) : AngleCode := { a with negative := !a.negative }
def AngleCode.half (a : AngleCode) (n : ℕ) : AngleCode :=
  {a with halvings := a.halvings+n}

@[simp] theorem AngleCode.neg_value (a : AngleCode) : a.neg.value=-a.value := by
  cases h : a.negative <;> simp [AngleCode.neg,AngleCode.value,h] <;> ring

@[simp] theorem AngleCode.half_value (a : AngleCode) (n : ℕ) :
    (a.half n).value=a.value/(2:ℝ)^n := by
  simp only [AngleCode.half,AngleCode.value,pow_add,div_mul_eq_div_div]
  rfl

def piCode : AngleCode := ⟨.pi,false,0⟩

@[simp] theorem piCode_value : piCode.value=Real.pi := by
  simp [piCode,AngleCode.value,AngleAtom.value]

inductive SingleCode where
  | hadamard
  | yBasis
  | phase (zero one : AngleCode)
  | inverse (u : SingleCode)
  deriving DecidableEq, Repr

noncomputable def SingleCode.value : SingleCode → Matrix.unitaryGroup Bool ℂ
  | .hadamard => CircuitCompletion.hadamard
  | .yBasis => CircuitCompletion.yBasis
  | .phase a b => diagonalUnitary
      (fun z => complexPhase (if z then b.value else a.value))
      (fun _ => complexPhase_normSq _)
  | .inverse u => star u.value

/-- Every runtime field is finite discrete data; matrices occur only in
the interpretation, never in the generated instruction list. -/
inductive GateCode (n : ℕ) where
  | single (wire : Fin n) (unitary : SingleCode)
  | cnot (control target : Fin n) (hne : control≠target)

noncomputable def GateCode.value {n : ℕ} : GateCode n → Gate n
  | .single i u => .single i u.value
  | .cnot c t h => .cnot c t h

def GateCode.inverse {n : ℕ} : GateCode n → GateCode n
  | .single i u => .single i (.inverse u)
  | .cnot c t h => .cnot c t h

@[simp] theorem GateCode.inverse_value {n : ℕ} (g : GateCode n) :
    g.inverse.value=g.value.inverse := by cases g <;> rfl

abbrev WordCode (n : ℕ) := List (GateCode n)

noncomputable def interpret {n : ℕ} (w : WordCode n) : Circuit n :=
  w.map GateCode.value

@[simp] theorem interpret_length {n : ℕ} (w : WordCode n) :
    (interpret w).length=w.length := List.length_map _

@[simp] theorem interpret_append {n : ℕ} (w v : WordCode n) :
    interpret (w++v)=interpret w++interpret v := List.map_append

def reverseCode {n : ℕ} (w : WordCode n) : WordCode n :=
  w.reverse.map GateCode.inverse

@[simp] theorem interpret_reverse {n : ℕ} (w : WordCode n) :
    interpret (reverseCode w)=reverseCircuit (interpret w) := by
  simp [interpret,reverseCode,reverseCircuit,List.map_map,Function.comp_def]

@[simp] theorem reverseCode_length {n : ℕ} (w : WordCode n) :
    (reverseCode w).length=w.length := by simp [reverseCode]

def maskOfBits {n : ℕ} (b : Bits n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => b j)

theorem maskOfBits_injective (n : ℕ) : Function.Injective (@maskOfBits n) := by
  intro b c h
  funext j
  have hj := Finset.ext_iff.mp h j
  simp only [maskOfBits,Finset.mem_filter,Finset.mem_univ,true_and] at hj
  cases hb : b j <;> cases hc : c j <;> simp_all

def masks (n : ℕ) : List (Finset (Fin n)) :=
  List.ofFn fun i : Fin (2^n) => maskOfBits (boundedBits n i)

theorem maskIndex_injective (n : ℕ) :
    Function.Injective (fun i : Fin (2^n) => maskOfBits (boundedBits n i)) :=
  (maskOfBits_injective n).comp (boundedBits_injective n)

theorem masks_nodup (n : ℕ) : (masks n).Nodup :=
  List.nodup_ofFn_ofInjective (maskIndex_injective n)

theorem mem_masks {n : ℕ} (S : Finset (Fin n)) : S∈masks n := by
  have hs := (Fintype.bijective_iff_injective_and_card
    (fun i : Fin (2^n) => maskOfBits (boundedBits n i))).mpr
      ⟨maskIndex_injective n,by simp⟩
  obtain ⟨i,hi⟩ := hs.2 S
  exact List.mem_ofFn.mpr ⟨i,hi⟩

theorem masks_length (n : ℕ) : (masks n).length=2^n := by simp [masks]

theorem masks_perm (n : ℕ) :
    (masks n).Perm ((Finset.univ : Finset (Fin n)).powerset.toList) := by
  apply List.perm_ext_iff_of_nodup (masks_nodup n) (Finset.nodup_toList _)|>.mpr
  intro S
  simp [mem_masks]

/-- Sorted finite sets provide a computable control order. -/
def controls {n : ℕ} (t : Fin n) (S : Finset (Fin n)) : List (Control t) :=
  ((S.erase t).sort (·≤·)).attach.map
    (fun i => ⟨i.1,(Finset.mem_erase.mp ((Finset.mem_sort (·≤·)).mp i.2)).1⟩)

theorem controls_length {n : ℕ} (t : Fin n) (S : Finset (Fin n)) :
    (controls t S).length=(S.erase t).card := by simp [controls]

theorem controls_character {n : ℕ} (t : Fin n) (S : Finset (Fin n))
    (ht : t∈S) (w : Bits n) :
    boolSign (Bool.xor (w t) (controlParity (controls t S) w))=maskCharacter S w := by
  rw [boolSign_xor]
  unfold controlParity
  rw [boolSign_foldr]
  simp only [controls,List.map_map,Function.comp_def,List.attach_map_val]
  have hp : (((S.erase t).sort (·≤·)).map (fun i => boolSign (w i))).prod=
      ∏ i∈S.erase t,boolSign (w i) := by
    rw [((Finset.sort_perm_toList (S.erase t) (·≤·)).map _).prod_eq]
    exact Finset.prod_map_toList _ _
  rw [hp]
  exact Finset.mul_prod_erase S (fun i => boolSign (w i)) ht

def cnotCode {n : ℕ} (t : Fin n) (cs : List (Control t)) : WordCode n :=
  cs.map (fun c => .cnot c.1 t c.2)

@[simp] theorem interpret_cnotCode {n : ℕ} (t : Fin n) (cs : List (Control t)) :
    interpret (cnotCode t cs)=cnotWord t cs := by
  simp [interpret,cnotCode,cnotWord,List.map_map,Function.comp_def,GateCode.value]

def parityCode {n : ℕ} (t : Fin n) (cs : List (Control t))
    (a b : AngleCode) : WordCode n :=
  cnotCode t cs++[.single t (.phase a b)]++reverseCode (cnotCode t cs)

theorem parityCode_action {n : ℕ} (t : Fin n) (cs : List (Control t))
    (a b : AngleCode) (v : Bits n → ℂ) :
    run (interpret (parityCode t cs a b)) v=
      fun w => complexPhase (if Bool.xor (w t) (controlParity cs w) then b.value else a.value)*v w := by
  unfold parityCode
  simp only [interpret_append,interpret_cnotCode,interpret_reverse]
  exact parityPhaseWord_action t cs
    (fun z => complexPhase (if z then b.value else a.value))
    (fun _ => complexPhase_normSq _) v

theorem parityCode_length {n : ℕ} (t : Fin n) (cs : List (Control t))
    (a b : AngleCode) : (parityCode t cs a b).length=2*cs.length+1 := by
  simp [parityCode,cnotCode]
  omega

def pauliCode {n : ℕ} (hn : 0<n) (S : Finset (Fin n)) (a : AngleCode) : WordCode n :=
  if hS : S.Nonempty then
    parityCode (S.min' hS) (controls (S.min' hS) S) a a.neg
  else [.single ⟨0,hn⟩ (.phase a a)]

theorem pauliCode_action {n : ℕ} (hn : 0<n) (S : Finset (Fin n))
    (a : AngleCode) (v : Bits n → ℂ) :
    run (interpret (pauliCode hn S a)) v=
      fun w => complexPhase (a.value*maskCharacter S w)*v w := by
  by_cases hS : S.Nonempty
  · rw [pauliCode,dif_pos hS,parityCode_action]
    funext w
    have hc := controls_character (S.min' hS) S (Finset.min'_mem _ _) w
    cases hb : Bool.xor (w (S.min' hS)) (controlParity (controls (S.min' hS) S) w)
    all_goals simp only [hb,boolSign] at hc
    all_goals rw [← hc];simp [hb]
  · have he : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    rw [pauliCode,dif_neg hS]
    simp only [interpret,List.map_cons,List.map_nil,GateCode.value,SingleCode.value,ite_self]
    simp only [run,denote,one_mul]
    rw [singleWire_diagonal_action]
    simp [maskCharacter]

theorem pauliCode_length {n : ℕ} (hn : 0<n) (S : Finset (Fin n)) (a : AngleCode) :
    (pauliCode hn S a).length≤2*n+1 := by
  by_cases hS : S.Nonempty
  · rw [pauliCode,dif_pos hS,parityCode_length,controls_length]
    have hc : (S.erase (S.min' hS)).card≤n :=
      (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by simp)
    omega
  · simp [pauliCode,hS]

def signedCode (a : AngleCode) (b : Bool) : AngleCode := if b then a.neg else a

@[simp] theorem signedCode_value (a : AngleCode) (b : Bool) :
    (signedCode a b).value=a.value*boolSign b := by
  cases b <;> simp [signedCode,boolSign]

def maskParity {n : ℕ} (S : Finset (Fin n)) (x : Bits n) : Bool :=
  ((S.sort (·≤·)).map x).foldr Bool.xor false

theorem maskParity_sign {n : ℕ} (S : Finset (Fin n)) (x : Bits n) :
    boolSign (maskParity S x)=maskCharacter S x := by
  rw [maskParity,boolSign_foldr,List.map_map]
  rw [((Finset.sort_perm_toList S (·≤·)).map _).prod_eq]
  exact Finset.prod_map_toList _ _

def selectedCode {n : ℕ} (hn : 0<n) (x : Bits n) (a : AngleCode) : WordCode n :=
  (masks n).flatMap (fun S => pauliCode hn S (signedCode (a.half n) (maskParity S x)))

theorem run_pauliCodes {n : ℕ} (hn : 0<n) (ss : List (Finset (Fin n)))
    (a : Finset (Fin n) → AngleCode) (v : Bits n → ℂ) :
    run (interpret (ss.flatMap (fun S => pauliCode hn S (a S)))) v=
      fun w => complexPhase ((ss.map (fun S => (a S).value*maskCharacter S w)).sum)*v w := by
  induction ss generalizing v with
  | nil => simp [interpret,run,denote,complexPhase]
  | cons S ss ih =>
    simp only [List.flatMap_cons,interpret_append,run_append,ih,
      pauliCode_action,List.map_cons,List.sum_cons]
    funext w
    simp only [complexPhase_add]
    ring

theorem selectedCode_action {n : ℕ} (hn : 0<n) (x : Bits n) (a : AngleCode)
    (v : Bits n → ℂ) :
    run (interpret (selectedCode hn x a)) v=
      fun w => complexPhase (if w=x then a.value else 0)*v w := by
  rw [selectedCode,run_pauliCodes]
  funext w
  simp only [signedCode_value,AngleCode.half_value,maskParity_sign]
  rw [((masks_perm n).map _).sum_eq,Finset.sum_map_toList]
  simp only [mul_assoc]
  rw [← Finset.mul_sum,walsh_mask_identity]
  by_cases hw : w=x <;> simp [hw]

theorem selectedCode_length {n : ℕ} (hn : 0<n) (x : Bits n) (a : AngleCode) :
    (selectedCode hn x a).length≤2^n*(2*n+1) := by
  simp only [selectedCode,List.length_flatMap]
  calc
    _ ≤ ((masks n).map (fun _ => 2*n+1)).sum := by
      apply List.sum_le_sum
      intro S hS
      exact pauliCode_length hn S _
    _ = _ := by simp [masks_length]

end EffectiveEncoding

