import EffectiveEncoding.GrayCompiler

open CircuitCompletion CircuitRecursion Matrix
namespace EffectiveEncoding

theorem swapCode_denote {n : ℕ} (hn : 0<n) (x y : Bits n) :
    denote (interpret (swapCode hn x y))=permutationUnitary (Equiv.swap x y) := by
  apply Subtype.ext
  apply Matrix.mulVec_injective
  funext v
  change run (interpret (swapCode hn x y)) v=_
  rw [swapCode_action,permutationUnitary_action]
  rfl

theorem rotationCode_denote_eq {n : ℕ} (hn : 0<n) (x y : Bits n) (h : x≠y)
    (a : AngleCode) :
    denote (interpret (rotationCode hn x y h a))=denote (rotationWord hn x y h a.value) := by
  apply Subtype.ext
  apply Matrix.mulVec_injective
  funext v
  change run (interpret (rotationCode hn x y h a)) v=run (rotationWord hn x y h a.value) v
  rw [rotationCode_action,rotationWord_action]

inductive RawCode (n : ℕ) where
  | swap (x y : Bits n)
  | merge (x y : Bits n) (hne : x≠y) (A B denominator : ℕ)

def mergeCode (A B j : ℕ) : AngleCode := ⟨.merge A B j,false,0⟩

@[simp] theorem mergeCode_value (A B j : ℕ) :
    (mergeCode A B j).value=mergeAngle ((A:ℝ)/j) ((B:ℝ)/j) := by
  simp [mergeCode,AngleCode.value,AngleAtom.value]

noncomputable def RawCode.value {n : ℕ} : RawCode n → TwoLevel n
  | .swap x y => .swap x y
  | .merge x y h A B j => .givens x y h ((A:ℝ)/j) ((B:ℝ)/j)
      (by positivity) (by positivity)

def RawCode.compile {n : ℕ} (hn : 0<n) : RawCode n → WordCode n
  | .swap x y => swapCode hn x y
  | .merge x y h A B j => rotationCode hn x y h (mergeCode A B j)

theorem RawCode.compile_denote {n : ℕ} (hn : 0<n) (g : RawCode n) :
    denote (interpret (g.compile hn))=g.value.denote := by
  cases g with
  | swap x y => exact swapCode_denote hn x y
  | merge x y h A B j =>
    rw [RawCode.compile,rotationCode_denote_eq,mergeCode_value]
    exact mergeWord_denote hn x y h ((A:ℝ)/j) ((B:ℝ)/j) (by positivity) (by positivity)

theorem RawCode.compile_length {n : ℕ} (hn : 0<n) (g : RawCode n) :
    (g.compile hn).length≤20*n^2*2^n := by
  cases g with
  | swap x y =>
    exact (swapCode_length hn x y).trans (by
      have h := elementary_twoLevel_bound n hn
      nlinarith [Nat.zero_le (2^n*(2*n+1))])
  | merge x y h A B j =>
    exact (rotationCode_length hn x y h _).trans (elementary_twoLevel_bound n hn)

def compileRaw {n : ℕ} (hn : 0<n) (xs : List (RawCode n)) : WordCode n :=
  xs.flatMap (RawCode.compile hn)

theorem compileRaw_denote {n : ℕ} (hn : 0<n) (xs : List (RawCode n)) :
    denote (interpret (compileRaw hn xs))=rawDenote (xs.map RawCode.value) := by
  induction xs with
  | nil => rfl
  | cons g gs ih =>
    change denote (interpret (g.compile hn++compileRaw hn gs))=_
    rw [interpret_append,denote_append,ih,RawCode.compile_denote]
    rfl

theorem compileRaw_length {n : ℕ} (hn : 0<n) (xs : List (RawCode n)) :
    (compileRaw hn xs).length≤xs.length*(20*n^2*2^n) := by
  induction xs with
  | nil => simp [compileRaw]
  | cons g gs ih =>
    change (g.compile hn++compileRaw hn gs).length≤_
    rw [List.length_append,List.length_cons]
    have h := g.compile_length hn
    nlinarith

/-- The finite swap-completion algorithm updates an actual permutation
table. It needs no arbitrary equivalence between complements. -/
def alignmentPerm {ι : Type*} {n : ℕ} (e f : ι ↪ Bits n) :
    List ι → Equiv.Perm (Bits n) → Equiv.Perm (Bits n)
  | [],p => p
  | i::is,p => alignmentPerm e f is ((Equiv.swap (p (e i)) (f i))*p)

def alignmentCode {ι : Type*} {n : ℕ} (hn : 0<n) (e f : ι ↪ Bits n) :
    List ι → Equiv.Perm (Bits n) → WordCode n
  | [],_ => []
  | i::is,p => swapCode hn (p (e i)) (f i)++
      alignmentCode hn e f is ((Equiv.swap (p (e i)) (f i))*p)

theorem alignmentPerm_complete {ι : Type*} [DecidableEq ι] {n : ℕ}
    (e f : ι ↪ Bits n) (xs : List ι) (p : Equiv.Perm (Bits n))
    (hp : ∀ i,i∉xs → p (e i)=f i) :
    ∀ i,alignmentPerm e f xs p (e i)=f i := by
  induction xs generalizing p with
  | nil => intro i;exact hp i (by simp)
  | cons x xs ih =>
    apply ih
    intro i hi
    by_cases hix : i=x
    · subst i
      simp [Equiv.Perm.mul_apply]
    · have ho : i∉x::xs := by simp [hix,hi]
      have hpi := hp i ho
      have h1 : f i≠p (e x) := by
        intro h
        have he : p (e i)=p (e x) := hpi.trans h
        exact hix (e.injective (p.injective he))
      have h2 : f i≠f x := by exact fun h => hix (f.injective h)
      change (Equiv.swap (p (e x)) (f x)) (p (e i))=f i
      rw [hpi,Equiv.swap_apply_of_ne_of_ne h1 h2]

theorem alignmentCode_action {ι : Type*} {n : ℕ} (hn : 0<n)
    (e f : ι ↪ Bits n) (xs : List ι) (p : Equiv.Perm (Bits n))
    (w : Bits n) (a : ℂ) :
    run (interpret (alignmentCode hn e f xs p)) (Pi.single (p w) a)=
      Pi.single (alignmentPerm e f xs p w) a := by
  induction xs generalizing p with
  | nil =>
    change (1 : Matrix (Bits n) (Bits n) ℂ)*ᵥPi.single (p w) a=Pi.single (p w) a
    rw [Matrix.one_mulVec]
  | cons i xs ih =>
    rw [alignmentCode,interpret_append,run_append]
    have hs : run (interpret (swapCode hn (p (e i)) (f i))) (Pi.single (p w) a)=
        Pi.single (((Equiv.swap (p (e i)) (f i))*p) w) a := by
      simp only [run,swapCode_denote]
      exact permutationUnitary_single _ _ _
    rw [hs,ih]
    rfl

theorem alignmentCode_length {ι : Type*} {n : ℕ} (hn : 0<n)
    (e f : ι ↪ Bits n) (xs : List ι) (p : Equiv.Perm (Bits n)) :
    (alignmentCode hn e f xs p).length≤xs.length*(20*n^2*2^n) := by
  induction xs generalizing p with
  | nil => simp [alignmentCode]
  | cons i xs ih =>
    rw [alignmentCode,List.length_append,List.length_cons]
    have hs : (swapCode hn (p (e i)) (f i)).length≤20*n^2*2^n :=
      RawCode.compile_length hn (.swap (p (e i)) (f i))
    have ht := ih ((Equiv.swap (p (e i)) (f i))*p)
    nlinarith

theorem alignmentCode_on_embedding {ι : Type*} [DecidableEq ι] {n : ℕ}
    (hn : 0<n) (e f : ι ↪ Bits n) (xs : List ι) (hxs : ∀ i,i∈xs)
    (i : ι) (a : ℂ) :
    run (interpret (alignmentCode hn e f xs 1)) (Pi.single (e i) a)=Pi.single (f i) a := by
  have hp : ∀ i,i∉xs → (1 : Equiv.Perm (Bits n)) (e i)=f i := by
    intro i hi
    exact False.elim (hi (hxs i))
  have h := alignmentCode_action hn e f xs 1 (e i) a
  simpa only [Equiv.Perm.one_apply,alignmentPerm_complete e f xs 1 hp i] using h

end EffectiveEncoding

