import EffectiveEncoding.StoredSwapAlignment

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

abbrev PackedBits (n : ℕ) := List.Vector Bool n

def packBits {n : ℕ} (x : Bits n) : PackedBits n := List.Vector.ofFn x

def unpackBits {n : ℕ} (x : PackedBits n) : Bits n := x.get


theorem unpackBits_packBits {n : ℕ} (x : Bits n) : unpackBits (packBits x)=x := by
  funext i
  exact List.Vector.get_ofFn x i


theorem packBits_unpackBits {n : ℕ} (x : PackedBits n) : packBits (unpackBits x)=x := by
  apply List.Vector.ext
  intro i
  exact List.Vector.get_ofFn x.get i


theorem unpackBits_injective (n : ℕ) : Function.Injective (@unpackBits n) := by
  intro x y h
  apply List.Vector.ext
  intro i
  exact congrFun h i


theorem map_swap_of_injective {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (a b x : α) :
    f (Equiv.swap a b x)=Equiv.swap (f a) (f b) (f x) := by
  by_cases ha : x=a
  · subst x
    simp only [Equiv.swap_apply_left]
  · by_cases hb : x=b
    · subst x
      simp only [Equiv.swap_apply_right]
    · rw [Equiv.swap_apply_of_ne_of_ne ha hb,
        Equiv.swap_apply_of_ne_of_ne (fun h => ha (hf h)) (fun h => hb (hf h))]


def packedStackBits {n : ℕ} (ss : List (PackedBits n×PackedBits n)) : StoredSwaps n :=
  ss.map (fun ab => (unpackBits ab.1,unpackBits ab.2))

/-- Endpoint equality is equality of finite Bool lists. No permutation closure
or function-valued endpoint is stored by this interpreter. -/
def applyPackedSwaps {n : ℕ} : List (PackedBits n×PackedBits n) → PackedBits n → PackedBits n×ℕ
  | [],x => (x,0)
  | (a,b)::ss,x =>
    let previous:=applyPackedSwaps ss x
    (Equiv.swap a b previous.1,previous.2+1)


theorem applyPackedSwaps_value {n : ℕ} (ss : List (PackedBits n×PackedBits n)) (x : PackedBits n) :
    unpackBits (applyPackedSwaps ss x).1=storedSwapPermutation (packedStackBits ss) (unpackBits x) := by
  induction ss with
  | nil => rfl
  | cons ab ss ih =>
    rcases ab with ⟨a,b⟩
    simp only [applyPackedSwaps,packedStackBits,List.map_cons,storedSwapPermutation,Equiv.Perm.mul_apply]
    rw [map_swap_of_injective unpackBits (unpackBits_injective n),ih]
    rfl


theorem applyPackedSwaps_count {n : ℕ} (ss : List (PackedBits n×PackedBits n)) (x : PackedBits n) :
    (applyPackedSwaps ss x).2=ss.length := by
  induction ss with
  | nil => rfl
  | cons ab ss ih => simp only [applyPackedSwaps,List.length_cons,ih]

structure PackedAlignmentRun (n : ℕ) where
  word : WordCode n
  swapApplications : ℕ
  endpointCoordinates : ℕ

/-- Materialize each source/target endpoint exactly once as an n-Bool vector.
Only these vectors are retained by the explicit swap stack. -/
def packedAlignmentRun {ι : Type*} {n : ℕ} (hn : 0<n) (e f : ι ↪ Bits n) :
    List ι → List (PackedBits n×PackedBits n) → PackedAlignmentRun n
  | [],_ => ⟨[],0,0⟩
  | i::is,ss =>
    let source:=packBits (e i)
    let evaluated:=applyPackedSwaps ss source
    let a:=evaluated.1
    let b:=packBits (f i)
    let headCode:=swapCode hn (unpackBits a) (unpackBits b)
    let tail:=packedAlignmentRun hn e f is ((a,b)::ss)
    ⟨headCode++tail.word,evaluated.2+tail.swapApplications,2*n+tail.endpointCoordinates⟩


theorem packedAlignmentRun_word {ι : Type*} {n : ℕ} (hn : 0<n) (e f : ι ↪ Bits n)
    (xs : List ι) (ss : List (PackedBits n×PackedBits n)) :
    (packedAlignmentRun hn e f xs ss).word=alignmentCode hn e f xs (storedSwapPermutation (packedStackBits ss)) := by
  induction xs generalizing ss with
  | nil => rfl
  | cons i xs ih =>
    simp only [packedAlignmentRun,alignmentCode,ih,packedStackBits,List.map_cons,storedSwapPermutation,
      applyPackedSwaps_value,unpackBits_packBits]


theorem packedAlignmentRun_coordinates {ι : Type*} {n : ℕ} (hn : 0<n) (e f : ι ↪ Bits n)
    (xs : List ι) (ss : List (PackedBits n×PackedBits n)) :
    (packedAlignmentRun hn e f xs ss).endpointCoordinates=2*n*xs.length := by
  induction xs generalizing ss with
  | nil => simp [packedAlignmentRun]
  | cons i xs ih => simp only [packedAlignmentRun,ih,List.length_cons];ring


theorem packedAlignmentRun_count {ι : Type*} {n : ℕ} (hn : 0<n) (e f : ι ↪ Bits n)
    (xs : List ι) (ss : List (PackedBits n×PackedBits n)) :
    2*(packedAlignmentRun hn e f xs ss).swapApplications=
      2*xs.length*ss.length+xs.length*(xs.length-1) := by
  induction xs generalizing ss with
  | nil => simp [packedAlignmentRun]
  | cons i xs ih =>
    have ht:=ih (((applyPackedSwaps ss (packBits (e i))).1,packBits (f i))::ss)
    simp only [List.length_cons] at ht
    change 2*((applyPackedSwaps ss (packBits (e i))).2+
      (packedAlignmentRun hn e f xs (((applyPackedSwaps ss (packBits (e i))).1,packBits (f i))::ss)).swapApplications)=_
    rw [applyPackedSwaps_count]
    simp only [List.length_cons]
    cases hl : xs.length with
    | zero => simp only [hl,Nat.zero_mul,Nat.zero_add,Nat.zero_sub] at ht ⊢;omega
    | succ l => simp only [hl,Nat.succ_sub_one] at ht ⊢;nlinarith

end EffectiveEncoding
