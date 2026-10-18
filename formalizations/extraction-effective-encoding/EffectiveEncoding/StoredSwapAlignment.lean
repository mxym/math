import EffectiveEncoding.RawCompiler

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

abbrev StoredSwaps (n : ℕ) := List (Bits n×Bits n)

/-- Apply each already stored transposition once, oldest first. The returned
annotation counts swap applications, not endpoint equality or bit operations. -/
def applyStoredSwaps {n : ℕ} : StoredSwaps n → Bits n → Bits n×ℕ
  | [],x => (x,0)
  | (a,b)::ss,x =>
    let previous:=applyStoredSwaps ss x
    (Equiv.swap a b previous.1,previous.2+1)

/-- Specification only: the runtime interpreter above traverses the stored
list and does not evaluate this composed permutation closure. -/
def storedSwapPermutation {n : ℕ} : StoredSwaps n → Equiv.Perm (Bits n)
  | [] => 1
  | (a,b)::ss => Equiv.swap a b*storedSwapPermutation ss


theorem applyStoredSwaps_value {n : ℕ} (ss : StoredSwaps n) (x : Bits n) :
    (applyStoredSwaps ss x).1=storedSwapPermutation ss x := by
  induction ss with
  | nil => rfl
  | cons ab ss ih =>
    rcases ab with ⟨a,b⟩
    simp only [applyStoredSwaps,storedSwapPermutation,Equiv.Perm.mul_apply,ih]

theorem applyStoredSwaps_count {n : ℕ} (ss : StoredSwaps n) (x : Bits n) :
    (applyStoredSwaps ss x).2=ss.length := by
  induction ss with
  | nil => rfl
  | cons ab ss ih => simp only [applyStoredSwaps,List.length_cons,ih]

structure StoredAlignmentRun (n : ℕ) where
  word : WordCode n
  swapApplications : ℕ

/-- Endpoints are computed and stored once per step. The next application
reads this explicit stack; no old permutation closure is used at runtime. -/
def storedAlignmentRun {ι : Type*} {n : ℕ} (hn : 0<n) (e f : ι ↪ Bits n) :
    List ι → StoredSwaps n → StoredAlignmentRun n
  | [],_ => ⟨[],0⟩
  | i::is,ss =>
    let evaluated:=applyStoredSwaps ss (e i)
    let a:=evaluated.1
    let b:=f i
    let headCode:=swapCode hn a b
    let tail:=storedAlignmentRun hn e f is ((a,b)::ss)
    ⟨headCode++tail.word,evaluated.2+tail.swapApplications⟩

/-- Exact code equality, including literal angles, wire indices and order. -/
theorem storedAlignmentRun_word {ι : Type*} {n : ℕ} (hn : 0<n) (e f : ι ↪ Bits n)
    (xs : List ι) (ss : StoredSwaps n) :
    (storedAlignmentRun hn e f xs ss).word=alignmentCode hn e f xs (storedSwapPermutation ss) := by
  induction xs generalizing ss with
  | nil => rfl
  | cons i xs ih =>
    simp only [storedAlignmentRun,alignmentCode,ih,storedSwapPermutation,applyStoredSwaps_value]


theorem storedAlignmentRun_count {ι : Type*} {n : ℕ} (hn : 0<n) (e f : ι ↪ Bits n)
    (xs : List ι) (ss : StoredSwaps n) :
    2*(storedAlignmentRun hn e f xs ss).swapApplications=
      2*xs.length*ss.length+xs.length*(xs.length-1) := by
  induction xs generalizing ss with
  | nil => simp [storedAlignmentRun]
  | cons i xs ih =>
    have ht:=ih (((applyStoredSwaps ss (e i)).1,f i)::ss)
    simp only [List.length_cons] at ht
    change 2*((applyStoredSwaps ss (e i)).2+
      (storedAlignmentRun hn e f xs (((applyStoredSwaps ss (e i)).1,f i)::ss)).swapApplications)=_
    rw [applyStoredSwaps_count]
    simp only [List.length_cons]
    cases hl : xs.length with
    | zero => simp only [hl,Nat.zero_mul,Nat.zero_add,Nat.zero_sub] at ht ⊢;omega
    | succ l => simp only [hl,Nat.add_sub_cancel,Nat.succ_sub_one] at ht ⊢;nlinarith


theorem storedAlignmentRun_empty_word {ι : Type*} {n : ℕ} (hn : 0<n) (e f : ι ↪ Bits n)
    (xs : List ι) : (storedAlignmentRun hn e f xs []).word=alignmentCode hn e f xs 1 :=
  storedAlignmentRun_word hn e f xs []


theorem storedAlignmentRun_empty_count_bound {ι : Type*} {n : ℕ} (hn : 0<n) (e f : ι ↪ Bits n)
    (xs : List ι) : (storedAlignmentRun hn e f xs []).swapApplications≤xs.length^2 := by
  have h:=storedAlignmentRun_count hn e f xs []
  have hm:=Nat.mul_le_mul_left xs.length (Nat.sub_le xs.length 1)
  simp only [List.length_nil,Nat.mul_zero,Nat.zero_add] at h
  rw [pow_two]
  omega

end EffectiveEncoding
