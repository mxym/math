import CircuitCompletion.RawCompiler
import Mathlib.GroupTheory.Perm.Sign

open Matrix
namespace CircuitCompletion

theorem permutationUnitary_one {ι : Type*} [Fintype ι] [DecidableEq ι] :
    permutationUnitary (1 : Equiv.Perm ι)=1 := by
  apply Subtype.ext
  apply Matrix.mulVec_injective
  funext v
  rw [permutationUnitary_action]
  change v=(1 : Matrix ι ι ℂ)*ᵥv
  rw [Matrix.one_mulVec]

theorem permutationUnitary_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e f : Equiv.Perm ι) : permutationUnitary (e*f)=permutationUnitary e*permutationUnitary f := by
  apply Subtype.ext
  apply Matrix.mulVec_injective
  funext v
  simp only [Matrix.UnitaryGroup.mul_val,← Matrix.mulVec_mulVec,permutationUnitary_action]
  rfl

theorem rawDenote_append {n : ℕ} (a b : List (TwoLevel n)) :
    rawDenote (a++b)=rawDenote b*rawDenote a := by
  induction a with
  | nil => simp [rawDenote]
  | cons g gs ih => simp only [List.cons_append,rawDenote,ih,mul_assoc]

/-- Finite selection-sort factorization into at most one transposition for
each input basis string. This is a literal recursively generated raw list. -/
noncomputable def permutationProgramAux {n : ℕ} :
    List (Bits n) → Equiv.Perm (Bits n) → List (TwoLevel n)
  | [],_ => []
  | x::xs,f => if x=f x then permutationProgramAux xs f else
      permutationProgramAux xs (Equiv.swap x (f x)*f)++[TwoLevel.swap x (f x)]

theorem permutationProgramAux_length {n : ℕ} (xs : List (Bits n)) (f : Equiv.Perm (Bits n)) :
    (permutationProgramAux xs f).length≤xs.length := by
  induction xs generalizing f with
  | nil => simp [permutationProgramAux]
  | cons x xs ih =>
    by_cases h : x=f x
    · simp only [permutationProgramAux,if_pos h,List.length_cons]
      exact (ih f).trans (Nat.le_succ _)
    · simp only [permutationProgramAux,if_neg h,List.length_append,List.length_singleton,List.length_cons]
      exact Nat.succ_le_succ (ih _)

theorem permutationProgramAux_denote {n : ℕ} (xs : List (Bits n)) (f : Equiv.Perm (Bits n))
    (hf : ∀ w,f w≠w → w∈xs) : rawDenote (permutationProgramAux xs f)=permutationUnitary f := by
  induction xs generalizing f with
  | nil =>
    have he : f=1 := by
      apply Equiv.ext
      intro w
      by_contra h
      exact List.not_mem_nil (hf w h)
    simp [permutationProgramAux,rawDenote,he,permutationUnitary_one]
  | cons x xs ih =>
    by_cases h : x=f x
    · simp only [permutationProgramAux,if_pos h]
      apply ih
      intro w hw
      have hwx : w≠x := by intro hwx;subst w;exact hw h.symm
      exact List.mem_of_ne_of_mem hwx (hf w hw)
    · simp only [permutationProgramAux,if_neg h,rawDenote_append,rawDenote,one_mul,
        TwoLevel.denote]
      have htail : ∀ w,(Equiv.swap x (f x)*f) w≠w → w∈xs := by
        intro w hw
        have hh := Equiv.Perm.ne_and_ne_of_swap_mul_apply_ne_self hw
        exact List.mem_of_ne_of_mem hh.2 (hf w hh.1)
      rw [ih _ htail,← permutationUnitary_mul,Equiv.swap_mul_self_mul]

noncomputable def permutationProgram {n : ℕ} (f : Equiv.Perm (Bits n)) : List (TwoLevel n) :=
  permutationProgramAux Finset.univ.toList f

theorem permutationProgram_denote {n : ℕ} (f : Equiv.Perm (Bits n)) :
    rawDenote (permutationProgram f)=permutationUnitary f := by
  apply permutationProgramAux_denote
  intro w hw
  simp

theorem permutationProgram_length {n : ℕ} (f : Equiv.Perm (Bits n)) :
    (permutationProgram f).length≤2^n := by
  exact (permutationProgramAux_length _ f).trans_eq (by simp [Bits])

noncomputable def permutationWord {n : ℕ} (hn : 0<n) (f : Equiv.Perm (Bits n)) : Circuit n :=
  compileProgram hn (permutationProgram f)

theorem permutationWord_denote {n : ℕ} (hn : 0<n) (f : Equiv.Perm (Bits n)) :
    denote (permutationWord hn f)=permutationUnitary f := by
  rw [permutationWord,compileProgram_denote,permutationProgram_denote]

theorem permutationWord_length {n : ℕ} (hn : 0<n) (f : Equiv.Perm (Bits n)) :
    (permutationWord hn f).length≤20*n^2*(2^n)^2 := by
  apply (compileProgram_length hn (permutationProgram f)).trans
  have h := Nat.mul_le_mul_right (20*n^2*2^n) (permutationProgram_length f)
  nlinarith

end CircuitCompletion
