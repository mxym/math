import CircuitCompletion.CompiledGivens

open scoped BigOperators
open Matrix
namespace CircuitCompletion

theorem swapWord_denote {n : ℕ} (hn : 0<n) (x y : Bits n) :
    denote (swapWord hn x y)=permutationUnitary (Equiv.swap x y) := by
  apply Subtype.ext
  apply Matrix.mulVec_injective
  funext v
  change run (swapWord hn x y) v=_
  rw [swapWord_action,permutationUnitary_action]
  rfl

/-- Raw two-level instructions still denote explicit original-space matrices.
They are compiled below, rather than being treated as physical primitives. -/
inductive TwoLevel (n : ℕ) where
  | swap (x y : Bits n)
  | givens (x y : Bits n) (h : x≠y) (a b : ℝ) (ha : 0≤a) (hb : 0≤b)

noncomputable def TwoLevel.denote {n : ℕ} : TwoLevel n → Matrix.unitaryGroup (Bits n) ℂ
  | .swap x y => permutationUnitary (Equiv.swap x y)
  | .givens x y h a b ha hb => mergeAt x y h a b ha hb

noncomputable def TwoLevel.compile {n : ℕ} (hn : 0<n) : TwoLevel n → Circuit n
  | .swap x y => swapWord hn x y
  | .givens x y h a b _ _ => mergeWord hn x y h a b

theorem TwoLevel.compile_denote {n : ℕ} (hn : 0<n) (g : TwoLevel n) :
    CircuitCompletion.denote (g.compile hn)=g.denote := by
  cases g with
  | swap x y => exact swapWord_denote hn x y
  | givens x y h a b ha hb => exact mergeWord_denote hn x y h a b ha hb

theorem elementary_twoLevel_bound (n : ℕ) (hn : 0<n) :
    2*n*(2^n*(2*n+1)+2)+2*(2^n*(2*n+1))+2≤20*n^2*2^n := by
  have hL : 1≤2^n := Nat.one_le_pow n 2 (by decide)
  have hnn : n≤n*n := by nlinarith
  have h1 : n*2^n≤n*n*2^n := Nat.mul_le_mul_right _ hnn
  have h2 : 2^n≤n*n*2^n := by
    simpa using Nat.mul_le_mul_right (2^n) (by nlinarith : 1≤n*n)
  have h3 : n≤n*n*2^n := (hnn.trans (Nat.le_mul_of_pos_right _ (by positivity)))
  have h4 : 1≤n*n*2^n := by omega
  nlinarith

theorem TwoLevel.compile_length {n : ℕ} (hn : 0<n) (g : TwoLevel n) :
    (g.compile hn).length≤20*n^2*2^n := by
  cases g with
  | swap x y =>
    exact (swapWord_length hn x y).trans (by
      have h := elementary_twoLevel_bound n hn
      nlinarith [Nat.zero_le (2^n*(2*n+1))])
  | givens x y h a b ha hb =>
    exact (mergeWord_length hn x y h a b).trans (elementary_twoLevel_bound n hn)

noncomputable def rawDenote {n : ℕ} : List (TwoLevel n) → Matrix.unitaryGroup (Bits n) ℂ
  | [] => 1
  | g::gs => rawDenote gs*g.denote

noncomputable def compileProgram {n : ℕ} (hn : 0<n) (a : List (TwoLevel n)) : Circuit n :=
  a.flatMap (TwoLevel.compile hn)

/-- The literal elementary word denotes the same sole-register unitary as
its complete raw program. This is a semantics theorem, not an oracle field. -/
theorem compileProgram_denote {n : ℕ} (hn : 0<n) (a : List (TwoLevel n)) :
    denote (compileProgram hn a)=rawDenote a := by
  induction a with
  | nil => rfl
  | cons g gs ih =>
    change denote (g.compile hn++compileProgram hn gs)=_
    rw [denote_append,ih,TwoLevel.compile_denote]
    rfl

theorem compileProgram_length {n : ℕ} (hn : 0<n) (a : List (TwoLevel n)) :
    (compileProgram hn a).length≤a.length*(20*n^2*2^n) := by
  induction a with
  | nil => simp [compileProgram]
  | cons g gs ih =>
    change (g.compile hn++compileProgram hn gs).length≤_
    rw [List.length_append,List.length_cons]
    have h := g.compile_length hn
    nlinarith

end CircuitCompletion
