import CircuitCompletion.ParityWord
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators
open Matrix
namespace CircuitCompletion

def boolSign (b : Bool) : ℝ := if b then -1 else 1

theorem boolSign_xor (b c : Bool) : boolSign (Bool.xor b c)=boolSign b*boolSign c := by
  cases b <;> cases c <;> norm_num [boolSign]

theorem boolSign_foldr (bs : List Bool) :
    boolSign (bs.foldr Bool.xor false)=(bs.map boolSign).prod := by
  induction bs with
  | nil => simp [boolSign]
  | cons b bs ih => simp [boolSign_xor,ih]

noncomputable def complexPhase (θ : ℝ) : ℂ := Complex.exp ((θ : ℂ)*Complex.I)

theorem complexPhase_normSq (θ : ℝ) : Complex.normSq (complexPhase θ)=1 := by
  rw [Complex.normSq_eq_norm_sq]
  simp [complexPhase,Complex.norm_exp_ofReal_mul_I]

theorem complexPhase_add (θ φ : ℝ) : complexPhase (θ+φ)=complexPhase θ*complexPhase φ := by
  simp only [complexPhase,Complex.ofReal_add,add_mul,Complex.exp_add]

def maskCharacter {n : ℕ} (S : Finset (Fin n)) (w : Bits n) : ℝ :=
  ∏ i ∈ S,boolSign (w i)

noncomputable def maskControls {n : ℕ} (t : Fin n) (S : Finset (Fin n)) :
    List (Control t) :=
  (S.erase t).attach.toList.map (fun i => ⟨i.1,(Finset.mem_erase.mp i.2).1⟩)

theorem maskControls_length {n : ℕ} (t : Fin n) (S : Finset (Fin n)) :
    (maskControls t S).length=(S.erase t).card := by simp [maskControls]

theorem maskControls_character {n : ℕ} (t : Fin n) (S : Finset (Fin n))
    (ht : t∈S) (w : Bits n) :
    boolSign (Bool.xor (w t) (controlParity (maskControls t S) w))=maskCharacter S w := by
  rw [boolSign_xor]
  unfold controlParity
  rw [boolSign_foldr]
  simp only [maskControls,List.map_map,Function.comp_def]
  rw [Finset.prod_map_toList,Finset.prod_attach (S.erase t) (fun i => boolSign (w i))]
  exact Finset.mul_prod_erase S (fun i => boolSign (w i)) ht

/-- A concrete original-register CNOT/one-wire word for exp(i θ Z_S).
The empty Pauli string uses a scalar one-wire phase on an existing wire. -/
noncomputable def pauliWord {n : ℕ} (hn : 0<n) (S : Finset (Fin n)) (θ : ℝ) : Circuit n :=
  if hS : S.Nonempty then
    let t := S.min' hS
    parityPhaseWord t (maskControls t S)
      (fun b => complexPhase (θ*boolSign b)) (fun b => complexPhase_normSq _)
  else
    [Gate.single ⟨0,hn⟩ (diagonalUnitary (fun _ => complexPhase θ)
      (fun _ => complexPhase_normSq _))]

theorem pauliWord_action {n : ℕ} (hn : 0<n) (S : Finset (Fin n)) (θ : ℝ)
    (v : Bits n → ℂ) :
    run (pauliWord hn S θ) v=fun w => complexPhase (θ*maskCharacter S w)*v w := by
  by_cases hS : S.Nonempty
  · simp only [pauliWord,dif_pos hS]
    rw [parityPhaseWord_action]
    funext w
    rw [maskControls_character _ _ (Finset.min'_mem _ _) w]
  · have hSe : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    simp only [pauliWord,dif_neg hS]
    have hsingle (u : Bits n → ℂ) :
        run [Gate.single ⟨0,hn⟩ (diagonalUnitary (fun _ => complexPhase θ)
          (fun _ => complexPhase_normSq _))] u=
        ((Gate.single ⟨0,hn⟩ (diagonalUnitary (fun _ => complexPhase θ)
          (fun _ => complexPhase_normSq _))).denote : Matrix (Bits n) (Bits n) ℂ)*ᵥu := by
      simp only [run,denote,one_mul]
    rw [hsingle,singleWire_diagonal_action]
    simp [maskCharacter]

theorem pauliWord_length {n : ℕ} (hn : 0<n) (S : Finset (Fin n)) (θ : ℝ) :
    (pauliWord hn S θ).length≤2*n+1 := by
  by_cases hS : S.Nonempty
  · simp only [pauliWord,dif_pos hS,parityPhaseWord_length,maskControls_length]
    have hc : (S.erase (S.min' hS)).card≤n :=
      (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by simp)
    omega
  · simp [pauliWord,hS]

end CircuitCompletion
