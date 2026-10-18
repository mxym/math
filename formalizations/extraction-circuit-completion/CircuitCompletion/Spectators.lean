import CircuitCompletion.AdjacentSwap

open scoped BigOperators Kronecker
open Matrix
namespace CircuitCompletion

def prefixBits {q r : ℕ} (w : Bits (q+r)) : Bits q := fun i => w (Fin.castAdd r i)
def suffixBits {q r : ℕ} (w : Bits (q+r)) : Bits r := fun i => w (Fin.natAdd q i)

theorem prefixBits_update {q r : ℕ} (w : Bits (q+r)) (i : Fin q) (b : Bool) :
    prefixBits (Function.update w (Fin.castAdd r i) b)=Function.update (prefixBits w) i b := by
  funext j
  by_cases h : j=i
  · subst j;simp [prefixBits]
  · have h' : Fin.castAdd r j≠Fin.castAdd r i := by simpa using h
    simp [prefixBits,Function.update_of_ne h',Function.update_of_ne h]

theorem suffixBits_update {q r : ℕ} (w : Bits (q+r)) (i : Fin q) (b : Bool) :
    suffixBits (Function.update w (Fin.castAdd r i) b)=suffixBits w := by
  funext j
  have h : Fin.natAdd q j≠Fin.castAdd r i := by
    intro h
    have h' := congrArg Fin.val h
    simp at h'
    omega
  simp [suffixBits,Function.update_of_ne h]

def Gate.lift {q : ℕ} (r : ℕ) : Gate q → Gate (q+r)
  | .single i U => .single (Fin.castAdd r i) U
  | .cnot c t h => .cnot (Fin.castAdd r c) (Fin.castAdd r t) (by simpa using h)

def liftCircuit {q : ℕ} (r : ℕ) (a : Circuit q) : Circuit (q+r) := a.map (Gate.lift r)

theorem run_singleton {n : ℕ} (g : Gate n) (v : Bits n → ℂ) :
    run [g] v=(g.denote : Matrix (Bits n) (Bits n) ℂ)*ᵥv := by
  simp only [run,denote,one_mul]

/-- An elementary gate is embedded in existing original wires. Arbitrary
spectator amplitudes are preserved, with no initialization requirement. -/
theorem run_lift_single {q r : ℕ} (g : Gate q) (v : Bits q → ℂ) (z : Bits r → ℂ) :
    run [g.lift r] (fun w => v (prefixBits w)*z (suffixBits w))=
      fun w => run [g] v (prefixBits w)*z (suffixBits w) := by
  cases g with
  | single i U =>
    simp only [Gate.lift,run_single]
    funext w
    simp only [Gate.lift,prefixBits_update,suffixBits_update,prefixBits]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b hb
    ring
  | cnot c t h =>
    rw [run_singleton,run_singleton]
    simp only [Gate.lift,cnot_action]
    funext w
    simp only [cnotFunction,prefixBits_update,suffixBits_update,prefixBits]

theorem run_cons {n : ℕ} (g : Gate n) (a : Circuit n) (v : Bits n → ℂ) :
    run (g::a) v=run a (run [g] v) := run_append [g] a v

/-- Exact matrix/tensor semantics for a complete embedded gate list on the
original register. This is stated on all product vectors, not only zeros. -/
theorem run_liftCircuit {q r : ℕ} (a : Circuit q) (v : Bits q → ℂ) (z : Bits r → ℂ) :
    run (liftCircuit r a) (fun w => v (prefixBits w)*z (suffixBits w))=
      fun w => run a v (prefixBits w)*z (suffixBits w) := by
  induction a generalizing v with
  | nil => simp [liftCircuit,run,denote]
  | cons g a ih =>
    change run (g.lift r::liftCircuit r a) _=_
    rw [run_cons,run_lift_single,ih]
    simp only [run_cons g a v]

theorem liftCircuit_length {q : ℕ} (r : ℕ) (a : Circuit q) :
    (liftCircuit r a).length=a.length := by simp [liftCircuit]

def splitRegister (q r : ℕ) : Bits (q+r) ≃ Bits q×Bits r where
  toFun w := (prefixBits w,suffixBits w)
  invFun p := Fin.append p.1 p.2
  left_inv w := by
    funext j
    refine Fin.addCases ?_ ?_ j
    · intro i;simp [prefixBits]
    · intro i;simp [suffixBits]
  right_inv p := by
    apply Prod.ext
    · funext i;simp [prefixBits]
    · funext i;simp [suffixBits]

/-- Full matrix equality, hence valid also on entangled inputs and every
input density matrix: lifting a word is exactly U tensor identity. -/
theorem liftCircuit_matrix {q r : ℕ} (a : Circuit q) :
    (denote (liftCircuit r a) : Matrix (Bits (q+r)) (Bits (q+r)) ℂ)=
      Matrix.reindex (splitRegister q r).symm (splitRegister q r).symm
        ((denote a : Matrix (Bits q) (Bits q) ℂ) ⊗ₖ (1 : Matrix (Bits r) (Bits r) ℂ)) := by
  classical
  ext w u
  have hprod : (fun p : Bits (q+r) =>
      (Pi.single (prefixBits u) (1 : ℂ) : Bits q → ℂ) (prefixBits p)*
      (Pi.single (suffixBits u) (1 : ℂ) : Bits r → ℂ) (suffixBits p))=Pi.single u 1 := by
    funext p
    by_cases hp : p=u
    · subst p;simp
    · have hsplit : ¬(prefixBits p=prefixBits u ∧ suffixBits p=suffixBits u) := by
        rintro ⟨h1,h2⟩
        apply hp
        apply (splitRegister q r).injective
        exact Prod.ext h1 h2
      by_cases h1 : prefixBits p=prefixBits u <;>
        by_cases h2 : suffixBits p=suffixBits u <;>
        simp_all [Pi.single_apply,eq_comm]
  have h := run_liftCircuit a (Pi.single (prefixBits u) 1) (Pi.single (suffixBits u) 1)
  rw [hprod] at h
  simp only [run,Matrix.mulVec_single_one] at h
  have he := congrFun h w
  simpa [Matrix.reindex_apply,splitRegister,Matrix.one_apply,Pi.single_apply,eq_comm] using he

end CircuitCompletion
