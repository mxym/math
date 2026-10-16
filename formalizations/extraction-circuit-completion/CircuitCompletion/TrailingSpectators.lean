import CircuitCompletion.Spectators

open scoped BigOperators Kronecker
open Matrix
namespace CircuitCompletion

theorem suffixBits_update_suffix {s q : ℕ} (w : Bits (s+q)) (i : Fin q) (b : Bool) :
    suffixBits (Function.update w (Fin.natAdd s i) b)=Function.update (suffixBits w) i b := by
  funext j
  by_cases h : j=i
  · subst j;simp [suffixBits]
  · have h' : Fin.natAdd s j≠Fin.natAdd s i := by simpa using h
    simp [suffixBits,Function.update_of_ne h',Function.update_of_ne h]

theorem prefixBits_update_suffix {s q : ℕ} (w : Bits (s+q)) (i : Fin q) (b : Bool) :
    prefixBits (Function.update w (Fin.natAdd s i) b)=prefixBits w := by
  funext j
  have h : Fin.castAdd q j≠Fin.natAdd s i := by
    intro h
    have h' := congrArg Fin.val h
    simp at h'
    omega
  simp [prefixBits,Function.update_of_ne h]

def Gate.shift {q : ℕ} (s : ℕ) : Gate q → Gate (s+q)
  | .single i U => .single (Fin.natAdd s i) U
  | .cnot c t h => .cnot (Fin.natAdd s c) (Fin.natAdd s t) (by simpa using h)

def shiftCircuit {q : ℕ} (s : ℕ) (a : Circuit q) : Circuit (s+q) := a.map (Gate.shift s)

theorem run_shift_single {s q : ℕ} (g : Gate q) (v : Bits q → ℂ) (z : Bits s → ℂ) :
    run [g.shift s] (fun w => z (prefixBits w)*v (suffixBits w))=
      fun w => z (prefixBits w)*run [g] v (suffixBits w) := by
  cases g with
  | single i U =>
    simp only [Gate.shift,run_single]
    funext w
    simp only [prefixBits_update_suffix,suffixBits_update_suffix,suffixBits]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    ring
  | cnot c t h =>
    rw [run_singleton,run_singleton]
    simp only [Gate.shift,cnot_action]
    funext w
    simp only [cnotFunction,prefixBits_update_suffix,suffixBits_update_suffix,suffixBits]

theorem run_shiftCircuit {s q : ℕ} (a : Circuit q) (v : Bits q → ℂ) (z : Bits s → ℂ) :
    run (shiftCircuit s a) (fun w => z (prefixBits w)*v (suffixBits w))=
      fun w => z (prefixBits w)*run a v (suffixBits w) := by
  induction a generalizing v with
  | nil => simp [shiftCircuit,run,denote]
  | cons g a ih =>
    change run (g.shift s::shiftCircuit s a) _=_
    rw [run_cons,run_shift_single,ih]
    simp only [run_cons g a v]

theorem shiftCircuit_length {q : ℕ} (s : ℕ) (a : Circuit q) :
    (shiftCircuit s a).length=a.length := by simp [shiftCircuit]

/-- Matrix semantics for running an already synthesized suffix circuit,
leaving the two freshly prefixed original-copy wires as spectators. -/
theorem shiftCircuit_matrix {s q : ℕ} (a : Circuit q) :
    (denote (shiftCircuit s a) : Matrix (Bits (s+q)) (Bits (s+q)) ℂ)=
      Matrix.reindex (splitRegister s q).symm (splitRegister s q).symm
        ((1 : Matrix (Bits s) (Bits s) ℂ) ⊗ₖ (denote a : Matrix (Bits q) (Bits q) ℂ)) := by
  classical
  ext w u
  have hprod : (fun p : Bits (s+q) =>
      (Pi.single (prefixBits u) (1 : ℂ) : Bits s → ℂ) (prefixBits p)*
      (Pi.single (suffixBits u) (1 : ℂ) : Bits q → ℂ) (suffixBits p))=Pi.single u 1 := by
    funext p
    by_cases hp : p=u
    · subst p;simp
    · have hsplit : ¬(prefixBits p=prefixBits u ∧ suffixBits p=suffixBits u) := by
        rintro ⟨h1,h2⟩
        apply hp
        apply (splitRegister s q).injective
        exact Prod.ext h1 h2
      by_cases h1 : prefixBits p=prefixBits u <;>
        by_cases h2 : suffixBits p=suffixBits u <;> simp_all [Pi.single_apply,eq_comm]
  have h := run_shiftCircuit a (Pi.single (suffixBits u) 1) (Pi.single (prefixBits u) 1)
  rw [hprod] at h
  simp only [run,Matrix.mulVec_single_one] at h
  have he := congrFun h w
  simpa [Matrix.reindex_apply,splitRegister,Matrix.one_apply,Pi.single_apply,eq_comm] using he

end CircuitCompletion
