import CircuitCompletion.OccupationStep
import CircuitCompletion.OriginalBits
import CircuitCompletion.TrailingSpectators
import CircuitCompletion.BellPreparation

open scoped BigOperators
open Matrix SymmetricSupport CircuitCompletion
namespace CircuitRecursion

def castBits {m n : ℕ} (h : m=n) (b : Bits m) : Bits n := h ▸ b
def castCircuit {m n : ℕ} (h : m=n) (c : Circuit m) : Circuit n := h ▸ c

@[simp] theorem castBits_rfl {n : ℕ} (b : Bits n) : castBits rfl b=b := rfl
@[simp] theorem castCircuit_rfl {n : ℕ} (c : Circuit n) : castCircuit rfl c=c := rfl

theorem castCircuit_length {m n : ℕ} (h : m=n) (c : Circuit m) :
    (castCircuit h c).length=c.length := by subst n; rfl

theorem run_castCircuit {m n : ℕ} (h : m=n) (c : Circuit m) (v : Bits m → ℂ) :
    run (castCircuit h c) (fun b => v (castBits h.symm b))=
      fun b => run c v (castBits h.symm b) := by subst n; rfl

def pad {q : ℕ} (r : ℕ) (b : Bits q) : Bits (q+r) := Fin.append b (zeroBits r)

@[simp] theorem prefix_append {q r : ℕ} (x : Bits q) (y : Bits r) :
    prefixBits (Fin.append x y)=x := by funext i; simp [prefixBits]
@[simp] theorem suffix_append {q r : ℕ} (x : Bits q) (y : Bits r) :
    suffixBits (Fin.append x y)=y := by funext i; simp [suffixBits]

def padEmbedding {ι : Type*} {q : ℕ} (r : ℕ) (e : ι ↪ Bits q) : ι ↪ Bits (q+r) where
  toFun i := pad r (e i)
  inj' := by
    intro i j h
    apply e.injective
    funext b
    simpa [pad] using congrFun h (Fin.castAdd r b)

theorem single_append {q r : ℕ} (x : Bits q) (y : Bits r) :
    (Pi.single (Fin.append x y) 1 : Bits (q+r) → ℂ)=
      fun w => (Pi.single x 1 : Bits q → ℂ) (prefixBits w)*
        (Pi.single y 1 : Bits r → ℂ) (suffixBits w) := by
  classical
  funext w
  have he : w=Fin.append x y ↔ prefixBits w=x ∧ suffixBits w=y := by
    constructor
    · intro h; subst w; simp
    · rintro ⟨h1,h2⟩
      apply (splitRegister q r).injective
      change (prefixBits w,suffixBits w)=(prefixBits (Fin.append x y),suffixBits (Fin.append x y))
      simpa using (Prod.ext h1 h2 : (prefixBits w,suffixBits w)=(x,y))
  have he' : Fin.append x y=w ↔ prefixBits w=x ∧ suffixBits w=y := by
    rw [eq_comm]; exact he
  simp only [Pi.single_apply,he,he']
  by_cases h1 : prefixBits w=x <;> by_cases h2 : suffixBits w=y <;>
    simp [h1,h2,eq_comm]

theorem run_shift_slice {s q : ℕ} (c : Circuit q) (v : Bits (s+q) → ℂ)
    (x : Bits s) (y : Bits q) :
    run (shiftCircuit s c) v (Fin.append x y)=
      run c (fun b => v (Fin.append x b)) y := by
  classical
  simp only [run,shiftCircuit_matrix,Matrix.mulVec,dotProduct]
  rw [← (splitRegister s q).symm.sum_comp]
  simp [Matrix.reindex_apply,splitRegister,Matrix.kronecker_apply,Matrix.one_apply,
    Fintype.sum_prod_type]

theorem encodedBranch_apply_append {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q)
    (ν : Sym (Fin 4) (k+1)) (i : Fin 4) (b : Bits q) :
    encodedBranch enc ν (Fin.append (letterBits i) b)=
      if hi : i∈ν then (Real.sqrt (occupationMass ν i) : ℂ)*
        (Pi.single (enc (ν.erase i hi)) 1 : Bits q → ℂ) b else 0 := by
  classical
  have he (j : {i : Fin 4 // i∈ν}) :
      Fin.append (letterBits i) b=branchCoordinates enc ν j.1 j.2 ↔
        i=j.1 ∧ b=enc (ν.erase j.1 j.2) := by
    constructor
    · intro h
      constructor
      · apply letterBits.injective
        funext t
        simpa [branchCoordinates] using congrFun h (Fin.castAdd q t)
      · funext t
        simpa [branchCoordinates] using congrFun h (Fin.natAdd 2 t)
    · rintro ⟨h1,h2⟩; subst i; subst b; rfl
  change (∑ j : {i : Fin 4 // i∈ν},
    (if Fin.append (letterBits i) b=branchCoordinates enc ν j.1 j.2 then (1 : ℂ) else 0)*
      (Real.sqrt (occupationMass ν j.1) : ℂ))=_
  simp only [he]
  by_cases hi : i∈ν
  · rw [dif_pos hi]
    rw [Finset.sum_eq_single ⟨i,hi⟩]
    · simp [Pi.single_apply,eq_comm]
    · intro j hj hn
      have hne : i≠j.1 := by intro h; apply hn; exact Subtype.ext h.symm
      simp [hne]
    · simp
  · rw [dif_neg hi]
    apply Finset.sum_eq_zero
    intro j hj
    have hne : i≠j.1 := by intro h; exact hi (h ▸ j.2)
    simp [hne]

end CircuitRecursion
