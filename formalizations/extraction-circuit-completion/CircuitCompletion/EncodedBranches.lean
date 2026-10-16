import CircuitCompletion.Canonical
import CircuitCompletion.Spectators
import CircuitCompletion.NormalizedBranch
import CircuitCompletion.FidelityError

open scoped BigOperators
open SymmetricSupport Matrix
namespace CircuitCompletion

def letterBits : Fin 4 ≃ Bits 2 :=
  (finFunctionFinEquiv : (Fin 2 → Fin 2) ≃ Fin 4).symm.trans
    (Equiv.piCongrRight (fun _ => finTwoEquiv))

noncomputable def branchCoordinates {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q)
    (ν : Sym (Fin 4) (k+1)) (i : Fin 4) (hi : i∈ν) : Bits (2+q) :=
  Fin.append (letterBits i) (enc (ν.erase i hi))

theorem branchCoordinates_equal {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q)
    (ν μ : Sym (Fin 4) (k+1)) (i j : Fin 4) (hi : i∈ν) (hj : j∈μ)
    (h : branchCoordinates enc ν i hi=branchCoordinates enc μ j hj) : ν=μ ∧ i=j := by
  have hij : i=j := by
    apply letterBits.injective
    funext b
    simpa only [branchCoordinates,Fin.append_left] using congrFun h (Fin.castAdd q b)
  have hp : ν.erase i hi=μ.erase j hj := by
    apply enc.injective
    funext b
    simpa only [branchCoordinates,Fin.append_right] using congrFun h (Fin.natAdd 2 b)
  exact ⟨predecessor_labels_disjoint ν μ i j hi hj (Prod.ext hp hij),hij⟩

noncomputable def branchEmbedding {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q)
    (ν : Sym (Fin 4) (k+1)) : {i : Fin 4 // i∈ν} ↪ Bits (2+q) where
  toFun i := branchCoordinates enc ν i.1 i.2
  inj' := by
    intro i j h
    exact Subtype.ext (branchCoordinates_equal enc ν ν i.1 j.1 i.2 j.2 h).2

theorem branchCoordinates_disjoint {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q)
    (ν μ : Sym (Fin 4) (k+1)) (hνμ : ν≠μ) (i j : Fin 4) (hi : i∈ν) (hj : j∈μ) :
    branchCoordinates enc ν i hi≠branchCoordinates enc μ j hj := by
  intro h
  exact hνμ (branchCoordinates_equal enc ν μ i j hi hj h).1

noncomputable def encodedBranch {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q)
    (ν : Sym (Fin 4) (k+1)) : Bits (2+q) → ℂ :=
  Extraction.coordinateIsometry (branchEmbedding enc ν)*ᵥ
    (fun i => (Real.sqrt (occupationMass ν i.1) : ℂ))

theorem encodedBranch_entry {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q)
    (ν : Sym (Fin 4) (k+1)) (i : Fin 4) (hi : i∈ν) :
    encodedBranch enc ν (branchCoordinates enc ν i hi)=(Real.sqrt (occupationMass ν i) : ℂ) := by
  change (Extraction.coordinateIsometry (branchEmbedding enc ν)*ᵥ
    (fun i => (Real.sqrt (occupationMass ν i.1) : ℂ))) ((branchEmbedding enc ν) ⟨i,hi⟩)=_
  simp only [Matrix.mulVec,dotProduct,Extraction.coordinateIsometry,
    (branchEmbedding enc ν).injective.eq_iff,ite_mul,one_mul,zero_mul]
  simp

theorem encodedBranch_disjoint_zero {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q)
    (ν μ : Sym (Fin 4) (k+1)) (hνμ : ν≠μ) (j : Fin 4) (hj : j∈μ) :
    encodedBranch enc ν (branchCoordinates enc μ j hj)=0 := by
  unfold encodedBranch
  simp only [Matrix.mulVec,dotProduct,Extraction.coordinateIsometry]
  apply Finset.sum_eq_zero
  intro i hi
  have hn := branchCoordinates_disjoint enc ν μ hνμ i.1 j i.2 hj
  change (if branchCoordinates enc μ j hj=branchCoordinates enc ν i.1 i.2 then (1 : ℂ) else 0)*
    (Real.sqrt (occupationMass ν i.1) : ℂ)=0
  simp [Ne.symm hn]

theorem vectorSquare_isometry {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (E : Matrix ι κ ℂ) (hE : Eᴴ*E=1) (v : κ → ℂ) :
    vectorSquare (E*ᵥv)=vectorSquare v := by
  have h := Extraction.isometry_trace_congruence E hE (pureMatrix v)
  change (E*Matrix.vecMulVec v (star v)*Eᴴ).trace=_ at h
  rw [Extraction.congruence_pure] at h
  change (pureMatrix (E*ᵥv)).trace=(pureMatrix v).trace at h
  have hr := congrArg Complex.re h
  simpa only [pureMatrix_trace,Complex.ofReal_re] using hr

theorem occupationMass_occupied_sum {k : ℕ} (ν : Sym (Fin 4) (k+1)) :
    (∑ i : {i : Fin 4 // i∈ν},occupationMass ν i.1)=1 := by
  classical
  have hzero (i : Fin 4) (hi : i∉ν) : occupationMass ν i=0 := by
    have hc : ν.val.count i=0 := Multiset.count_eq_zero.mpr hi
    unfold occupationMass
    rw [hc,Nat.cast_zero,zero_div]
  rw [← Finset.sum_subtype (Finset.univ.filter (fun i : Fin 4 => i∈ν))
    (by intro i;simp) (occupationMass ν),Finset.sum_filter]
  have he (i : Fin 4) : (if i∈ν then occupationMass ν i else 0)=occupationMass ν i := by
    by_cases hi : i∈ν <;> simp [hi,hzero]
  simp only [he]
  exact occupationMass_sum ν

theorem encodedBranch_normalized {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q)
    (ν : Sym (Fin 4) (k+1)) : vectorSquare (encodedBranch enc ν)=1 := by
  rw [encodedBranch,vectorSquare_isometry _ (Extraction.coordinateIsometry_isometry _)]
  unfold vectorSquare
  have he (i : {i : Fin 4 // i∈ν}) :
      Complex.normSq (Real.sqrt (occupationMass ν i.1) : ℂ)=occupationMass ν i.1 := by
    simp [Complex.normSq_apply,← pow_two,Real.sq_sqrt (occupationMass_nonneg ν i.1)]
  simp only [he]
  exact occupationMass_occupied_sum ν

end CircuitCompletion
