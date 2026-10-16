import CircuitCompletion.FourMerge
import SymmetricSupport.Occupation

open scoped BigOperators
open Matrix
namespace CircuitCompletion

theorem multiset_sum_counts {α : Type*} [Fintype α] [DecidableEq α] (s : Multiset α) :
    (∑ i,s.count i)=s.card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih => simp [Multiset.count_cons,Finset.sum_add_distrib,ih]

noncomputable def occupationMass {k : ℕ} (ν : Sym (Fin 4) (k+1)) (i : Fin 4) : ℝ :=
  (ν.val.count i:ℝ)/(k+1)

theorem occupationMass_nonneg {k : ℕ} (ν : Sym (Fin 4) (k+1)) (i : Fin 4) :
    0 ≤ occupationMass ν i := by unfold occupationMass;positivity

theorem occupationMass_sum {k : ℕ} (ν : Sym (Fin 4) (k+1)) :
    (∑ i,occupationMass ν i)=1 := by
  simp only [occupationMass,← Finset.sum_div,← Nat.cast_sum,multiset_sum_counts,ν.property]
  push_cast
  exact div_self (by positivity)

/-- Branch labels are actual predecessor occupations and the actual next
letter. Equal labels recover the entire successor occupation. -/
theorem predecessor_labels_disjoint {k : ℕ} (ν μ : Sym (Fin 4) (k+1))
    (i j : Fin 4) (hi : i∈ν) (hj : j∈μ)
    (h : (ν.erase i hi,i)=(μ.erase j hj,j)) : ν=μ := by
  have hij : i=j := congrArg Prod.snd h
  subst j
  calc
    ν=i ::ₛ ν.erase i hi := (Sym.cons_erase hi).symm
    _=i ::ₛ μ.erase i hj := congrArg (Sym.cons i) (congrArg Prod.fst h)
    _=μ := Sym.cons_erase hj

/-- The normalized four coefficients in the paper are compressed by the
explicit three Givens matrices, including occupations with absent letters. -/
theorem compress_occupation_coefficients {k : ℕ} (ν : Sym (Fin 4) (k+1)) :
    (compressFour (occupationMass ν) (occupationMass_nonneg ν) :
      Matrix (Fin 4) (Fin 4) ℂ)*ᵥ(fun i => (Real.sqrt (occupationMass ν i):ℂ))=
        Pi.single 0 1 := by
  rw [compressFour_action,occupationMass_sum,Real.sqrt_one,Complex.ofReal_one]

end CircuitCompletion
