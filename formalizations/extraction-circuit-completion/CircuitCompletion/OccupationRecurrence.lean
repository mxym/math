import CircuitCompletion.OccupationBranch
import SymmetricSupport.FiberFactorial

open scoped BigOperators
open SymmetricSupport
namespace CircuitCompletion

def occupationFactorials {D k : ℕ} (ν : Sym (Fin D) k) : ℕ :=
  ∏ i : Fin D,(ν.val.count i).factorial

theorem occupationFactorials_pos {D k : ℕ} (ν : Sym (Fin D) k) :
    0<occupationFactorials ν := by
  exact Finset.prod_pos (fun i hi => Nat.factorial_pos _)

theorem occupationFactorials_cons {D k : ℕ} (i : Fin D) (mu : Sym (Fin D) k) :
    occupationFactorials (Sym.cons i mu)=(mu.val.count i+1)*occupationFactorials mu := by
  unfold occupationFactorials
  have hν (d : Fin D) : (Sym.cons i mu).val.count d=if d=i then mu.val.count d+1 else mu.val.count d := by
    by_cases h : d=i <;> simp [Sym.cons,Multiset.count_cons,h,eq_comm]
  calc
    _ = ((Sym.cons i mu).val.count i).factorial*
        ∏ d ∈ (Finset.univ : Finset (Fin D)).erase i,((Sym.cons i mu).val.count d).factorial :=
      (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
    _ = ((mu.val.count i+1)*((mu.val.count i).factorial))*
        ∏ d ∈ (Finset.univ : Finset (Fin D)).erase i,(mu.val.count d).factorial := by
      rw [hν i,if_pos rfl,Nat.factorial_succ]
      congr 1
      apply Finset.prod_congr rfl
      intro d hd
      rw [hν d,if_neg (Finset.mem_erase.mp hd).1]
    _ = (mu.val.count i+1)*∏ d : Fin D,(mu.val.count d).factorial := by
      rw [mul_assoc]
      exact congrArg ((mu.val.count i+1)*·)
        (Finset.mul_prod_erase (Finset.univ : Finset (Fin D))
          (fun d : Fin D => (mu.val.count d).factorial) (Finset.mem_univ i))

theorem fiberCard_cons_recurrence {D k : ℕ} (i : Fin D) (mu : Sym (Fin D) k) :
    fiberCard (occupation D k) mu*(k+1)=
      ((Sym.cons i mu).val.count i)*fiberCard (occupation D (k+1)) (Sym.cons i mu) := by
  have hmu := fiberCard_mul_occupation_factorials D k mu
  have hν := fiberCard_mul_occupation_factorials D (k+1) (Sym.cons i mu)
  change fiberCard (occupation D k) mu*occupationFactorials mu=k.factorial at hmu
  change fiberCard (occupation D (k+1)) (Sym.cons i mu)*occupationFactorials (Sym.cons i mu)=
    (k+1).factorial at hν
  apply Nat.eq_of_mul_eq_mul_right (occupationFactorials_pos mu)
  calc
    (fiberCard (occupation D k) mu*(k+1))*occupationFactorials mu=
        (k+1)*(fiberCard (occupation D k) mu*occupationFactorials mu) := by ring
    _ = (k+1)*k.factorial := by rw [hmu]
    _ = (k+1).factorial := (Nat.factorial_succ k).symm
    _ = fiberCard (occupation D (k+1)) (Sym.cons i mu)*occupationFactorials (Sym.cons i mu) := hν.symm
    _ = ((Sym.cons i mu).val.count i)*fiberCard (occupation D (k+1)) (Sym.cons i mu)*
        occupationFactorials mu := by
      rw [occupationFactorials_cons]
      simp only [Sym.cons,Multiset.count_cons_self]
      ring

theorem fiberCard_erase_recurrence {D k : ℕ} (ν : Sym (Fin D) (k+1)) (i : Fin D) (hi : i∈ν) :
    fiberCard (occupation D k) (ν.erase i hi)*(k+1)=
      ν.val.count i*fiberCard (occupation D (k+1)) ν := by
  have h := fiberCard_cons_recurrence i (ν.erase i hi)
  simpa only [Sym.cons_erase hi] using h

theorem occupation_cons {D k : ℕ} (i : Fin D) (w : Word D k) :
    occupation D (k+1) (Fin.cons i w)=Sym.cons i (occupation D k w) := by
  apply Subtype.ext
  have hv : (List.Vector.ofFn (Fin.cons i w)).toList=i::(List.Vector.ofFn w).toList := by
    rw [List.Vector.toList_ofFn,List.Vector.toList_ofFn,List.ofFn_succ]
    rfl
  exact congrArg (fun l : List (Fin D) => (l : Multiset (Fin D))) hv

end CircuitCompletion
