import FourRowBasic
open scoped BigOperators ComplexConjugate
namespace FourRowTradeoff
noncomputable section

/-- A kernel-computed enumeration, used only for the exact Laplace identity. -/
def permEnum : Fin 24 → Equiv.Perm (Fin 4) :=
  ![(Equiv.swap 0 0) * (Equiv.swap 1 1) * (Equiv.swap 2 2),
    (Equiv.swap 0 0) * (Equiv.swap 1 1) * (Equiv.swap 2 3),
    (Equiv.swap 0 0) * (Equiv.swap 1 2) * (Equiv.swap 2 2),
    (Equiv.swap 0 0) * (Equiv.swap 1 2) * (Equiv.swap 2 3),
    (Equiv.swap 0 0) * (Equiv.swap 1 3) * (Equiv.swap 2 2),
    (Equiv.swap 0 0) * (Equiv.swap 1 3) * (Equiv.swap 2 3),
    (Equiv.swap 0 1) * (Equiv.swap 1 1) * (Equiv.swap 2 2),
    (Equiv.swap 0 1) * (Equiv.swap 1 1) * (Equiv.swap 2 3),
    (Equiv.swap 0 1) * (Equiv.swap 1 2) * (Equiv.swap 2 2),
    (Equiv.swap 0 1) * (Equiv.swap 1 2) * (Equiv.swap 2 3),
    (Equiv.swap 0 1) * (Equiv.swap 1 3) * (Equiv.swap 2 2),
    (Equiv.swap 0 1) * (Equiv.swap 1 3) * (Equiv.swap 2 3),
    (Equiv.swap 0 2) * (Equiv.swap 1 1) * (Equiv.swap 2 2),
    (Equiv.swap 0 2) * (Equiv.swap 1 1) * (Equiv.swap 2 3),
    (Equiv.swap 0 2) * (Equiv.swap 1 2) * (Equiv.swap 2 2),
    (Equiv.swap 0 2) * (Equiv.swap 1 2) * (Equiv.swap 2 3),
    (Equiv.swap 0 2) * (Equiv.swap 1 3) * (Equiv.swap 2 2),
    (Equiv.swap 0 2) * (Equiv.swap 1 3) * (Equiv.swap 2 3),
    (Equiv.swap 0 3) * (Equiv.swap 1 1) * (Equiv.swap 2 2),
    (Equiv.swap 0 3) * (Equiv.swap 1 1) * (Equiv.swap 2 3),
    (Equiv.swap 0 3) * (Equiv.swap 1 2) * (Equiv.swap 2 2),
    (Equiv.swap 0 3) * (Equiv.swap 1 2) * (Equiv.swap 2 3),
    (Equiv.swap 0 3) * (Equiv.swap 1 3) * (Equiv.swap 2 2),
    (Equiv.swap 0 3) * (Equiv.swap 1 3) * (Equiv.swap 2 3)]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem permEnum_bijective : Function.Bijective permEnum := by decide

theorem sum_perms (f : Equiv.Perm (Fin 4) → ℂ) :
    (∑ σ, f σ) = ∑ i : Fin 24, f (permEnum i) :=
  (Equiv.sum_comp (Equiv.ofBijective permEnum permEnum_bijective) f).symm

def shuffleSign : Fin 6 → ℂ := ![1,-1,1,1,-1,1]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem permanent_laplace (A : Mat) :
    A.permanent = ∑ i, symPair (A 0) (A 1) i *
      symPair (A 2) (A 3) (Fin.rev i) := by
  unfold Matrix.permanent
  rw [sum_perms]
  simp [permEnum, symPair, Fin.sum_univ_succ, Fin.prod_univ_succ,
    Equiv.Perm.mul_apply, Equiv.swap_apply_def, Fin.rev]
  ring

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem det_laplace (A : Mat) :
    A.det = ∑ i, altPair (A 0) (A 1) i *
      (shuffleSign i * altPair (A 2) (A 3) (Fin.rev i)) := by
  rw [Matrix.det_apply, sum_perms]
  simp [permEnum, altPair, shuffleSign, Fin.sum_univ_succ, Fin.prod_univ_succ,
    Equiv.Perm.mul_apply, Equiv.swap_apply_def, Fin.rev,
    Equiv.Perm.sign_mul, Equiv.Perm.sign_swap']
  ring

theorem sym_complement_energy (a b : Row) :
    (∑ i : Fin 6, ‖symPair a b (Fin.rev i)‖^2) = symEnergy a b := by
  simp [symEnergy, normSq_as_sq, Fin.sum_univ_succ, Fin.rev]
  ring

theorem alt_complement_energy (a b : Row) :
    (∑ i : Fin 6, ‖shuffleSign i * altPair a b (Fin.rev i)‖^2) =
      altEnergy a b := by
  simp [altEnergy, normSq_as_sq, shuffleSign, Fin.sum_univ_succ, Fin.rev]
  ring

theorem permanent_sq_bound (A : Mat) :
    ‖A.permanent‖^2 ≤ symEnergy (A 0) (A 1) * symEnergy (A 2) (A 3) := by
  rw [permanent_laplace]
  have h := norm_sum_mul_sq_le (symPair (A 0) (A 1))
    (fun i => symPair (A 2) (A 3) (Fin.rev i))
  rw [sym_complement_energy] at h
  simpa only [symEnergy, normSq_as_sq] using h

theorem det_sq_bound (A : Mat) :
    ‖A.det‖^2 ≤ altEnergy (A 0) (A 1) * altEnergy (A 2) (A 3) := by
  rw [det_laplace]
  have h := norm_sum_mul_sq_le (altPair (A 0) (A 1))
    (fun i => shuffleSign i * altPair (A 2) (A 3) (Fin.rev i))
  rw [alt_complement_energy] at h
  simpa only [altEnergy, normSq_as_sq] using h

#print axioms permanent_sq_bound
#print axioms det_sq_bound
end
end FourRowTradeoff
