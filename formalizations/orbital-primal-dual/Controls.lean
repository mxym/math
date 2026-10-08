import UniversalOrbitalTheorem

open scoped BigOperators

namespace OrbitalMarginals

/-- With no features on two atoms, the actual sharp coefficient is one. -/
theorem empty_features_nonvacuous :
    sharpConstant (fun _ : Empty => fun _ : Fin 2 => (0 : ℝ)) (0 : Fin 2) = 1 := by
  let p : Fin 2 → ℝ := fun g => if g = 0 then 1 else 0
  let q : Fin 2 → ℝ := fun g => if g = 1 then 1 else 0
  have hp : Probability p := by
    constructor
    · intro g
      dsimp [p]
      split_ifs <;> norm_num
    · norm_num [p, Fin.sum_univ_two]
  have hq : Probability q := by
    constructor
    · intro g
      dsimp [q]
      split_ifs <;> norm_num
    · norm_num [q, Fin.sum_univ_two]
  have hm : Match (fun _ : Empty => fun _ : Fin 2 => (0 : ℝ)) p q := by
    intro j
    cases j
  have hb : PairBound (fun _ : Empty => fun _ : Fin 2 => (0 : ℝ)) (0 : Fin 2) 1 := by
    intro P Q hP hQ _
    have he := hP.2
    rw [Fin.sum_univ_two] at he
    linarith [hP.1 1, hQ.1 0]
  have ho : p 0 - q 0 = 1 := by norm_num [p, q]
  have hb' : PairBound (fun _ : Empty => fun _ : Fin 2 => (0 : ℝ)) (0 : Fin 2) (p 0 - q 0) := by
    rwa [ho]
  exact (sharpConstant_eq_optimum _ _ p q hp hq hm hb').trans ho

/-- A one-atom zero-mass kernel is trivial, giving the actual zero endpoint. -/
theorem one_atom_zero_endpoint :
    sharpConstant (fun _ : Empty => fun _ : Unit => (0 : ℝ)) () = 0 := by
  apply sharpConstant_trivial_kernel
  intro v hv
  funext g
  cases g
  simpa using hv.1

/-- Concrete omitted-hypothesis counterexample: positive mass differs from TV.
Jordan normalization cannot be used without zero total signed mass. -/
theorem jordan_requires_zero_mass :
    TV (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0) = 1 / 2 ∧
      (∑ i : Fin 2, jordanP (fun j : Fin 2 => if j = 0 then (1 : ℝ) else 0) i) = 2 := by
  norm_num [TV, jordanP, posPart, Fin.sum_univ_two]

end OrbitalMarginals
