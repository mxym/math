import CircuitRecursion.BalancedCommutator

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix
namespace CircuitRecursion

abbrev SU2 := Matrix.specialUnitaryGroup (Fin 2) ℂ

theorem su2AsUnitary_mul (A B : SU2) :
    su2AsUnitary (A*B)=su2AsUnitary A*su2AsUnitary B := rfl

theorem su2AsUnitary_inv (A : SU2) :
    su2AsUnitary A⁻¹=(su2AsUnitary A)⁻¹ := rfl

noncomputable def balancedFactors (U : SU2) : SU2×SU2 :=
  let A := Classical.choose (su2_balanced_commutator U)
  let B := Classical.choose (Classical.choose_spec (su2_balanced_commutator U))
  (A,B)

theorem balancedFactors_spec (U : SU2) :
    U=su2Commutator (balancedFactors U).1 (balancedFactors U).2 ∧
      unitaryDistance (su2AsUnitary (balancedFactors U).1) 1≤Real.sqrt (unitaryDistance (su2AsUnitary U) 1) ∧
      unitaryDistance (su2AsUnitary (balancedFactors U).2) 1≤Real.sqrt (unitaryDistance (su2AsUnitary U) 1) :=
  Classical.choose_spec (Classical.choose_spec (su2_balanced_commutator U))

def instructionInverse {m : ℕ} (inverseLabel : Fin m → Fin m) (w : List (Fin m)) : List (Fin m) :=
  w.reverse.map inverseLabel

/-- A genuine SK correction word, in chronological circuit order. -/
noncomputable def skCorrection {m : ℕ} (G : Fin m → SU2) (inverseLabel : Fin m → Fin m)
    (approx : SU2 → List (Fin m)) (U : SU2) : List (Fin m) :=
  let u := approx U
  let factors := balancedFactors (U*(instructionWordValue G u)⁻¹)
  let a := approx factors.1
  let b := approx factors.2
  u++instructionInverse inverseLabel b++instructionInverse inverseLabel a++b++a

theorem skCorrection_value {m : ℕ} (G : Fin m → SU2) (inverseLabel : Fin m → Fin m)
    (hi : ∀ i,G (inverseLabel i)=(G i)⁻¹) (approx : SU2 → List (Fin m)) (U : SU2) :
    instructionWordValue G (skCorrection G inverseLabel approx U)=
      su2Commutator (instructionWordValue G (approx (balancedFactors
        (U*(instructionWordValue G (approx U))⁻¹)).1))
        (instructionWordValue G (approx (balancedFactors
          (U*(instructionWordValue G (approx U))⁻¹)).2))*instructionWordValue G (approx U) := by
  simp only [skCorrection,instructionWordValue_append,instructionInverse,
    instructionWordValue_inverse G inverseLabel hi,su2Commutator,mul_assoc]

theorem skCorrection_length {m : ℕ} (G : Fin m → SU2) (inverseLabel : Fin m → Fin m)
    (approx : SU2 → List (Fin m)) (L : ℕ) (hL : ∀ U,(approx U).length≤L) (U : SU2) :
    (skCorrection G inverseLabel approx U).length≤5*L := by
  simp only [skCorrection,List.length_append,instructionInverse,List.length_map,List.length_reverse]
  have hu := hL U
  have ha := hL (balancedFactors (U*(instructionWordValue G (approx U))⁻¹)).1
  have hb := hL (balancedFactors (U*(instructionWordValue G (approx U))⁻¹)).2
  omega

theorem skCorrection_error {m : ℕ} (G : Fin m → SU2) (inverseLabel : Fin m → Fin m)
    (hi : ∀ i,G (inverseLabel i)=(G i)⁻¹) (approx : SU2 → List (Fin m))
    (ε : ℝ) (hε : 0≤ε) (hε1 : ε≤1)
    (heach : ∀ U,unitaryDistance (su2AsUnitary U)
      (su2AsUnitary (instructionWordValue G (approx U)))≤ε) (U : SU2) :
    unitaryDistance (su2AsUnitary U)
      (su2AsUnitary (instructionWordValue G (skCorrection G inverseLabel approx U)))≤
        6*ε*Real.sqrt ε := by
  let u := instructionWordValue G (approx U)
  let R := U*u⁻¹
  let A := (balancedFactors R).1
  let B := (balancedFactors R).2
  let A' := instructionWordValue G (approx A)
  let B' := instructionWordValue G (approx B)
  have hRu : unitaryDistance (su2AsUnitary R) 1=
      unitaryDistance (su2AsUnitary U) (su2AsUnitary u) := by
    have hu : su2AsUnitary u*(su2AsUnitary u)⁻¹=1 := mul_inv_cancel _
    rw [← hu,su2AsUnitary_mul,su2AsUnitary_inv,unitaryDistance_mul_right]
  have hR : unitaryDistance (su2AsUnitary R) 1≤ε := by rw [hRu]; exact heach U
  have hs := balancedFactors_spec R
  have hA : unitaryDistance (su2AsUnitary A) 1≤Real.sqrt ε := hs.2.1.trans (Real.sqrt_le_sqrt hR)
  have hB : unitaryDistance (su2AsUnitary B) 1≤Real.sqrt ε := hs.2.2.trans (Real.sqrt_le_sqrt hR)
  have herr := unitaryCommutator_error (su2AsUnitary A) (su2AsUnitary B)
    (su2AsUnitary A') (su2AsUnitary B') (Real.sqrt ε) ε (Real.sqrt_nonneg _) hε
      hA hB (heach A) (heach B)
  have hval : instructionWordValue G (skCorrection G inverseLabel approx U)=su2Commutator A' B'*u :=
    skCorrection_value G inverseLabel hi approx U
  rw [hval,su2AsUnitary_mul]
  have hU : U=R*u := by dsimp [R]; simp
  rw [hU,su2AsUnitary_mul,unitaryDistance_mul_right]
  rw [hs.1,su2Commutator_unitary,su2Commutator_unitary]
  apply herr.trans
  have hroot : ε≤Real.sqrt ε := by
    have ht := Real.sq_sqrt hε
    have hp := Real.sqrt_nonneg ε
    nlinarith
  nlinarith [mul_nonneg hε (sub_nonneg.mpr hroot)]

/-- Two actual corrections square a small error with a conservative fixed
constant, while increasing the actual instruction-word length by at most 25. -/
theorem skDoubleCorrection_error {m : ℕ} (G : Fin m → SU2) (inverseLabel : Fin m → Fin m)
    (hi : ∀ i,G (inverseLabel i)=(G i)⁻¹) (approx : SU2 → List (Fin m))
    (ε : ℝ) (hε : 0≤ε) (hεsmall : ε≤1/288)
    (heach : ∀ U,unitaryDistance (su2AsUnitary U)
      (su2AsUnitary (instructionWordValue G (approx U)))≤ε) (U : SU2) :
    unitaryDistance (su2AsUnitary U)
      (su2AsUnitary (instructionWordValue G
        (skCorrection G inverseLabel (skCorrection G inverseLabel approx) U)))≤144*ε^2 := by
  have hε1 : ε≤1 := by linarith
  have hs : Real.sqrt ε≤1 := by nlinarith [Real.sq_sqrt hε,Real.sqrt_nonneg ε]
  let η := 6*ε*Real.sqrt ε
  have hη0 : 0≤η := by dsimp [η]; positivity
  have hη : η≤6*ε := by dsimp [η]; nlinarith [Real.sqrt_nonneg ε]
  have hη1 : η≤1 := by linarith
  have ht := skCorrection_error G inverseLabel hi (skCorrection G inverseLabel approx)
    η hη0 hη1 (skCorrection_error G inverseLabel hi approx ε hε hε1 heach) U
  apply ht.trans
  have hroot : Real.sqrt η≤4*Real.sqrt ε := by
    have he := Real.sq_sqrt hε
    have hh := Real.sq_sqrt hη0
    have h0 := Real.sqrt_nonneg ε
    have h1 := Real.sqrt_nonneg η
    nlinarith
  calc
    6*η*Real.sqrt η≤6*(6*ε*Real.sqrt ε)*(4*Real.sqrt ε) := by gcongr
    _ = 144*ε*(Real.sqrt ε)^2 := by ring
    _ = 144*ε^2 := by rw [Real.sq_sqrt hε]; ring

end CircuitRecursion
