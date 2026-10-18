import CircuitRecursion.BalancedReference

open scoped Matrix.Norms.L2Operator
open Matrix
namespace CircuitRecursion

noncomputable def normalizedQuaternionSU2 (a b : ℂ)
    (hp : 0<Complex.normSq a+Complex.normSq b) : SU2 :=
  let r := Real.sqrt (Complex.normSq a+Complex.normSq b)
  quaternionSU2 ((r⁻¹:ℝ) • a) ((r⁻¹:ℝ) • b) (by
    have hr : r≠0 := (Real.sqrt_pos.mpr hp).ne'
    have hr2 : r*r=Complex.normSq a+Complex.normSq b := Real.mul_self_sqrt hp.le
    have he : r⁻¹*r⁻¹*(Complex.normSq a+Complex.normSq b)=1 := by
      rw [← hr2]
      field_simp
    simp only [Complex.real_smul,Complex.normSq_mul,Complex.normSq_ofReal]
    nlinarith [he])

theorem normalizedQuaternionSU2_unitary (a b : ℂ)
    (hp : 0<Complex.normSq a+Complex.normSq b) :
    su2AsUnitary (normalizedQuaternionSU2 a b hp)=normalizedQuaternion a b hp := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [normalizedQuaternionSU2,normalizedQuaternion_val,quaternionSU2,
      quaternionMatrix,su2AsUnitary,star_smul,smul_neg]

noncomputable def normalizedIntertwiner (U V : SU2) (j : Fin 4)
    (hp : 0 < intertwinerMass U V j) : SU2 :=
  normalizedQuaternionSU2 (U.val 0 0-star ((conjugacyTarget V j).val 0 0))
    (U.val 0 1+(conjugacyTarget V j).val 0 1) hp

theorem normalizedIntertwiner_coordinates (U V : SU2) (j : Fin 4)
    (hp : 0 < intertwinerMass U V j) (i : Fin 4) :
    quaternionCoordinates (normalizedIntertwiner U V j hp) i=
      (Real.sqrt (intertwinerMass U V j))⁻¹*
        (quaternionCoordinates U i-quaternionCoordinates (conjugacyTarget V j)⁻¹ i) := by
  rw [quaternionCoordinates_inverse]
  fin_cases i <;>
    simp [normalizedIntertwiner,normalizedQuaternionSU2,quaternionSU2,quaternionCoordinates,
      quaternionMatrix,intertwinerMass,Complex.real_smul,Complex.mul_re,Complex.mul_im] <;> ring

def coordinateSubOracle (f g : QuaternionOracle) (i : Fin 4) : RationalOracle :=
  oracleAdd (coordinateOracle f i) (oracleNeg (coordinateOracle g i))

theorem coordinateSubOracle_correct (f g : QuaternionOracle) (U V : SU2)
    (hf : QApproximates f U) (hg : QApproximates g V) (i : Fin 4) :
    Approximates (coordinateSubOracle f g i) (quaternionCoordinates U i-quaternionCoordinates V i) := by
  exact oracleAdd_correct _ _ _ _ (coordinateOracle_correct f U hf i)
    (oracleNeg_correct _ _ (coordinateOracle_correct g V hg i))

def intertwinerRadiusOracle (f g : QuaternionOracle) (j : Fin 4) : RationalOracle :=
  oracleSqrt (fun p => chartMassScore f g p j)

def normalizedIntertwinerOracle (f g : QuaternionOracle) (t : ℕ) (j : Fin 4) : QuaternionOracle := fun p =>
  let inverseRadius := oracleInv (t+1) (intertwinerRadiusOracle f g j)
  let adjointChart := quaternionOracleInverse (chartTargetOracle g j)
  List.Vector.ofFn (fun i => oracleMul (t+2) (coordinateSubOracle f adjointChart i) inverseRadius p)

theorem normalizedIntertwinerOracle_correct (f g : QuaternionOracle) (U V : SU2)
    (hf : QApproximates f U) (hg : QApproximates g V) (t : ℕ) (j : Fin 4)
    (hp : 0 < intertwinerMass U V j)
    (hroot : (1/2:ℝ)^(t+1)≤Real.sqrt (intertwinerMass U V j)) :
    QApproximates (normalizedIntertwinerOracle f g t j) (normalizedIntertwiner U V j hp) := by
  let r := Real.sqrt (intertwinerMass U V j)
  have hr : 0<r := Real.sqrt_pos.mpr hp
  have hrad : Approximates (intertwinerRadiusOracle f g j) r :=
    oracleSqrt_correct _ _ (fun p => chartMassScore_correct f g U V hf hg p j)
      (intertwinerMass_nonneg U V j)
  have hinv := oracleInv_correct (t+1) _ _ hrad hroot
  have hsub := fun i => coordinateSubOracle_correct f
    (quaternionOracleInverse (chartTargetOracle g j)) U (conjugacyTarget V j)⁻¹ hf
      (quaternionOracleInverse_correct _ _ (chartTargetOracle_correct g V hg j)) i
  have hlarge : (2:ℝ)≤2^(t+2) := by
    rw [pow_add]
    have ht : (1:ℝ)≤2^t := one_le_pow₀ (by norm_num)
    norm_num
    linarith
  have hinvb : |r⁻¹|≤(2:ℝ)^(t+2) := by
    have ht := one_div_le_one_div_of_le (by positivity : (0:ℝ)<(1/2)^ (t+1)) hroot
    have ht' : r⁻¹≤(2:ℝ)^(t+1) := by simpa only [one_div,inv_pow,inv_inv] using ht
    rw [abs_of_pos (inv_pos.mpr hr)]
    have hpow : (2:ℝ)^(t+1)≤2^(t+2) := by
      have heq : (2:ℝ)^(t+2)=2^(t+1)*2 := pow_succ _ _
      rw [heq]
      nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤2) (t+1)]
    exact ht'.trans hpow
  intro p i
  have hnum : |quaternionCoordinates U i-quaternionCoordinates (conjugacyTarget V j)⁻¹ i|≤(2:ℝ)^(t+2) := by
    have ht := abs_add_le (quaternionCoordinates U i) (-quaternionCoordinates (conjugacyTarget V j)⁻¹ i)
    simp only [abs_neg,← sub_eq_add_neg] at ht
    have h₁ := quaternionCoordinates_bound U i
    have h₂ := quaternionCoordinates_bound (conjugacyTarget V j)⁻¹ i
    linarith
  have he := oracleMul_correct (t+2) _ _ _ _ (hsub i) hinv hnum hinvb p
  simp only [normalizedIntertwinerOracle,List.Vector.get_ofFn,normalizedIntertwiner_coordinates]
  simpa only [mul_comm] using he

end CircuitRecursion
