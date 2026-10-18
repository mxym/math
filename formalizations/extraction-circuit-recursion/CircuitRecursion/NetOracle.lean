import CircuitRecursion.QuaternionOracles

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix
namespace CircuitRecursion

theorem quaternionMatrix_norm_square (a b : ℂ) :
    ‖quaternionMatrix a b‖^2=Complex.normSq a+Complex.normSq b := by
  have h := CStarRing.norm_star_mul_self (x := quaternionMatrix a b)
  change ‖(quaternionMatrix a b)ᴴ*quaternionMatrix a b‖=
    ‖quaternionMatrix a b‖*‖quaternionMatrix a b‖ at h
  rw [quaternionMatrix_star_mul,norm_smul,norm_one,Real.norm_eq_abs,
    abs_of_nonneg (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)),mul_one] at h
  simpa only [pow_two] using h.symm

theorem su2_sub_quaternion (U V : SU2) :
    U.val-V.val=quaternionMatrix (U.val 0 0-V.val 0 0) (U.val 0 1-V.val 0 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [quaternionMatrix,su2_lower_left,su2_lower_right] <;> ring

theorem su2_distance_coordinates (U V : SU2) :
    unitaryDistance (su2AsUnitary U) (su2AsUnitary V)^2=
      ∑ i,(quaternionCoordinates U i-quaternionCoordinates V i)^2 := by
  change ‖U.val-V.val‖^2=_
  rw [su2_sub_quaternion,quaternionMatrix_norm_square]
  simp [quaternionCoordinates,Fin.sum_univ_succ,Complex.normSq_apply,pow_two]
  ring

def rationalSquaredDistance (a b : List.Vector ℚ 4) : ℚ := ∑ i,(a.get i-b.get i)^2

theorem square_distance_error (a b x y δ : ℝ) (hδ0 : 0≤δ) (hδ1 : δ≤1)
    (hx : |x|≤1) (hy : |y|≤1) (ha : |a-x|≤δ) (hb : |b-y|≤δ) :
    |(a-b)^2-(x-y)^2|≤12*δ := by
  have haa := abs_le.mp (unit_product_error a a x x δ hδ0 hδ1 hx hx ha ha)
  have hbb := abs_le.mp (unit_product_error b b y y δ hδ0 hδ1 hy hy hb hb)
  have hab := abs_le.mp (unit_product_error a b x y δ hδ0 hδ1 hx hy ha hb)
  exact abs_le.mpr ⟨by nlinarith,by nlinarith⟩

def distanceScore (f g : QuaternionOracle) (p : ℕ) : ℚ :=
  rationalSquaredDistance (f (p+6)) (g (p+6))

theorem distanceScore_correct (f g : QuaternionOracle) (U V : SU2)
    (hf : QApproximates f U) (hg : QApproximates g V) (p : ℕ) :
    |(distanceScore f g p:ℝ)-unitaryDistance (su2AsUnitary U) (su2AsUnitary V)^2|≤(1/2:ℝ)^p := by
  rw [su2_distance_coordinates]
  simp only [distanceScore,rationalSquaredDistance,Rat.cast_sum,Rat.cast_pow,Rat.cast_sub]
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have hs : (∑ i : Fin 4,|(((f (p+6)).get i:ℝ)-((g (p+6)).get i:ℝ))^2-
      (quaternionCoordinates U i-quaternionCoordinates V i)^2|)≤∑ _i : Fin 4,12*(1/2:ℝ)^(p+6) := by
    apply Finset.sum_le_sum
    intro i hi
    exact square_distance_error _ _ _ _ _ (by positivity)
      (pow_le_one₀ (by norm_num) (by norm_num)) (quaternionCoordinates_bound U i)
      (quaternionCoordinates_bound V i) (hf _ _) (hg _ _)
  apply hs.trans
  norm_num
  rw [pow_add]
  nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤1/2) p]

/-- The online base approximation reads only the numerical entry packets
and a fixed finite table of label words. It never reads the semantic U. -/
def fixedNetWord {m n : ℕ} (entry : Fin m → QuaternionOracle)
    (table : Fin (n+1) → List (Fin m)) (target : QuaternionOracle) : List (Fin m) :=
  let scores := List.Vector.ofFn (fun j => distanceScore target (quaternionWordOracle entry (table j)) 20)
  table (rationalMinIndex n scores.get)

theorem fixedNetWord_correct {m n : ℕ} (entry : Fin m → QuaternionOracle)
    (G : Fin m → SU2) (he : ∀ i,QApproximates (entry i) (G i))
    (table : Fin (n+1) → List (Fin m))
    (hcover : ∀ U : SU2,∃ j,unitaryDistance (su2AsUnitary U)
      (su2AsUnitary (instructionWordValue G (table j)))≤1/576)
    (target : QuaternionOracle) (U : SU2) (htarget : QApproximates target U) :
    unitaryDistance (su2AsUnitary U)
      (su2AsUnitary (instructionWordValue G (fixedNetWord entry table target)))≤1/288 := by
  let score := fun j => distanceScore target (quaternionWordOracle entry (table j)) 20
  let actual := fun j => unitaryDistance (su2AsUnitary U)
    (su2AsUnitary (instructionWordValue G (table j)))^2
  have herr : ∀ j,|(score j:ℝ)-actual j|≤(1/2:ℝ)^20 := by
    intro j
    exact distanceScore_correct _ _ _ _ htarget (quaternionWordOracle_correct entry G he _) 20
  obtain ⟨i,hi⟩ := hcover U
  have hmin := rationalMinIndex_error n score actual ((1/2:ℝ)^20) herr i
  have hi0 := unitaryDistance_nonneg (su2AsUnitary U)
    (su2AsUnitary (instructionWordValue G (table i)))
  have hsel0 := unitaryDistance_nonneg (su2AsUnitary U)
    (su2AsUnitary (instructionWordValue G (table (rationalMinIndex n score))))
  have hget : (List.Vector.ofFn score).get=score := by
    funext j
    exact List.Vector.get_ofFn score j
  simp only [fixedNetWord]
  change unitaryDistance (su2AsUnitary U)
    (su2AsUnitary (instructionWordValue G (table (rationalMinIndex n (List.Vector.ofFn score).get))))≤_
  rw [hget]
  dsimp only [actual] at hmin
  norm_num at hmin
  nlinarith

theorem fixedNetWord_length {m n : ℕ} (entry : Fin m → QuaternionOracle)
    (table : Fin (n+1) → List (Fin m)) (L : ℕ) (hL : ∀ j,(table j).length≤L)
    (target : QuaternionOracle) : (fixedNetWord entry table target).length≤L := by
  exact hL _

end CircuitRecursion
