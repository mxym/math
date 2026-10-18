import CircuitRecursion.SKCorrection

open scoped Matrix.Norms.L2Operator
open Matrix
namespace CircuitRecursion

noncomputable def skPairError (n : ℕ) : ℝ := (1/144)*(1/2)^(2^n)

theorem skPairError_zero : skPairError 0=1/288 := by norm_num [skPairError]

theorem skPairError_nonneg (n : ℕ) : 0≤skPairError n := by unfold skPairError; positivity

theorem skPairError_succ (n : ℕ) : skPairError (n+1)=144*(skPairError n)^2 := by
  simp only [skPairError,Nat.pow_succ,pow_mul]
  ring

theorem skPairError_small (n : ℕ) : skPairError n≤1/288 := by
  induction n with
  | zero => rw [skPairError_zero]
  | succ n ih =>
    rw [skPairError_succ]
    nlinarith [mul_nonneg (skPairError_nonneg n) (sub_nonneg.mpr ih)]

theorem skPairError_precision (n p : ℕ) (hp : p≤2^n) : skPairError n≤(1/2 : ℝ)^p := by
  obtain ⟨r,hr⟩ := Nat.exists_eq_add_of_le hp
  have hpow : (1/2 : ℝ)^r≤1 := pow_le_one₀ (by norm_num) (by norm_num)
  unfold skPairError
  rw [hr,pow_add]
  have hnonneg : 0≤(1/2 : ℝ)^p := by positivity
  nlinarith

noncomputable def skPairWord {m : ℕ} (G : Fin m → SU2) (inverseLabel : Fin m → Fin m)
    (base : SU2 → List (Fin m)) : ℕ → SU2 → List (Fin m)
  | 0 => base
  | n+1 => skCorrection G inverseLabel (skCorrection G inverseLabel (skPairWord G inverseLabel base n))

theorem skPairWord_error {m : ℕ} (G : Fin m → SU2) (inverseLabel : Fin m → Fin m)
    (hi : ∀ i,G (inverseLabel i)=(G i)⁻¹) (base : SU2 → List (Fin m))
    (hb : ∀ U,unitaryDistance (su2AsUnitary U)
      (su2AsUnitary (instructionWordValue G (base U)))≤1/288) (n : ℕ) (U : SU2) :
    unitaryDistance (su2AsUnitary U)
      (su2AsUnitary (instructionWordValue G (skPairWord G inverseLabel base n U)))≤skPairError n := by
  induction n generalizing U with
  | zero => simpa only [skPairWord,skPairError_zero] using hb U
  | succ n ih =>
    rw [skPairWord,skPairError_succ]
    exact skDoubleCorrection_error G inverseLabel hi _ (skPairError n)
      (skPairError_nonneg n) (skPairError_small n) ih U

theorem skPairWord_length {m : ℕ} (G : Fin m → SU2) (inverseLabel : Fin m → Fin m)
    (base : SU2 → List (Fin m)) (L : ℕ) (hb : ∀ U,(base U).length≤L) (n : ℕ) (U : SU2) :
    (skPairWord G inverseLabel base n U).length≤L*25^n := by
  induction n generalizing U with
  | zero => simpa only [skPairWord,pow_zero,mul_one] using hb U
  | succ n ih =>
    have hf := skCorrection_length G inverseLabel (skPairWord G inverseLabel base n) (L*25^n) ih
    have ht := skCorrection_length G inverseLabel
      (skCorrection G inverseLabel (skPairWord G inverseLabel base n)) (5*(L*25^n)) hf U
    calc
      _ ≤ 5*(5*(L*25^n)) := ht
      _ = L*25^(n+1) := by rw [pow_succ]; ring

theorem pow_clog_two_le (r : ℕ) (hr : 0<r) : 2^Nat.clog 2 r≤2*r := by
  by_cases h : r≤1
  · have he : r=1 := by omega
    simp [he]
  · have hpos : 1<r := by omega
    have hc : 0<Nat.clog 2 r := Nat.clog_pos (by decide) hpos
    have hp := Nat.pow_pred_clog_lt_self (by decide : 1<2) hpos
    have he : Nat.clog 2 r=(Nat.clog 2 r-1)+1 := by omega
    rw [Nat.pred_eq_sub_one] at hp
    rw [he,Nat.pow_succ]
    nlinarith

theorem precisionDepth_length (p : ℕ) : 25^Nat.clog 2 (p+1)≤32*(p+1)^5 := by
  have hp := pow_clog_two_le (p+1) (by omega)
  calc
    25^Nat.clog 2 (p+1)≤(2^5)^Nat.clog 2 (p+1) := Nat.pow_le_pow_left (by norm_num) _
    _ = (2^Nat.clog 2 (p+1))^5 := by
      rw [← Nat.pow_mul,← Nat.pow_mul,Nat.mul_comm]
    _ ≤ (2*(p+1))^5 := Nat.pow_le_pow_left hp _
    _ = _ := by ring

/-- Full finite-library SU(2) synthesis existence, with a literal word and
polynomial precision cost. Its net and balanced commutators are proved
internally; only inverse-closed universality of the fixed finite library is
assumed. Effective finite-precision classical running time is separate. -/
theorem su2_synthesis_dyadic {m : ℕ} (G : Fin m → SU2)
    (hinv : ∀ i,∃ j,G j=(G i)⁻¹)
    (huniversal : Dense (Subgroup.closure (Set.range G) : Set SU2)) :
    ∃ C : ℕ,∀ (p : ℕ) (U : SU2),∃ w : List (Fin m),
      w.length≤C*(p+1)^5 ∧
      ‖U.val-(instructionWordValue G w).val‖≤(1/2 : ℝ)^p := by
  classical
  obtain ⟨L,hL⟩ := su2_uniform_instructionLength G hinv huniversal (1/288) (by norm_num)
  let base (U : SU2) := Classical.choose (hL U)
  have hbaseL : ∀ U,(base U).length≤L := fun U => (Classical.choose_spec (hL U)).1
  have hbaseE : ∀ U,unitaryDistance (su2AsUnitary U)
      (su2AsUnitary (instructionWordValue G (base U)))≤1/288 :=
    fun U => (Classical.choose_spec (hL U)).2.le
  let inverseLabel (i : Fin m) := Classical.choose (hinv i)
  have hi : ∀ i,G (inverseLabel i)=(G i)⁻¹ := fun i => Classical.choose_spec (hinv i)
  refine ⟨32*L,fun p U => ?_⟩
  let n := Nat.clog 2 (p+1)
  let w := skPairWord G inverseLabel base n U
  refine ⟨w,?_,?_⟩
  · have ht := skPairWord_length G inverseLabel base L hbaseL n U
    have hp := Nat.mul_le_mul_left L (precisionDepth_length p)
    exact ht.trans (by simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using hp)
  · have ht := skPairWord_error G inverseLabel hi base hbaseE n U
    have hp : p≤2^n := (Nat.le_succ p).trans (Nat.le_pow_clog (by decide) (p+1))
    exact ht.trans (skPairError_precision n p hp)

end CircuitRecursion
