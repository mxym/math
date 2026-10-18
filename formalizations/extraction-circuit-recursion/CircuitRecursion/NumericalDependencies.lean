import CircuitRecursion.FactorDependencies

namespace CircuitRecursion

theorem quaternionWordOracle_agrees {m : ℕ} (entry entry' : Fin m → QuaternionOracle)
    (w : List (Fin m)) (P : ℕ)
    (he : ∀ i,AgreesThrough (entry i) (entry' i) (P+4*w.length)) :
    AgreesThrough (quaternionWordOracle entry w) (quaternionWordOracle entry' w) P := by
  induction w generalizing P with
  | nil => exact AgreesThrough.refl _ _
  | cons i w ih =>
    apply quaternionOracleMul_agrees
    · exact ih (P+4) (fun j => (he j).mono (by simp only [List.length_cons]; omega))
    · exact (he i).mono (by simp only [List.length_cons]; omega)

theorem fixedNetWord_agrees {m n : ℕ} (entry entry' : Fin m → QuaternionOracle)
    (table : Fin (n+1) → List (Fin m)) (L : ℕ) (hL : ∀ j,(table j).length≤L)
    (he : ∀ i,AgreesThrough (entry i) (entry' i) (26+4*L))
    (f f' : QuaternionOracle) (hf : AgreesThrough f f' (26+4*L)) :
    fixedNetWord entry table f=fixedNetWord entry' table f' := by
  have hs : (fun j => distanceScore f (quaternionWordOracle entry (table j)) 20)=
      (fun j => distanceScore f' (quaternionWordOracle entry' (table j)) 20) := by
    funext j
    exact distanceScore_agrees _ _ _ _ 20 (hf.mono (by omega))
      (quaternionWordOracle_agrees entry entry' (table j) 26
        (fun i => (he i).mono (by have h := hL j; omega))) 20 (le_refl _)
  simp only [fixedNetWord,hs]

theorem residualSmall_agrees (f f' : QuaternionOracle) (t : ℕ)
    (hf : AgreesThrough f f' (2*t+8)) : residualSmall f t=residualSmall f' t := by
  have hs := distanceScore_agrees f f' quaternionOracleOne quaternionOracleOne (2*t+2)
    (hf.mono (by omega)) (AgreesThrough.refl _ _) (2*t+2) (le_refl _)
  simp only [residualSmall,hs]

def correctionDemand (M L t : ℕ) : ℕ := 16*M+48*t+578+4*L

theorem correctionDemand_ge (M L t : ℕ) : M≤correctionDemand M L t := by
  unfold correctionDemand
  omega

/-- A bound on all input precision dependencies of one actual correction,
including the rational stopping decision and both factor-oracle branches. -/
theorem numericalCorrection_agrees {m : ℕ} (entry entry' : Fin m → QuaternionOracle)
    (inverseLabel : Fin m → Fin m) (approx approx' : QuaternionOracle → List (Fin m))
    (M L t : ℕ) (hL : ∀ f,(approx f).length≤L)
    (happrox : ∀ f f',AgreesThrough f f' M → approx f=approx' f')
    (he : ∀ i,AgreesThrough (entry i) (entry' i) (correctionDemand M L t))
    (f f' : QuaternionOracle) (hf : AgreesThrough f f' (correctionDemand M L t)) :
    numericalCorrection entry inverseLabel approx t f=
      numericalCorrection entry' inverseLabel approx' t f' := by
  have hu := happrox f f' (hf.mono (correctionDemand_ge M L t))
  let uw := approx f
  let r := quaternionOracleMul f (quaternionOracleInverse (quaternionWordOracle entry uw))
  let r' := quaternionOracleMul f' (quaternionOracleInverse (quaternionWordOracle entry' uw))
  let D := 16*M+48*t+570
  have hlen : uw.length≤L := hL f
  have hr : AgreesThrough r r' D := by
    apply quaternionOracleMul_agrees
    · exact hf.mono (by dsimp [D,correctionDemand]; omega)
    · apply quaternionOracleInverse_agrees
      exact quaternionWordOracle_agrees entry entry' uw (D+4)
        (fun i => (he i).mono (by dsimp [D,correctionDemand]; omega))
  have hsmall := residualSmall_agrees r r' t (hr.mono (by dsimp [D]; omega))
  have ha := happrox (conditionedFactorXOracle r t) (conditionedFactorXOracle r' t)
    (conditionedFactorXOracle_agrees r r' t M hr)
  have hb := happrox (conditionedFactorYOracle r t) (conditionedFactorYOracle r' t)
    (conditionedFactorYOracle_agrees r r' t M hr)
  simp only [numericalCorrection,← hu]
  change (if residualSmall r t=true then uw else
    uw++instructionInverse inverseLabel (approx (conditionedFactorYOracle r t))++
      instructionInverse inverseLabel (approx (conditionedFactorXOracle r t))++
      approx (conditionedFactorYOracle r t)++approx (conditionedFactorXOracle r t))=
    (if residualSmall r' t=true then uw else
    uw++instructionInverse inverseLabel (approx' (conditionedFactorYOracle r' t))++
      instructionInverse inverseLabel (approx' (conditionedFactorXOracle r' t))++
      approx' (conditionedFactorYOracle r' t)++approx' (conditionedFactorXOracle r' t))
  rw [hsmall,ha,hb]

def numericalDemand (L : ℕ) : ℕ → ℕ
  | 0 => 26+4*L
  | k+1 => correctionDemand
      (correctionDemand (numericalDemand L k) (L*25^k) (numericalThreshold k))
      (5*(L*25^k)) (numericalThreshold k)

theorem numericalDemand_ge (L k : ℕ) : numericalDemand L k≤numericalDemand L (k+1) :=
  (correctionDemand_ge _ _ _).trans (correctionDemand_ge _ _ _)

theorem numericalPairWord_agrees {m n : ℕ} (entry entry' : Fin m → QuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L : ℕ) (hL : ∀ j,(table j).length≤L) (k : ℕ)
    (he : ∀ i,AgreesThrough (entry i) (entry' i) (numericalDemand L k))
    (f f' : QuaternionOracle) (hf : AgreesThrough f f' (numericalDemand L k)) :
    numericalPairWord entry inverseLabel table k f=numericalPairWord entry' inverseLabel table k f' := by
  induction k generalizing f f' with
  | zero => exact fixedNetWord_agrees entry entry' table L hL he f f' hf
  | succ k ih =>
    let M := numericalDemand L k
    let B := L*25^k
    let t := numericalThreshold k
    let M' := correctionDemand M B t
    have hle : M'≤numericalDemand L (k+1) := correctionDemand_ge _ _ _
    have he' : ∀ i,AgreesThrough (entry i) (entry' i) M' := fun i => (he i).mono hle
    have hlen : ∀ g,(numericalPairWord entry inverseLabel table k g).length≤B :=
      numericalPairWord_length entry inverseLabel table L hL k
    have hinner : ∀ g g',AgreesThrough g g' M' →
        numericalCorrection entry inverseLabel (numericalPairWord entry inverseLabel table k) t g=
        numericalCorrection entry' inverseLabel (numericalPairWord entry' inverseLabel table k) t g' := by
      intro g g' hg
      exact numericalCorrection_agrees entry entry' inverseLabel _ _ M B t hlen
        (fun a a' ha => ih (fun i => (he' i).mono (correctionDemand_ge M B t)) a a' ha)
        he' g g' hg
    exact numericalCorrection_agrees entry entry' inverseLabel _ _ M' (5*B) t
      (numericalCorrection_length entry inverseLabel _ B t hlen) hinner he f f' hf

theorem numericalDemand_succ (L k : ℕ) :
    numericalDemand L (k+1)=256*numericalDemand L k+816*numericalThreshold k+9826+84*(L*25^k) := by
  rw [numericalDemand]
  unfold correctionDemand
  ring

theorem numericalDemand_bound (L k : ℕ) : numericalDemand L k≤100000*(L+1)*512^k := by
  induction k with
  | zero => simp only [numericalDemand,pow_zero,mul_one]; omega
  | succ k ih =>
    have h2 : 2^k≤512^k := Nat.pow_le_pow_left (by norm_num) _
    have h25 : 25^k≤512^k := Nat.pow_le_pow_left (by norm_num) _
    have h1 : 1≤512^k := Nat.one_le_pow _ _ (by norm_num)
    have hL25 := Nat.mul_le_mul_left L h25
    rw [numericalDemand_succ]
    unfold numericalThreshold
    rw [Nat.pow_succ]
    nlinarith

theorem numericalDemand_precision_bound (L p : ℕ) :
    numericalDemand L (Nat.clog 2 (p+1))≤51200000*(L+1)*(p+1)^9 := by
  have ht := numericalDemand_bound L (Nat.clog 2 (p+1))
  have hp := pow_clog_two_le (p+1) (by omega)
  have hpow : 512^Nat.clog 2 (p+1)≤512*(p+1)^9 := by
    calc
      _=(2^Nat.clog 2 (p+1))^9 := by
        change (2^9)^Nat.clog 2 (p+1)=_
        rw [← Nat.pow_mul,← Nat.pow_mul,Nat.mul_comm]
      _≤(2*(p+1))^9 := Nat.pow_le_pow_left hp _
      _=_ := by ring
  exact ht.trans (by nlinarith [Nat.mul_le_mul_left (100000*(L+1)) hpow])

end CircuitRecursion
