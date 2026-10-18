import SchurCompletion.JucysSpectrum

open scoped BigOperators ComplexOrder
open Matrix

namespace ExtractionSchur

open SymmetricSupport ExtractionSpectrum ExtractionRankSupport

noncomputable section

/-- The actual cycle-character eigenvalue is the product polynomial of the
 actual Jucys--Murphy joint eigenvalues. These have not yet been classified as
 integer tableau contents. -/
theorem cycleOperator_jucys_eigenvector (D k t : ℕ) (v : Word D k → ℂ)
    (c : Fin k → ℂ) (he : ∀ j, jucysOperators D k j *ᵥ v = c j • v) :
    cycleOperator D t k *ᵥ v = (∏ j : Fin k, ((t : ℂ)+c j)) • v := by
  have hf (j : Fin k) :
      ((t : ℂ) • (1 : Matrix (Word D k) (Word D k) ℂ) + jucysOperators D k j) *ᵥ v =
        ((t : ℂ)+c j) • v := by
    rw [Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,he j,add_smul]
  have hl (l : List (Fin k)) :
      (l.map (fun j => (t : ℂ) • (1 : Matrix (Word D k) (Word D k) ℂ) +
        jucysOperators D k j)).prod *ᵥ v = (l.map (fun j => (t : ℂ)+c j)).prod • v := by
    induction l with
    | nil => simp
    | cons j l ih =>
      rw [List.map_cons,List.prod_cons,← Matrix.mulVec_mulVec,ih,Matrix.mulVec_smul,hf j,
        List.map_cons,List.prod_cons,smul_smul,mul_comm]
  rw [cycleOperator_jucys_factorization]
  simpa only [List.map_ofFn,Function.comp_def,List.prod_ofFn] using hl (List.ofFn (fun j : Fin k => j))

/-- Every actual nonzero Jucys--Murphy joint vector has a nonvanishing ambient
 product denominator, deduced from genuine matrix invertibility. -/
theorem jucys_ambient_product_ne_zero (D k : ℕ) (v : Word D k → ℂ) (hv : v ≠ 0)
    (c : Fin k → ℂ) (he : ∀ j, jucysOperators D k j *ᵥ v = c j • v) :
    (∏ j : Fin k, ((D : ℂ)+c j)) ≠ 0 :=
  jointCycle_denominator_ne_zero D k v hv
    (fun t => ∏ j : Fin k, ((t : ℂ)+c j))
      (fun t => cycleOperator_jucys_eigenvector D k t v c he)

/-- The genuine rank-s Haar average has a finite product ratio on every actual
 joint spectral block. This is the complete unclassified content-product
 identity; tableau indexing, multiplicities and asymptotics remain further work. -/
theorem flatHaarAverage_jucys_product_eigenvalue (D s k : ℕ) (hsD : s ≤ D)
    (v : Word D k → ℂ) (hv : v ≠ 0) (c : Fin k → ℂ)
    (he : ∀ j, jucysOperators D k j *ᵥ v = c j • v) :
    flatHaarAverage D s k hsD *ᵥ v =
      (((s : ℂ)^k)⁻¹ * ((∏ j : Fin k, ((s : ℂ)+c j)) /
        (∏ j : Fin k, ((D : ℂ)+c j)))) • v :=
  flatHaarAverage_jointCycle_eigenvalue D s k hsD v hv
    (fun t => ∏ j : Fin k, ((t : ℂ)+c j))
      (fun t => cycleOperator_jucys_eigenvector D k t v c he)

end
end ExtractionSchur
