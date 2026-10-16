import CircuitCompletion.SparseBlocks
import CircuitCompletion.RawCompiler

open scoped BigOperators
open Matrix
namespace CircuitCompletion

theorem mergeAt_coordinate_intertwine {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Fin 4 ↪ ι) (p q : Fin 4) (hpq : p≠q) (a b : ℝ) (ha : 0≤a) (hb : 0≤b) :
    (mergeAt (e p) (e q) (fun h => hpq (e.injective h)) a b ha hb : Matrix ι ι ℂ)*
        Extraction.coordinateIsometry e=
      Extraction.coordinateIsometry e*(mergeAt p q hpq a b ha hb : Matrix (Fin 4) (Fin 4) ℂ) := by
  have h := isometry_embedPlane_intertwine (Extraction.coordinateIsometry e)
    (Extraction.coordinateIsometry_isometry e) (pairPlane p q hpq)
    (pairPlane_isometry p q hpq) (mergeRotation a b ha hb)
  simpa only [mergeAt,embedPlane,coordinateIsometry_pairPlane] using h

theorem matrix_intertwine_mul {ι κ : Type*} [Fintype ι] [Fintype κ]
    (E : Matrix ι κ ℂ) (A B : Matrix ι ι ℂ) (X Y : Matrix κ κ ℂ)
    (hA : A*E=E*X) (hB : B*E=E*Y) : (A*B)*E=E*(X*Y) := by
  rw [Matrix.mul_assoc,hB,← Matrix.mul_assoc,hA,Matrix.mul_assoc]

noncomputable def fourProgram {n : ℕ} (e : Fin 4 ↪ Bits n) (a : Fin 4 → ℝ)
    (ha : ∀ i,0≤a i) : List (TwoLevel n) :=
  [TwoLevel.givens (e 0) (e 1) (fun h => (by decide : (0 : Fin 4)≠1) (e.injective h))
      (a 0) (a 1) (ha 0) (ha 1),
    TwoLevel.givens (e 0) (e 2) (fun h => (by decide : (0 : Fin 4)≠2) (e.injective h))
      (a 0+a 1) (a 2) (add_nonneg (ha 0) (ha 1)) (ha 2),
    TwoLevel.givens (e 0) (e 3) (fun h => (by decide : (0 : Fin 4)≠3) (e.injective h))
      (a 0+a 1+a 2) (a 3) (add_nonneg (add_nonneg (ha 0) (ha 1)) (ha 2)) (ha 3)]

theorem fourProgram_intertwine {n : ℕ} (e : Fin 4 ↪ Bits n) (a : Fin 4 → ℝ)
    (ha : ∀ i,0≤a i) :
    (rawDenote (fourProgram e a ha) : Matrix (Bits n) (Bits n) ℂ)*
      Extraction.coordinateIsometry e=
      Extraction.coordinateIsometry e*(compressFour a ha : Matrix (Fin 4) (Fin 4) ℂ) := by
  have h1 := mergeAt_coordinate_intertwine e 0 1 (by decide) (a 0) (a 1) (ha 0) (ha 1)
  have h2 := mergeAt_coordinate_intertwine e 0 2 (by decide) (a 0+a 1) (a 2)
    (add_nonneg (ha 0) (ha 1)) (ha 2)
  have h3 := mergeAt_coordinate_intertwine e 0 3 (by decide) (a 0+a 1+a 2) (a 3)
    (add_nonneg (add_nonneg (ha 0) (ha 1)) (ha 2)) (ha 3)
  have h12 := matrix_intertwine_mul _ _ _ _ _ h2 h1
  have h123 := matrix_intertwine_mul _ _ _ _ _ h3 h12
  simpa only [fourProgram,rawDenote,TwoLevel.denote,one_mul,compressFour,
    Matrix.UnitaryGroup.mul_val,Matrix.mul_assoc] using h123

theorem coordinateIsometry_single {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : κ ↪ ι) (j : κ) (c : ℂ) :
    Extraction.coordinateIsometry e*ᵥPi.single j c=Pi.single (e j) c := by
  ext w
  rw [Matrix.mulVec_single]
  simp [Extraction.coordinateIsometry,Pi.single_apply,eq_comm]

/-- A genuine elementary circuit compresses the actual four-point vector
in arbitrary original-register coordinates. Its spectators are untouched. -/
theorem compiled_four_compression {n : ℕ} (hn : 0<n) (e : Fin 4 ↪ Bits n)
    (a : Fin 4 → ℝ) (ha : ∀ i,0≤a i) :
    run (compileProgram hn (fourProgram e a ha))
      (Extraction.coordinateIsometry e*ᵥ(fun i => (Real.sqrt (a i) : ℂ)))=
      Pi.single (e 0) (Real.sqrt (∑ i,a i) : ℂ) := by
  simp only [run,compileProgram_denote,Matrix.mulVec_mulVec]
  rw [fourProgram_intertwine,← Matrix.mulVec_mulVec,compressFour_action,coordinateIsometry_single]

theorem compiled_four_length {n : ℕ} (hn : 0<n) (e : Fin 4 ↪ Bits n)
    (a : Fin 4 → ℝ) (ha : ∀ i,0≤a i) :
    (compileProgram hn (fourProgram e a ha)).length≤60*n^2*2^n := by
  have h := compileProgram_length hn (fourProgram e a ha)
  have hlen : (fourProgram e a ha).length=3 := rfl
  rw [hlen] at h
  nlinarith

end CircuitCompletion
