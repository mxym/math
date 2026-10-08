import Entry005.TruncationFacetFormula
import Mathlib.Data.Fintype.CardEmbedding

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Entry005

def truncationCoordinateVector (d : ℕ) (i : Fin d) : Fin d → ℝ :=
  fun j => if i = j then 1 else 0

def truncationRowDeterminant (d : ℕ) :
    (Fin d → ℝ) [⋀^Fin d]→ₗ[ℝ] ℝ := Matrix.detRowAlternating

theorem truncation_row_determinant_horizontal {d : ℕ}
    (v : Fin d → Fin d → ℝ) :
    truncationRowDeterminant d v = horizontalDeterminant v := by
  exact (Matrix.det_transpose (Matrix.of v)).symm

theorem truncation_coordinate_embedding_abs_det (d : ℕ) (τ : Fin d ↪ Fin d) :
    |truncationRowDeterminant d (fun i => truncationCoordinateVector d (τ i))| = 1 := by
  classical
  let e : Fin d ≃ Fin d := Equiv.ofBijective τ
    ⟨τ.injective, Finite.surjective_of_injective τ.injective⟩
  have he : (Matrix.of (fun i => truncationCoordinateVector d (τ i))) =
      (1 : Matrix (Fin d) (Fin d) ℝ).submatrix e (Equiv.refl (Fin d)) := by
    ext i j
    change (if τ i = j then 1 else 0) = (if τ i = j then 1 else 0)
    rfl
  have hh := Matrix.abs_det_submatrix_equiv_equiv e (Equiv.refl (Fin d))
    (1 : Matrix (Fin d) (Fin d) ℝ)
  rw [← he] at hh
  exact hh.trans (by simp)

theorem truncation_ones_embedding_abs_det (d : ℕ) (τ : Fin d ↪ Fin (d + 1)) :
    |truncationRowDeterminant (d + 1)
      (Fin.cons (fun _ => 1) (fun i => truncationCoordinateVector (d + 1) (τ i)))| = 1 := by
  classical
  have hn : ¬Function.Surjective τ := by
    intro h
    have hh := Fintype.card_le_of_surjective τ h
    simp only [Fintype.card_fin] at hh
    omega
  change ¬ ∀ y, ∃ x, τ x = y at hn
  push Not at hn
  obtain ⟨k, hk⟩ := hn
  let σ : Fin (d + 1) ↪ Fin (d + 1) :=
    ⟨Fin.cons k τ, Fin.cons_injective_iff.mpr ⟨by rintro ⟨i, hi⟩; exact hk i hi,
      τ.injective⟩⟩
  have hsum : (∑ j, truncationCoordinateVector (d + 1) (σ j)) = fun _ => 1 := by
    have hs : Function.Surjective σ := Finite.surjective_of_injective σ.injective
    let e : Fin (d + 1) ≃ Fin (d + 1) := Equiv.ofBijective σ ⟨σ.injective, hs⟩
    have he : (∑ j, truncationCoordinateVector (d + 1) (σ j)) =
        ∑ j, truncationCoordinateVector (d + 1) j :=
      e.sum_comp (truncationCoordinateVector (d + 1))
    rw [he]
    ext i
    simp [truncationCoordinateVector]
  let A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
    Matrix.of (fun j => truncationCoordinateVector (d + 1) (σ j))
  have hupdate : A.updateRow 0 (fun _ => 1) =
      Matrix.of (Fin.cons (fun _ => 1)
        (fun i => truncationCoordinateVector (d + 1) (τ i))) := by
    ext i j
    induction i using Fin.cases with
    | zero => simp [Matrix.updateRow, Function.update]
    | succ i => simp [Matrix.updateRow, Function.update, A, σ]
  have hdet : (A.updateRow 0 (fun _ => 1)).det = A.det := by
    have hh := Matrix.det_updateRow_sum A 0 (fun _ => (1 : ℝ))
    simp only [one_smul] at hh
    change (A.updateRow 0 (∑ j, truncationCoordinateVector (d + 1) (σ j))).det = A.det at hh
    rw [hsum] at hh
    exact hh
  calc
    |truncationRowDeterminant (d + 1) _| = |(A.updateRow 0 (fun _ => 1)).det| :=
      congrArg (fun B : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ => |B.det|) hupdate.symm
    _ = |A.det| := congrArg abs hdet
    _ = 1 := truncation_coordinate_embedding_abs_det (d + 1) σ

def truncationBindFirst {n k : ℕ}
    (f : (Fin n → ℝ) [⋀^Fin (k + 1)]→ₗ[ℝ] ℝ) (v : Fin n → ℝ) :
    (Fin n → ℝ) [⋀^Fin k]→ₗ[ℝ] ℝ :=
  { f.toMultilinearMap.curryLeft v with
    map_eq_zero_of_eq' w i j h hij :=
      f.map_eq_zero_of_eq _ (by simpa using h) ((Fin.succ_injective _).ne hij) }

theorem truncation_two_special_injection_sum {n k m : ℕ}
    (f : (Fin n → ℝ) [⋀^Fin (k + 2)]→ₗ[ℝ] ℝ)
    (v w : Fin n → ℝ) (g : Fin m → Fin n → ℝ) :
    (∑ σ : Fin (k + 2) ↪ Fin (m + 2),
      |f (fun i => (Fin.cons v (Fin.cons w g) : Fin (m + 2) → Fin n → ℝ) (σ i))|) =
      (∑ σ : Fin (k + 2) ↪ Fin m, |f (fun i => g (σ i))|) +
      (k + 2 : ℝ) * (∑ τ : Fin (k + 1) ↪ Fin m,
        |f (Fin.cons w (fun i => g (τ i)))|) +
      (k + 2 : ℝ) * (∑ τ : Fin (k + 1) ↪ Fin m,
        |f (Fin.cons v (fun i => g (τ i)))|) +
      (k + 2 : ℝ) * (k + 1 : ℝ) * (∑ τ : Fin k ↪ Fin m,
        |f (Fin.cons v (Fin.cons w (fun i => g (τ i))))|) := by
  have h1 := alternating_injection_sum_cons (k + 1) (m + 1) f v (Fin.cons w g)
  have h2 := alternating_injection_sum_cons (k + 1) m f w g
  have h3 := alternating_injection_sum_cons k m (truncationBindFirst f v) w g
  change (∑ σ : Fin (k + 1) ↪ Fin (m + 1),
    |f (Fin.cons v (fun i => (Fin.cons w g : Fin (m + 1) → Fin n → ℝ) (σ i)))|) =
    (∑ σ : Fin (k + 1) ↪ Fin m, |f (Fin.cons v (fun i => g (σ i)))|) +
    (k + 1 : ℝ) * (∑ τ : Fin k ↪ Fin m,
      |f (Fin.cons v (Fin.cons w (fun i => g (τ i))))|) at h3
  rw [h1, h2, h3]
  simp only [Nat.cast_add, Nat.cast_one]
  ring

theorem truncation_embedding_card_predecessor (d : ℕ) :
    Fintype.card (Fin d ↪ Fin (d + 1)) = (d + 1).factorial := by
  rw [Fintype.card_embedding_eq]
  simp only [Fintype.card_fin]
  have hh := Nat.factorial_mul_descFactorial (n := d + 1) (k := d) (by omega)
  have hs : d + 1 - d = 1 := by omega
  simpa only [hs, Nat.factorial_one, one_mul] using hh

theorem truncation_scaled_coordinate_embedding_abs_det (d : ℕ) (r : ℝ)
    (hr : 0 ≤ r) (τ : Fin d ↪ Fin d) :
    |truncationRowDeterminant d
      (fun i => (-r) • truncationCoordinateVector d (τ i))| = r ^ d := by
  rw [(truncationRowDeterminant d).map_smul_univ]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    abs_mul, abs_pow, abs_neg, abs_of_nonneg hr,
    truncation_coordinate_embedding_abs_det, mul_one]

theorem truncation_scaled_ones_embedding_abs_det (d : ℕ) (a r : ℝ)
    (hr : 0 ≤ r) (τ : Fin d ↪ Fin (d + 1)) :
    |truncationRowDeterminant (d + 1)
      (Fin.cons (fun _ => a) (fun i => (-r) • truncationCoordinateVector (d + 1) (τ i)))| =
      |a| * r ^ d := by
  let u : Fin (d + 1) → Fin (d + 1) → ℝ :=
    Fin.cons (fun _ => 1) (fun i => truncationCoordinateVector (d + 1) (τ i))
  let k : Fin (d + 1) → ℝ := Fin.cons a (fun _ => -r)
  have he : Fin.cons (fun _ => a)
      (fun i => (-r) • truncationCoordinateVector (d + 1) (τ i)) =
      fun i => k i • u i := by
    funext i j
    induction i using Fin.cases <;> simp [k, u]
  rw [he, (truncationRowDeterminant (d + 1)).map_smul_univ]
  simp only [k, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, abs_mul,
    abs_pow, abs_neg, abs_of_nonneg hr]
  rw [show |truncationRowDeterminant (d + 1) u| = 1 from
    truncation_ones_embedding_abs_det d τ, mul_one]

theorem truncation_parallel_horizontal_abs_det_zero (d : ℕ) (q : ℝ)
    (g : Fin d → Fin (d + 2) → ℝ) :
    truncationRowDeterminant (d + 2)
      (Fin.cons (fun _ => 1) (Fin.cons (fun _ => -q) g)) = 0 := by
  let u : Fin (d + 2) → Fin (d + 2) → ℝ :=
    Fin.cons (fun _ => 1) (Fin.cons (fun _ => 1) g)
  let k : Fin (d + 2) → ℝ := Fin.cons 1 (Fin.cons (-q) (fun _ => 1))
  have he : Fin.cons (fun _ => 1) (Fin.cons (fun _ => -q) g) =
      fun i => k i • u i := by
    funext i j
    induction i using Fin.cases with
    | zero => simp [k, u]
    | succ i => induction i using Fin.cases <;> simp [k, u]
  rw [he, (truncationRowDeterminant (d + 2)).map_smul_univ]
  have hz : truncationRowDeterminant (d + 2) u = 0 := by
    apply (truncationRowDeterminant (d + 2)).map_eq_zero_of_eq u (i := 0) (j := 1)
    · simp [u]
    · exact Fin.zero_ne_one
  rw [hz, smul_zero]

def truncationLiftVector {d : ℕ} (b : ℝ) (u : Fin d → ℝ) : Fin (d + 1) → ℝ :=
  Fin.cons b u

theorem truncation_lifted_coordinate_embedding_abs_det (d : ℕ) (a b r : ℝ)
    (hr : 0 ≤ r) (τ : Fin d ↪ Fin d) :
    |truncationRowDeterminant (d + 1)
      (Fin.cons (truncationLiftVector a (fun _ => b))
        (fun i => truncationLiftVector 0 ((-r) • truncationCoordinateVector d (τ i))))| =
      |a| * r ^ d := by
  let A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
    Matrix.of (Fin.cons (truncationLiftVector a (fun _ => b))
      (fun i => truncationLiftVector 0 ((-r) • truncationCoordinateVector d (τ i))))
  have he : A.det = a * truncationRowDeterminant d
      (fun i => (-r) • truncationCoordinateVector d (τ i)) := by
    change A.det = a * (Matrix.of (fun i => (-r) • truncationCoordinateVector d (τ i))).det
    rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
    simp [A, truncationLiftVector, Matrix.submatrix]
    left
    congr 1
  change |A.det| = _
  rw [he, abs_mul, truncation_scaled_coordinate_embedding_abs_det d r hr τ]

theorem truncation_lifted_pair_embedding_abs_det (d : ℕ) (q s r : ℝ)
    (hr : 0 ≤ r) (hqs : s ≤ q) (τ : Fin d ↪ Fin (d + 1)) :
    |truncationRowDeterminant (d + 2)
      (Fin.cons (truncationLiftVector 1 (fun _ => 1))
        (Fin.cons (truncationLiftVector (-s) (fun _ => -q))
          (fun i => truncationLiftVector 0
            ((-r) • truncationCoordinateVector (d + 1) (τ i)))))| =
      (q - s) * r ^ d := by
  let g : Fin d → Fin (d + 2) → ℝ := fun i =>
    truncationLiftVector 0 ((-r) • truncationCoordinateVector (d + 1) (τ i))
  let v : Fin (d + 2) → ℝ := truncationLiftVector 1 (fun _ => 1)
  let w : Fin (d + 2) → ℝ := truncationLiftVector (-s) (fun _ => -q)
  let z : Fin (d + 2) → ℝ := truncationLiftVector (q - s) (fun _ => 0)
  let A : Matrix (Fin (d + 2)) (Fin (d + 2)) ℝ := Matrix.of (Fin.cons v (Fin.cons w g))
  have hz : z = w + q • v := by
    funext i
    induction i using Fin.cases with
    | zero => simp [z, w, v, truncationLiftVector]; ring
    | succ i => simp [z, w, v, truncationLiftVector]
  have he : (Matrix.of (Fin.cons v (Fin.cons z g))).det = A.det := by
    have hh := Matrix.det_updateRow_add_smul_self A (i := 1) (j := 0) Fin.zero_ne_one.symm q
    have hu : A.updateRow 1 (A 1 + q • A 0) = Matrix.of (Fin.cons v (Fin.cons z g)) := by
      ext i j
      induction i using Fin.cases with
      | zero => rw [Matrix.updateRow_ne Fin.zero_ne_one]; rfl
      | succ i =>
        induction i using Fin.cases with
        | zero =>
          change (A.updateRow 1 (A 1 + q • A 0)) 1 j = z j
          rw [Matrix.updateRow_self]
          exact (congrFun hz j).symm
        | succ i => rw [Matrix.updateRow_ne (Fin.succ_succ_ne_one i)]; rfl
    rw [hu] at hh
    exact hh
  have hswap : (Fin.cons v (Fin.cons z g)) ∘ Equiv.swap (0 : Fin (d + 2)) 1 =
      Fin.cons z (Fin.cons v g) := by
    funext i
    induction i using Fin.cases with
    | zero => simp
    | succ i =>
      induction i using Fin.cases with
      | zero => simp
      | succ i =>
        rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne
          (Fin.succ_ne_zero i.succ) (Fin.succ_succ_ne_one i)]
        rfl
  have ha : |A.det| = |(Matrix.of (Fin.cons z (Fin.cons v g))).det| := by
    rw [← he]
    have hh := zonotope_alternating_abs_swap (truncationRowDeterminant (d + 2))
      (Fin.cons v (Fin.cons z g)) 1
    rw [hswap] at hh
    exact hh.symm
  have hf : (Matrix.of (Fin.cons z (Fin.cons v g))).det =
      (q - s) * truncationRowDeterminant (d + 1)
        (Fin.cons (fun _ => 1)
          (fun i => (-r) • truncationCoordinateVector (d + 1) (τ i))) := by
    change (Matrix.of (Fin.cons z (Fin.cons v g))).det =
      (q - s) * (Matrix.of (Fin.cons (fun _ => 1)
        (fun i => (-r) • truncationCoordinateVector (d + 1) (τ i)))).det
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
    simp [z, v, g, truncationLiftVector, Matrix.submatrix]
    left
    congr 1
    ext i j
    induction i using Fin.cases <;> rfl
  change |A.det| = _
  rw [ha, hf, abs_mul, abs_of_nonneg (sub_nonneg.mpr hqs),
    truncation_scaled_ones_embedding_abs_det d 1 r hr τ]
  simp

def truncationPackedHorizontal (d : ℕ) (c r q : ℝ) :
    Fin (d + 2) → Fin d → ℝ :=
  Fin.cons (fun _ => c) (Fin.cons (fun _ => -c * q)
    (fun i j => -c * r * truncationCoordinateVector d i j))

def truncationPackedLifted (d : ℕ) (c r q s : ℝ) :
    Fin (d + 2) → Fin (d + 1) → ℝ :=
  Fin.cons (truncationLiftVector c (fun _ => c))
    (Fin.cons (truncationLiftVector (-c * s) (fun _ => -c * q))
      (fun i => truncationLiftVector 0
        (fun j => -c * r * truncationCoordinateVector d i j)))

def truncationPackedTupleSum {d m : ℕ} (v : Fin m → Fin d → ℝ) : ℝ :=
  ∑ σ : Fin d → Fin m, |horizontalDeterminant (fun j => v (σ j))|

theorem truncation_tuple_sum_eq_injection_sum {d m : ℕ}
    (v : Fin m → Fin d → ℝ) :
    truncationPackedTupleSum v =
      ∑ σ : Fin d ↪ Fin m, |truncationRowDeterminant d (fun j => v (σ j))| := by
  unfold truncationPackedTupleSum
  change (∑ σ : Fin d → Fin m, |(Matrix.of (fun i j => v (σ j) i)).det|) = _
  rw [finite_determinant_tuple_sum_eq_injection_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [truncation_row_determinant_horizontal]
  rfl

theorem truncation_tuple_sum_smul {d m : ℕ}
    (v : Fin m → Fin d → ℝ) (c : ℝ) (hc : 0 ≤ c) :
    truncationPackedTupleSum (fun i => c • v i) = c ^ d * truncationPackedTupleSum v := by
  rw [truncation_tuple_sum_eq_injection_sum, truncation_tuple_sum_eq_injection_sum]
  have hd (σ : Fin d ↪ Fin m) :
      |truncationRowDeterminant d (fun j => c • v (σ j))| =
        c ^ d * |truncationRowDeterminant d (fun j => v (σ j))| := by
    rw [(truncationRowDeterminant d).map_smul_univ]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, abs_mul, abs_pow, abs_of_nonneg hc]
  simp_rw [hd]
  exact Finset.mul_sum _ _ _ |>.symm

theorem truncation_packed_horizontal_scalar (d : ℕ) (c r q : ℝ) :
    truncationPackedHorizontal d c r q =
      fun i => c • truncationPackedHorizontal d 1 r q i := by
  funext i j
  induction i using Fin.cases with
  | zero => simp [truncationPackedHorizontal]
  | succ i =>
    induction i using Fin.cases with
    | zero => simp [truncationPackedHorizontal]
    | succ i => simp [truncationPackedHorizontal]; ring

theorem truncation_packed_lifted_scalar (d : ℕ) (c r q s : ℝ) :
    truncationPackedLifted d c r q s =
      fun i => c • truncationPackedLifted d 1 r q s i := by
  funext i j
  induction i using Fin.cases with
  | zero => induction j using Fin.cases <;> simp [truncationPackedLifted, truncationLiftVector]
  | succ i =>
    induction i using Fin.cases with
    | zero => induction j using Fin.cases <;> simp [truncationPackedLifted, truncationLiftVector]
    | succ i =>
      induction j using Fin.cases with
      | zero => simp [truncationPackedLifted, truncationLiftVector]
      | succ j => simp [truncationPackedLifted, truncationLiftVector]; ring

theorem truncation_packed_horizontal_tuple_sum {d : ℕ} (hd : 2 ≤ d)
    (c r q : ℝ) (hc : 0 ≤ c) (hr : 0 ≤ r) (hq : 0 ≤ q) :
    truncationPackedTupleSum (truncationPackedHorizontal d c r q) =
      (d.factorial : ℝ) * c ^ d *
        (r ^ d + (d : ℝ) * (1 + q) * r ^ (d - 1)) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hd
  have heq : d = k + 2 := by omega
  clear hk
  subst d
  let f := truncationRowDeterminant (k + 2)
  let g : Fin (k + 2) → Fin (k + 2) → ℝ :=
    fun i => (-r) • truncationCoordinateVector (k + 2) i
  have hpack : truncationPackedHorizontal (k + 2) 1 r q =
      Fin.cons (fun _ => 1) (Fin.cons (fun _ => -q) g) := by
    funext i j
    induction i using Fin.cases with
    | zero => simp [truncationPackedHorizontal]
    | succ i => induction i using Fin.cases <;> simp [truncationPackedHorizontal, g]
  have hsum := truncation_two_special_injection_sum f (fun _ => 1) (fun _ => -q) g
  have hbase : (∑ σ : Fin (k + 2) ↪ Fin (k + 2), |f (fun i => g (σ i))|) =
      ((k + 2).factorial : ℝ) * r ^ (k + 2) := by
    simp only [f, g, truncation_scaled_coordinate_embedding_abs_det (k + 2) r hr,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    simp only [Fintype.card_embedding_eq, Fintype.card_fin, Nat.descFactorial_self]
  have htop : (∑ σ : Fin (k + 1) ↪ Fin (k + 2),
      |f (Fin.cons (fun _ => 1) (fun i => g (σ i)))|) =
      ((k + 2).factorial : ℝ) * r ^ (k + 1) := by
    simp only [f, g, truncation_scaled_ones_embedding_abs_det (k + 1) 1 r hr,
      abs_one, one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      truncation_embedding_card_predecessor]
  have hbot : (∑ σ : Fin (k + 1) ↪ Fin (k + 2),
      |f (Fin.cons (fun _ => -q) (fun i => g (σ i)))|) =
      ((k + 2).factorial : ℝ) * q * r ^ (k + 1) := by
    simp only [f, g, truncation_scaled_ones_embedding_abs_det (k + 1) (-q) r hr,
      abs_neg, abs_of_nonneg hq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      truncation_embedding_card_predecessor]
    ring
  have hpair : (∑ σ : Fin k ↪ Fin (k + 2),
      |f (Fin.cons (fun _ => 1) (Fin.cons (fun _ => -q) (fun i => g (σ i))))|) = 0 := by
    simp only [f, truncation_parallel_horizontal_abs_det_zero, abs_zero, Finset.sum_const_zero]
  rw [hbase, htop, hbot, hpair] at hsum
  rw [truncation_packed_horizontal_scalar, truncation_tuple_sum_smul _ _ hc,
    hpack, truncation_tuple_sum_eq_injection_sum]
  rw [hsum]
  have hn : k + 2 - 1 = k + 1 := by omega
  simp only [hn, Nat.cast_add, mul_zero, add_zero]
  ring

theorem truncation_packed_lifted_tuple_sum {d : ℕ} (hd : 1 ≤ d)
    (c r q s : ℝ) (hc : 0 ≤ c) (hr : 0 ≤ r) (hs : 0 ≤ s) (hqs : s ≤ q) :
    truncationPackedTupleSum (truncationPackedLifted d c r q s) =
      ((d + 1).factorial : ℝ) * c ^ (d + 1) *
        (r ^ d * (1 + s) + (d : ℝ) * r ^ (d - 1) * (q - s)) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hd
  have heq : d = k + 1 := by omega
  clear hk
  subst d
  let f := truncationRowDeterminant (k + 2)
  let g : Fin (k + 1) → Fin (k + 2) → ℝ := fun i =>
    truncationLiftVector 0 ((-r) • truncationCoordinateVector (k + 1) i)
  let v : Fin (k + 2) → ℝ := truncationLiftVector 1 (fun _ => 1)
  let w : Fin (k + 2) → ℝ := truncationLiftVector (-s) (fun _ => -q)
  have hpack : truncationPackedLifted (k + 1) 1 r q s = Fin.cons v (Fin.cons w g) := by
    funext i j
    induction i using Fin.cases with
    | zero => simp [truncationPackedLifted, v]
    | succ i =>
      induction i using Fin.cases with
      | zero => simp [truncationPackedLifted, w]
      | succ i =>
        induction j using Fin.cases <;> simp [truncationPackedLifted, g, truncationLiftVector]
  have hsum := truncation_two_special_injection_sum f v w g
  have hbase : (∑ σ : Fin (k + 2) ↪ Fin (k + 1), |f (fun i => g (σ i))|) = 0 := by
    have : IsEmpty (Fin (k + 2) ↪ Fin (k + 1)) := ⟨fun σ => by
      have hh := Fintype.card_le_of_embedding σ
      simp only [Fintype.card_fin] at hh
      omega⟩
    exact Finset.sum_of_isEmpty _
  have htop : (∑ σ : Fin (k + 1) ↪ Fin (k + 1),
      |f (Fin.cons v (fun i => g (σ i)))|) =
      ((k + 1).factorial : ℝ) * r ^ (k + 1) := by
    simp only [f, v, g, truncation_lifted_coordinate_embedding_abs_det (k + 1) 1 1 r hr,
      abs_one, one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Fintype.card_embedding_eq, Fintype.card_fin, Nat.descFactorial_self]
  have hbot : (∑ σ : Fin (k + 1) ↪ Fin (k + 1),
      |f (Fin.cons w (fun i => g (σ i)))|) =
      ((k + 1).factorial : ℝ) * s * r ^ (k + 1) := by
    simp only [f, w, g, truncation_lifted_coordinate_embedding_abs_det (k + 1) (-s) (-q) r hr,
      abs_neg, abs_of_nonneg hs, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Fintype.card_embedding_eq, Fintype.card_fin, Nat.descFactorial_self]
    ring
  have hpair : (∑ σ : Fin k ↪ Fin (k + 1),
      |f (Fin.cons v (Fin.cons w (fun i => g (σ i))))|) =
      ((k + 1).factorial : ℝ) * (q - s) * r ^ k := by
    simp only [f, v, w, g, truncation_lifted_pair_embedding_abs_det k q s r hr hqs,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      truncation_embedding_card_predecessor]
    ring
  rw [hbase, htop, hbot, hpair] at hsum
  rw [truncation_packed_lifted_scalar, truncation_tuple_sum_smul _ _ hc,
    hpack, truncation_tuple_sum_eq_injection_sum, hsum]
  simp only [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  ring

#print axioms truncation_row_determinant_horizontal
#print axioms truncation_coordinate_embedding_abs_det
#print axioms truncation_ones_embedding_abs_det
#print axioms truncation_two_special_injection_sum
#print axioms truncation_embedding_card_predecessor
#print axioms truncation_scaled_coordinate_embedding_abs_det
#print axioms truncation_scaled_ones_embedding_abs_det
#print axioms truncation_parallel_horizontal_abs_det_zero
#print axioms truncation_lifted_coordinate_embedding_abs_det
#print axioms truncation_lifted_pair_embedding_abs_det
#print axioms truncation_tuple_sum_eq_injection_sum
#print axioms truncation_tuple_sum_smul
#print axioms truncation_packed_horizontal_scalar
#print axioms truncation_packed_lifted_scalar
#print axioms truncation_packed_horizontal_tuple_sum
#print axioms truncation_packed_lifted_tuple_sum

end Entry005
