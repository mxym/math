import SpectralProtocol.SpectralSelection
import Mathlib.Algebra.Order.Floor.Ring

open scoped BigOperators ComplexOrder Kronecker
open Matrix
namespace SpectralProtocol

/-- Integer-floor packing retains at least the continuous dimension budget
with the explicit factor four. All floor losses are proved on actual naturals. -/
theorem integer_floor_product_feasible (a b d r : ℕ)
    (hd : 0 < d) (hda : d ≤ a) (hdb : d ≤ b)
    (hbudget : 4*d^2*r ≤ a*b) : r ≤ (a/d)*(b/d) := by
  have half (x : ℕ) (hdx : d ≤ x) : x ≤ 2*(x/d)*d := by
    have hxdiv := Nat.div_pos hdx hd
    have hxmod := Nat.mod_lt x hd
    have hxeq := Nat.div_add_mod x d
    nlinarith
  have hprod := Nat.mul_le_mul (half a hda) (half b hdb)
  have hprod' : a*b ≤ (4*d^2)*((a/d)*(b/d)) := by nlinarith [hprod]
  exact Nat.le_of_mul_le_mul_left (hbudget.trans hprod') (by positivity)

/-- A feasible integer Bell dimension is constructed from an arbitrary valid
continuous budget. The lower bound is uniform at the small-budget endpoints. -/
theorem exists_quarter_packing (a b K r : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hK : 0 < K) (hrdim : r ≤ a*b) (w : ℝ) (hw : 1 ≤ w)
    (hwa : w ≤ a) (hwb : w ≤ b) (hwK : w ≤ K)
    (hbudget : w^2*(r:ℝ) ≤ (a:ℝ)*b) :
    ∃ d : ℕ, 0 < d ∧ d ≤ K ∧ r ≤ (a/d)*(b/d) ∧ w/4 ≤ (d:ℝ) := by
  by_cases hsmall : w < 4
  · refine ⟨1,by omega,by omega,?_,?_⟩
    · simpa only [Nat.div_one] using hrdim
    · norm_num
      linarith
  · have hw4 : 4 ≤ w := le_of_not_gt hsmall
    let d := ⌊w/2⌋₊
    have hd2 : 2 ≤ d := Nat.le_floor (by norm_num; linarith : (2:ℝ) ≤ w/2)
    have hd : 0 < d := by omega
    have hdw : (d:ℝ) ≤ w/2 := Nat.floor_le (by linarith)
    have hwd : w/2 < (d:ℝ)+1 := Nat.lt_floor_add_one (w/2)
    have hda : d ≤ a := by exact_mod_cast (show (d:ℝ) ≤ (a:ℝ) by linarith)
    have hdb : d ≤ b := by exact_mod_cast (show (d:ℝ) ≤ (b:ℝ) by linarith)
    have hdK : d ≤ K := by exact_mod_cast (show (d:ℝ) ≤ (K:ℝ) by linarith)
    have h4 : (4:ℝ)*(d:ℝ)^2 ≤ w^2 := by
      have hd0 : 0 ≤ (d:ℝ) := by positivity
      nlinarith
    have hbud : (4:ℝ)*(d:ℝ)^2*(r:ℝ) ≤ (a:ℝ)*b :=
      (mul_le_mul_of_nonneg_right h4 (by positivity)).trans hbudget
    have hbudn : 4*d^2*r ≤ a*b := by exact_mod_cast hbud
    refine ⟨d,hd,hdK,integer_floor_product_feasible a b d r hd hda hdb hbudn,?_⟩
    linarith

/-- The actual continuous prefix budget appearing in the paper. -/
noncomputable def prefixWidth (a b K r : ℕ) : ℝ :=
  min (a:ℝ) (min (K:ℝ) (Real.sqrt (((a:ℝ)*b)/r)))

theorem prefixWidth_feasible (a b K r : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hK : 0 < K) (hr : 0 < r) (hrdim : r ≤ a*b) (hab : a ≤ b) :
    ∃ d : ℕ, 0 < d ∧ d ≤ K ∧ r ≤ (a/d)*(b/d) ∧
      prefixWidth a b K r / 4 ≤ (d:ℝ) := by
  have hrpos : 0 < (r:ℝ) := by exact_mod_cast hr
  have hquot : 1 ≤ ((a:ℝ)*b)/r := by
    apply (le_div_iff₀ hrpos).mpr
    simpa only [one_mul] using (show (r:ℝ) ≤ (a:ℝ)*b by exact_mod_cast hrdim)
  have hsqrt : 1 ≤ Real.sqrt (((a:ℝ)*b)/r) := by
    exact (Real.le_sqrt (by norm_num) (by positivity)).mpr (by simpa only [one_pow] using hquot)
  have hw : 1 ≤ prefixWidth a b K r := by
    simp only [prefixWidth, le_min_iff]
    exact ⟨by exact_mod_cast ha, by exact_mod_cast hK, hsqrt⟩
  have hwa : prefixWidth a b K r ≤ a := min_le_left _ _
  have hwK : prefixWidth a b K r ≤ K := (min_le_right _ _).trans (min_le_left _ _)
  have hws : prefixWidth a b K r ≤ Real.sqrt (((a:ℝ)*b)/r) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hwb : prefixWidth a b K r ≤ b := hwa.trans (by exact_mod_cast hab)
  have hbudget : (prefixWidth a b K r)^2*(r:ℝ) ≤ (a:ℝ)*b := by
    have hs : (prefixWidth a b K r)^2 ≤ (((a:ℝ)*b)/r) :=
      ((Real.le_sqrt (by linarith) (by positivity)).mp hws)
    exact (le_div_iff₀ hrpos).mp hs
  exact exists_quarter_packing a b K r ha hb hK hrdim _ hw hwa hwb hwK hbudget

/-- Quarter-envelope lower bound, with an internally constructed actual
spectral projection and a physical deterministic pair of local channels. -/
theorem spectral_subset_quarter_lower (a b K : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hK : 0 < K) (hab : a ≤ b)
    (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hX : X.PosSemidef)
    (s : Finset (Fin a × Fin b)) (hs : 0 < s.card) :
    ∃ (d : ℕ) (hd : 0 < d) (hdk : d ≤ K)
      (U : Matrix.unitaryGroup (Fin a × Fin b) ℂ)
      (A : Fin (a/d) ⊕ Fin a → Matrix (Fin K) (Fin a) ℂ)
      (B : Fin (b/d) ⊕ Fin b → Matrix (Fin K) (Fin b) ℂ),
      (∑ j, (A j)ᴴ * A j = 1) ∧ (∑ j, (B j)ᴴ * B j = 1) ∧
      (prefixWidth a b K s.card / (4*K)) * (∑ i ∈ s, hX.isHermitian.eigenvalues i) ≤
        (Extraction.bellProjector (d := Fin K) *
          Extraction.krausApply (Extraction.productKraus A B)
            ((U : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) * X *
              (U : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)ᴴ)).trace.re := by
  have hrdim : s.card ≤ a*b := by
    have h := Finset.card_le_univ s
    simpa only [Fintype.card_prod, Fintype.card_fin] using h
  obtain ⟨d,hd,hdk,hr,hw⟩ := prefixWidth_feasible a b K s.card ha hb hK hs hrdim hab
  obtain ⟨U,A,B,hA,hB,he⟩ := spectral_subset_actual_lower a b d K hd hdk X hX s hr
  refine ⟨d,hd,hdk,U,A,B,hA,hB,?_⟩
  have hKpos : 0 < (K:ℝ) := by exact_mod_cast hK
  have hwidth : prefixWidth a b K s.card / (4*K) ≤ (d:ℝ)/K := by
    rw [div_mul_eq_div_div]
    exact div_le_div_of_nonneg_right hw hKpos.le
  exact (mul_le_mul_of_nonneg_right hwidth
    (Finset.sum_nonneg fun i _ => hX.eigenvalues_nonneg i)).trans he

end SpectralProtocol