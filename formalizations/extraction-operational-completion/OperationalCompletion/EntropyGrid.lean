import OperationalCompletion.UniversalSectors
import MinimaxProfile.UniversalCutoff

open scoped BigOperators ComplexOrder
open Matrix SymmetricSupport MinimaxProfile
namespace OperationalCompletion
noncomputable section

def sourceCutoff (D k a b d : ℕ) : ℝ :=
  (Real.log ((a:ℝ)*b/(4*(d:ℝ)^2))-Real.log (orbitOverhead D k))/k

theorem sourceCutoff_budget (D k a b d : ℕ) (hD : 0<D) (hk : 0<k)
    (hd : 0<d) (hda : d≤a) (hdb : d≤b) :
    (ExtractionSpectrum.lowEntropyWords (ι := Fin D) k (sourceCutoff D k a b d)).card *
      (D*D+k-1).choose k ≤ (a/d)*(b/d) := by
  let S := ExtractionSpectrum.lowEntropyWords (ι := Fin D) k (sourceCutoff D k a b d)
  let C := (symmetricProjector (D*D) k).rank
  have hsize := ExtractionSpectrum.lowEntropyWords_card_le (ι := Fin D) k (sourceCutoff D k a b d)
  have hC : 0<C := symmetricProjector_rank_pos _ k (by positivity)
  have hO := orbitOverhead_pos D k hD
  have hQ : 0<(a:ℝ)*b/(4*(d:ℝ)^2) := by
    have ha : 0<a := lt_of_lt_of_le hd hda
    have hb : 0<b := lt_of_lt_of_le hd hdb
    positivity
  have he : orbitOverhead D k * Real.exp ((k:ℝ)*sourceCutoff D k a b d) =
      (a:ℝ)*b/(4*(d:ℝ)^2) := by
    have hid : (k:ℝ)*sourceCutoff D k a b d =
        Real.log ((a:ℝ)*b/(4*(d:ℝ)^2))-Real.log (orbitOverhead D k) := by
      unfold sourceCutoff
      field_simp
    rw [hid,Real.exp_sub,Real.exp_log hQ,Real.exp_log hO]
    field_simp
  have hreal : ((S.card*C:ℕ):ℝ) ≤ (((a/d)*(b/d):ℕ):ℝ) := by
    calc
      _ ≤ orbitOverhead D k * Real.exp ((k:ℝ)*sourceCutoff D k a b d) := by
        have hh := mul_le_mul_of_nonneg_right hsize (show (0:ℝ)≤C by positivity)
        simpa only [Fintype.card_fin,Nat.cast_mul,Nat.cast_add,Nat.cast_one,
          orbitOverhead,C,mul_comm,mul_left_comm,mul_assoc] using hh
      _ = _ := he
      _ ≤ _ := quarter_capacity_lower a b d hd hda hdb
  have hnats : S.card*C ≤ (a/d)*(b/d) := by exact_mod_cast hreal
  simpa only [S,C,symmetricProjector_rank_choose] using hnats

theorem sourceCutoff_antitone (D k a b d e : ℕ) (hd : 0<d) (hde : d≤e) :
    sourceCutoff D k a b e ≤ sourceCutoff D k a b d := by
  unfold sourceCutoff
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg k)
  apply sub_le_sub_right
  by_cases ha : a=0
  · simp [ha]
  by_cases hb : b=0
  · simp [hb]
  have hda : (0:ℝ)<d := by exact_mod_cast hd
  have hdeR : (d:ℝ)≤e := by exact_mod_cast hde
  have heR : (0:ℝ)<e := hda.trans_le hdeR
  have haR : (0:ℝ)<a := by exact_mod_cast Nat.pos_of_ne_zero ha
  have hbR : (0:ℝ)<b := by exact_mod_cast Nat.pos_of_ne_zero hb
  apply Real.log_le_log (by positivity)
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  nlinarith

def gridWidth (K a j : ℕ) : ℕ := max 1 (min K a / 2^j)

theorem gridWidth_pos (K a j : ℕ) : 0<gridWidth K a j := by
  unfold gridWidth
  omega

theorem gridWidth_le (K a j : ℕ) (hK : 0<K) (ha : 0<a) :
    gridWidth K a j ≤ min K a := by
  exact max_le (by omega) (Nat.div_le_self _ _)

theorem gridWidth_antitone (K a : ℕ) : Antitone (gridWidth K a) := by
  intro i j hij
  apply max_le_max_left
  exact Nat.div_le_div_left (Nat.pow_le_pow_right (by norm_num) hij) (by positivity)

def entropyGrid (D k K a b : ℕ) : ℕ → Finset (Word D k)
  | 0 => ∅
  | j+1 => ExtractionSpectrum.lowEntropyWords k (sourceCutoff D k a b (gridWidth K a j))

theorem entropyGrid_mono (D k K a b : ℕ) : Monotone (entropyGrid D k K a b) := by
  apply monotone_nat_of_le_succ
  intro j
  cases j with
  | zero => exact Finset.empty_subset _
  | succ j =>
    intro w hw
    simp only [entropyGrid,ExtractionSpectrum.lowEntropyWords,Finset.mem_filter,Finset.mem_univ,
      true_and] at hw ⊢
    exact hw.trans (sourceCutoff_antitone D k a b _ _ (gridWidth_pos K a (j+1))
      (gridWidth_antitone K a (by omega)))

/-- An explicit geometric grid meets every actual rank/packing budget.  The
single protocol is selected before all unknown input densities. -/
theorem geometric_universal_protocol (m n k K J a₀ b₀ : ℕ)
    (hm : 0<m) (hn : 0<n) (hk : 0<k) (hK : 0<K)
    (ha₀ : 0<a₀) (hab : a₀≤b₀) (ha : J*a₀≤m^k) (hb : J*b₀≤n^k) :
    ∃ V : KrausPPTProtocol (m^k) (n^k) K,
      V.IsProductLocal ∧
      ∀ (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1),
        weightedDifference J (fun j => (gridWidth K a₀ j:ℝ)/K)
          (fun j => ∑ w ∈ entropyGrid (m*n) k K a₀ b₀ j,
            ExtractionSpectrum.iidLaw hX.1.isHermitian.eigenvalues k w)
          ≤ V.fidelity (tensorInput m n k X) := by
  apply nested_universal_set_protocol m n k K J a₀ b₀ hK _
    (entropyGrid_mono _ _ _ _ _) rfl _
    (fun j _ => gridWidth_pos K a₀ j)
    (fun j _ => (gridWidth_le K a₀ j hK ha₀).trans (min_le_left _ _))
    (gridWidth_antitone _ _) ha hb
  intro j _
  exact sourceCutoff_budget (m*n) k a₀ b₀ _ (Nat.mul_pos hm hn) hk
    (gridWidth_pos K a₀ j) ((gridWidth_le K a₀ j hK ha₀).trans (min_le_right _ _))
    (((gridWidth_le K a₀ j hK ha₀).trans (min_le_right _ _)).trans hab)

theorem geometric_universal_prefix_protocol (m n k K J a₀ b₀ : ℕ)
    (hm : 0<m) (hn : 0<n) (hk : 0<k) (hK : 0<K)
    (ha₀ : 0<a₀) (hab : a₀≤b₀) (ha : J*a₀≤m^k) (hb : J*b₀≤n^k) :
    ∃ V : KrausPPTProtocol (m^k) (n^k) K,
      V.IsProductLocal ∧
      ∀ (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1)
        (j : ℕ), j<J →
        ((gridWidth K a₀ j:ℝ)/K) *
          ExtractionSpectrum.empiricalEntropyMass hX.1.isHermitian.eigenvalues k
            (sourceCutoff (m*n) k a₀ b₀ (gridWidth K a₀ j))
          ≤ V.fidelity (tensorInput m n k X) := by
  classical
  obtain ⟨V,hLocal,hV⟩ := geometric_universal_protocol m n k K J a₀ b₀
    hm hn hk hK ha₀ hab ha hb
  refine ⟨V,hLocal,?_⟩
  intro X hX j hj
  let G := fun i => ∑ w ∈ entropyGrid (m*n) k K a₀ b₀ i,
    ExtractionSpectrum.iidLaw hX.1.isHermitian.eigenvalues k w
  have hG : Monotone G := by
    intro i l hil
    exact Finset.sum_le_sum_of_subset_of_nonneg (entropyGrid_mono _ _ _ _ _ hil)
      (fun w _ _ => ExtractionSpectrum.iidLaw_nonneg _ hX.1.eigenvalues_nonneg k w)
  exact (weightedDifference_lower_prefix J j hj (fun i => (gridWidth K a₀ i:ℝ)/K) G
    (fun i => by positivity)
    (fun i l hil => div_le_div_of_nonneg_right (by exact_mod_cast gridWidth_antitone K a₀ hil)
      (Nat.cast_nonneg _)) hG (by simp [G,entropyGrid])).trans (hV X hX)

end
end OperationalCompletion
