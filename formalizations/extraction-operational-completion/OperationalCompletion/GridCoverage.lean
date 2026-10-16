import OperationalCompletion.GridLimit

open scoped BigOperators ComplexOrder Topology
open Matrix SymmetricSupport MinimaxProfile Filter ExtractionSpectrum
namespace OperationalCompletion
noncomputable section

theorem exists_geometric_quotient (J n d : ℕ) (hd : 0<d) (hdn : d≤n) (hn : n<2^J) :
    ∃ j,j<J ∧ d≤n/2^j ∧ n/2^j<2*d := by
  induction J generalizing n with
  | zero => simp only [pow_zero] at hn; omega
  | succ J ih =>
    by_cases hsmall : n<2*d
    · exact ⟨0,by omega,by simpa,by simpa⟩
    · have hhalf : d≤n/2 := (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)
      have hn' : n/2<2^J := by
        apply (Nat.div_lt_iff_lt_mul (by norm_num)).mpr
        simpa only [pow_succ] using hn
      obtain ⟨j,hj,hlo,hhi⟩ := ih (n/2) hhalf hn'
      refine ⟨j+1,by omega,?_,?_⟩
      · simpa only [Nat.div_div_eq_div_mul,pow_succ,Nat.mul_comm] using hlo
      · simpa only [Nat.div_div_eq_div_mul,pow_succ,Nat.mul_comm] using hhi

theorem gridWidth_covers (K a J d : ℕ) (hd : 0<d) (hdn : d≤min K a)
    (hn : min K a<2^J) :
    ∃ j,j<J ∧ d≤gridWidth K a j ∧ gridWidth K a j<2*d := by
  obtain ⟨j,hj,hlo,hhi⟩ := exists_geometric_quotient J (min K a) d hd hdn hn
  have hmax : gridWidth K a j=min K a/2^j := by
    apply max_eq_right
    omega
  exact ⟨j,hj,by rwa [hmax],by rwa [hmax]⟩

theorem grid_count_covers_local_eventually (m : ℕ) :
    ∀ᶠ k : ℕ in atTop,m^k<2^gridSectorCount k := by
  filter_upwards [eventually_gt_atTop m] with k hk
  have hm : m≤2^m := (show m<2^m from Nat.lt_two_pow_self).le
  have hpow : m^k≤2^(m*k) := by
    simpa only [pow_mul] using Nat.pow_le_pow_left hm k
  have hJ : m*k<gridSectorCount k := by unfold gridSectorCount; nlinarith
  exact hpow.trans_lt (Nat.pow_lt_pow_right (by norm_num) hJ)

/-- The same protocol retains every test width simultaneously, with a factor
two in its cutoff. The chosen geometric level is allowed to depend on the test,
while the original unitary and local channels do not. -/
theorem gridProtocol_test_width (m n k K d : ℕ) (hm : 0<m) (hn : 0<n)
    (hmn : m≤n) (hK : 0<K) (hk : 0<k) (hd : 0<d)
    (hdK : d≤K) (hda : d≤gridLocalDimension m k)
    (hcover : m^k<2^gridSectorCount k)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1) :
    ((d:ℝ)/K)*empiricalEntropyMass hX.1.isHermitian.eigenvalues k
      (sourceCutoff (m*n) k (gridLocalDimension m k) (gridLocalDimension n k) (2*d)) ≤
        (gridProtocol m n k K hm hn hmn hK).fidelity (tensorInput m n k X) := by
  have hmin : min K (gridLocalDimension m k)<2^gridSectorCount k := by
    apply lt_of_le_of_lt _ hcover
    exact (min_le_right _ _).trans (Nat.div_le_self _ _)
  obtain ⟨j,hj,hlo,hhi⟩ := gridWidth_covers K (gridLocalDimension m k) (gridSectorCount k) d
    hd (le_min hdK hda) hmin
  have hcut := sourceCutoff_antitone (m*n) k (gridLocalDimension m k) (gridLocalDimension n k)
    (gridWidth K (gridLocalDimension m k) j) (2*d) (gridWidth_pos _ _ _) hhi.le
  have hmass := empiricalEntropyMass_mono hX.1.isHermitian.eigenvalues
    hX.1.eigenvalues_nonneg k hcut
  have hweight : (d:ℝ)/K≤(gridWidth K (gridLocalDimension m k) j:ℝ)/K :=
    div_le_div_of_nonneg_right (by exact_mod_cast hlo) (Nat.cast_nonneg K)
  exact (mul_le_mul hweight hmass
    (empiricalEntropyMass_nonneg _ hX.1.eigenvalues_nonneg _ _) (by positivity)).trans
    (gridProtocol_prefix m n k K hm hn hmn hK hk (hd.trans_le hda) X hX j hj)

end
end OperationalCompletion
