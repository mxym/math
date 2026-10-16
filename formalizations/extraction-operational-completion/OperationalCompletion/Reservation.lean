import OperationalCompletion.ReservedSets
import MinimaxProfile.IntegerPacking
import MinimaxProfile.Minimax

open scoped BigOperators ComplexOrder
open Matrix SymmetricSupport SpectralProtocol MinimaxProfile
namespace OperationalCompletion
noncomputable section

def reservationDivisor (J r : ℕ) : ℕ := 4*J*r
def reservedSmall (a J r : ℕ) : ℕ := a/reservationDivisor J r
def reservedLarge (a J r : ℕ) : ℕ := a-J*reservedSmall a J r

theorem reservationDivisor_pos (J r : ℕ) (hJ : 0<J) (hr : 0<r) : 0<reservationDivisor J r := by
  unfold reservationDivisor
  positivity

theorem reservationDivisor_ge_sum (J r : ℕ) (hJ : 0<J) (hr : 0<r) :
    J+r≤reservationDivisor J r := by
  have h₁ := Nat.mul_le_mul_left J (show 1≤r by omega)
  have h₂ := Nat.mul_le_mul_right r (show 1≤J by omega)
  unfold reservationDivisor
  nlinarith

theorem reservedLarge_lower (a J r : ℕ) (hJ : 0<J) (hr : 0<r) :
    r*reservedSmall a J r≤reservedLarge a J r := by
  have hh := Nat.mul_le_mul_right (reservedSmall a J r) (reservationDivisor_ge_sum J r hJ hr)
  have hmul : reservationDivisor J r*reservedSmall a J r≤a := Nat.mul_div_le _ _
  have hsum : r*reservedSmall a J r+J*reservedSmall a J r≤a := by nlinarith
  exact Nat.le_sub_of_add_le hsum

theorem reserved_dimensions_budget (a J r : ℕ) (hJ : 0<J) (hr : 0<r) :
    reservedLarge a J r+J*reservedSmall a J r=a := by
  have hh := Nat.mul_le_mul_right (reservedSmall a J r)
    ((Nat.le_add_right J r).trans (reservationDivisor_ge_sum J r hJ hr))
  have hmul : reservationDivisor J r*reservedSmall a J r≤a := Nat.mul_div_le _ _
  unfold reservedLarge
  omega

theorem reservedSmall_mono (a b J r : ℕ) (hab : a≤b) : reservedSmall a J r≤reservedSmall b J r :=
  Nat.div_le_div_right hab

theorem reserved_pure_budget_at_small (a b J r : ℕ) (hJ : 0<J) (hr : 0<r)
    (hab : a≤b) (ha₀ : 0<reservedSmall a J r) :
    r≤(reservedLarge a J r/reservedSmall a J r)*(reservedLarge b J r/reservedSmall a J r) := by
  have hA := reservedLarge_lower a J r hJ hr
  have hB := reservedLarge_lower b J r hJ hr
  have hsmall := reservedSmall_mono a b J r hab
  have hqA : r≤reservedLarge a J r/reservedSmall a J r := (Nat.le_div_iff_mul_le ha₀).mpr hA
  have hqB : 1≤reservedLarge b J r/reservedSmall a J r := by
    apply (Nat.le_div_iff_mul_le ha₀).mpr
    have h := Nat.mul_le_mul_right (reservedSmall b J r) (show 1≤r by omega)
    nlinarith
  nlinarith

theorem reservedLarge_pos (a J r : ℕ) (hJ : 0<J) (hr : 0<r) (ha₀ : 0<reservedSmall a J r) :
    0<reservedLarge a J r := (Nat.mul_pos hr ha₀).trans_le (reservedLarge_lower a J r hJ hr)

theorem reserved_rank_le_product (a b J r : ℕ) (hJ : 0<J) (hr : 0<r)
    (hab : a≤b) (ha₀ : 0<reservedSmall a J r) : r≤reservedLarge a J r*reservedLarge b J r :=
  (reserved_pure_budget_at_small a b J r hJ hr hab ha₀).trans
    (Nat.mul_le_mul (Nat.div_le_self _ _) (Nat.div_le_self _ _))

def reservedPacking (a b J r : ℕ) (hJ : 0<J) (hr : 0<r)
    (hab : a≤b) (ha₀ : 0<reservedSmall a J r) : ℕ :=
  packingDimension (reservedLarge a J r) (reservedLarge b J r) r
    (reservedLarge_pos a J r hJ hr ha₀) (reserved_rank_le_product a b J r hJ hr hab ha₀)

theorem reservedPacking_properties (a b J r : ℕ) (hJ : 0<J) (hr : 0<r)
    (hab : a≤b) (ha₀ : 0<reservedSmall a J r) :
    0<reservedPacking a b J r hJ hr hab ha₀ ∧
      r≤(reservedLarge a J r/reservedPacking a b J r hJ hr hab ha₀)*
        (reservedLarge b J r/reservedPacking a b J r hJ hr hab ha₀) := by
  have h := packingDimension_properties (reservedLarge_pos a J r hJ hr ha₀)
    (reserved_rank_le_product a b J r hJ hr hab ha₀)
  exact ⟨h.1,h.2.2⟩

theorem reservedSmall_le_packing (a b J r : ℕ) (hJ : 0<J) (hr : 0<r)
    (hab : a≤b) (ha₀ : 0<reservedSmall a J r) :
    reservedSmall a J r≤reservedPacking a b J r hJ hr hab ha₀ := by
  have hA : reservedSmall a J r≤reservedLarge a J r := by
    have h := Nat.mul_le_mul_right (reservedSmall a J r) (show 1≤r by omega)
    have hl := reservedLarge_lower a J r hJ hr
    nlinarith
  exact feasible_le_packingDimension (reservedLarge_pos a J r hJ hr ha₀)
    (reserved_rank_le_product a b J r hJ hr hab ha₀) ha₀ hA
    (reserved_pure_budget_at_small a b J r hJ hr hab ha₀)

end
end OperationalCompletion
