import Init

/-!
# Finite binary-character algebra (standalone Lean 4)

Theorems needed for the exact symmetry of Gaussian binary-code
score orbits. No mathlib or additional axioms.
-/
namespace GaussianCode

def dot : (n : Nat) → (Fin n → Bool) → (Fin n → Bool) → Bool
  | 0, _, _ => false
  | n+1, u, g =>
     ((u 0) && (g 0)) ^^ dot n (fun i => u i.succ) (fun i => g i.succ)

def add (n : Nat) (u v : Fin n → Bool) : Fin n → Bool :=
  fun i => u i ^^ v i

theorem dot_add (n : Nat) (u v g : Fin n → Bool) :
    dot n (add n u v) g = (dot n u g ^^ dot n v g) := by
  induction n with
  | zero =>
    rfl
  | succ n ih =>
    simp only [dot, add]
    change ((u 0 ^^ v 0) && g 0 ^^
      dot n (add n (fun i => u i.succ) (fun i => v i.succ))
        (fun i => g i.succ)) =
        ((u 0 && g 0 ^^ dot n (fun i => u i.succ) (fun i => g i.succ)) ^^
         (v 0 && g 0 ^^ dot n (fun i => v i.succ) (fun i => g i.succ)))
    rw [ih]
    simp [Bool.and_xor_distrib_right, Bool.xor_left_comm]

def sign (b : Bool) : Int := if b then -1 else 1

theorem sign_xor (a b : Bool) :
    sign (a ^^ b) = sign a * sign b := by
  cases a <;> cases b <;> decide

theorem sign_dot_add (n : Nat) (u v g : Fin n → Bool) :
   sign (dot n (add n u v) g) =
      sign (dot n u g) * sign (dot n v g) := by
  rw [dot_add, sign_xor]

theorem add_self (n : Nat) (u : Fin n → Bool) :
    add n u u = fun _ => false := by
  funext i
  simp [add]

theorem sign_dot_self (n : Nat) (u g : Fin n → Bool) :
    sign (dot n (add n u u) g) = 1 := by
  rw [sign_dot_add]
  cases h : dot n u g <;> simp [sign]

/-! **Binary Gaussian orbit:** the following statements
are exactly the sign-changing group laws used in the
probabilistic-method construction. They are algebraic
kernel proofs; Gaussian measure and rank extraction are
handled separately in the paper. -/

def orbitCoord (n m : Nat) (cols : Fin m → Fin n → Bool)
    (u : Fin n → Bool) (j : Fin m) : Int :=
  sign (dot n u (cols j))

theorem orbit_mul (n m : Nat) (cols : Fin m → Fin n → Bool)
    (a u : Fin n → Bool) (j : Fin m) :
    orbitCoord n m cols (add n a u) j =
      orbitCoord n m cols a j * orbitCoord n m cols u j := by
  exact sign_dot_add n a u (cols j)

theorem sign_square (b : Bool) : sign b * sign b = 1 := by
  cases b <;> decide

theorem orbit_unit (n m : Nat) (cols : Fin m → Fin n → Bool)
    (u : Fin n → Bool) (j : Fin m) :
    orbitCoord n m cols u j * orbitCoord n m cols u j = 1 := by
  exact sign_square (dot n u (cols j))

theorem orbit_reflection_preserves_square
    (n m : Nat) (cols : Fin m → Fin n → Bool)
    (a u : Fin n → Bool) (j : Fin m) :
      (orbitCoord n m cols a j * orbitCoord n m cols u j) *
      (orbitCoord n m cols a j * orbitCoord n m cols u j) =
      orbitCoord n m cols u j * orbitCoord n m cols u j := by
  calc
    _ = (orbitCoord n m cols a j * orbitCoord n m cols a j) *
        (orbitCoord n m cols u j * orbitCoord n m cols u j) := by
          ac_rfl
    _ = 1 * (orbitCoord n m cols u j * orbitCoord n m cols u j) := by
          rw [orbit_unit]
    _ = _ := by simp

theorem orbit_reflection_maps_code
    (n m : Nat) (cols : Fin m → Fin n → Bool)
    (a u : Fin n → Bool) (j : Fin m) :
      orbitCoord n m cols (add n a u) j =
        orbitCoord n m cols a j * orbitCoord n m cols u j :=
  orbit_mul n m cols a u j

/-! An entire sign-reflection is an isometry of the
standard integer Euclidean square energy, not only
of each individual coordinate. -/

def sqEnergy : (n : Nat) → (Fin n → Int) → Int
  | 0, _ => 0
  | n + 1, x => x 0 * x 0 + sqEnergy n (fun i => x i.succ)

def signTwist (n : Nat) (mask : Fin n → Bool)
    (x : Fin n → Int) : Fin n → Int :=
  fun j => sign (mask j) * x j

theorem sqEnergy_signTwist (n : Nat) (mask : Fin n → Bool)
    (x : Fin n → Int) :
    sqEnergy n (signTwist n mask x) = sqEnergy n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sqEnergy, signTwist]
    change
      (sign (mask 0) * x 0) * (sign (mask 0) * x 0) +
        sqEnergy n (signTwist n (fun j => mask j.succ)
          (fun j => x j.succ)) =
      x 0 * x 0 + sqEnergy n (fun j => x j.succ)
    rw [ih]
    have hcoord :
      (sign (mask 0) * x 0) * (sign (mask 0) * x 0) = x 0 * x 0 := by
      calc
        _ = (sign (mask 0) * sign (mask 0)) * (x 0 * x 0) := by
          ac_rfl
        _ = x 0 * x 0 := by rw [sign_square]; simp
    rw [hcoord]

def codeTwist (n m : Nat) (cols : Fin m → Fin n → Bool)
    (a : Fin n → Bool) (x : Fin m → Int) : Fin m → Int :=
  signTwist m (fun j => dot n a (cols j)) x

theorem codeTwist_orbit (n m : Nat)
    (cols : Fin m → Fin n → Bool)
    (a u : Fin n → Bool) :
    codeTwist n m cols a (orbitCoord n m cols u) =
      orbitCoord n m cols (add n a u) := by
  funext j
  exact (orbit_mul n m cols a u j).symm

theorem codeTwist_preserves_energy (n m : Nat)
    (cols : Fin m → Fin n → Bool)
    (a : Fin n → Bool) (x : Fin m → Int) :
    sqEnergy m (codeTwist n m cols a x) = sqEnergy m x := by
  exact sqEnergy_signTwist m (fun j => dot n a (cols j)) x

/-! No sorry, no local axiom and no external proof assumptions
occur in this standalone module. -/
#print axioms GaussianCode.sign_dot_add
#print axioms GaussianCode.orbit_reflection_preserves_square
#print axioms GaussianCode.codeTwist_preserves_energy

end GaussianCode
