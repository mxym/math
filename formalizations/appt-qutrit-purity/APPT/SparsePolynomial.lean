import APPT.Core

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace APPT.SparsePolynomial

abbrev Monomial := List Nat
abbrev Poly := List (Monomial × Int)

noncomputable def mon (x : Nat → ℝ) : Monomial → ℝ
  | [] => 1
  | i :: is => x i * mon x is

noncomputable def eval (x : Nat → ℝ) : Poly → ℝ
  | [] => 0
  | (m,c) :: ps => (c : ℝ) * mon x m + eval x ps

def insertVar (i : Nat) : Monomial → Monomial
  | [] => [i]
  | j :: js => if i ≤ j then i :: j :: js else j :: insertVar i js

def mulMon : Monomial → Monomial → Monomial
  | [], ns => ns
  | i :: is, ns => insertVar i (mulMon is ns)

theorem mon_insertVar (x : Nat → ℝ) (i : Nat) (m : Monomial) :
    mon x (insertVar i m) = x i * mon x m := by
  induction m with
  | nil => simp [insertVar, mon]
  | cons j js ih =>
    by_cases h : i ≤ j <;> simp [insertVar, h, mon, ih] <;> ring

theorem mon_mulMon (x : Nat → ℝ) (m n : Monomial) :
    mon x (mulMon m n) = mon x m * mon x n := by
  induction m with
  | nil => simp [mulMon, mon]
  | cons i is ih => simp [mulMon, mon_insertVar, ih, mon, mul_assoc]

theorem eval_append (x : Nat → ℝ) (p q : Poly) :
    eval x (p ++ q) = eval x p + eval x q := by
  induction p with
  | nil => simp [eval]
  | cons t ts ih => rcases t with ⟨m,c⟩; simp [eval, ih, add_assoc]

/-- The fallback preserves evaluation even without the expected sorting invariant. -/
def mergeAux : Nat → Poly → Poly → Poly
  | 0, p, q => p ++ q
  | _+1, [], q => q
  | _+1, p, [] => p
  | k+1, (m,c)::p, (n,d)::q =>
    if m = n then (m,c+d)::mergeAux k p q
    else if compare m n == Ordering.lt then
      (m,c)::mergeAux k p ((n,d)::q)
    else (n,d)::mergeAux k ((m,c)::p) q

def merge (p q : Poly) : Poly := mergeAux (p.length+q.length) p q

theorem eval_mergeAux (x : Nat → ℝ) (k : Nat) (p q : Poly) :
    eval x (mergeAux k p q) = eval x p + eval x q := by
  induction k generalizing p q with
  | zero => exact eval_append x p q
  | succ k ih =>
    cases p with
    | nil => simp [mergeAux, eval]
    | cons t p =>
      cases q with
      | nil => simp [mergeAux, eval]
      | cons u q =>
        rcases t with ⟨m,c⟩
        rcases u with ⟨n,d⟩
        by_cases h : m = n
        · subst n
          simp [mergeAux, eval, ih, Int.cast_add]; ring
        · by_cases hlt : (compare m n == Ordering.lt) = true
          · simp [mergeAux, h, hlt, eval, ih]; ring
          · simp [mergeAux, h, hlt, eval, ih]; ring

theorem eval_merge (x : Nat → ℝ) (p q : Poly) :
    eval x (merge p q) = eval x p + eval x q := eval_mergeAux ..

def scale (c : Int) : Poly → Poly
  | [] => []
  | (m,d)::p => (m,c*d)::scale c p

theorem eval_scale (x : Nat → ℝ) (c : Int) (p : Poly) :
    eval x (scale c p) = (c : ℝ)*eval x p := by
  induction p with
  | nil => simp [scale, eval]
  | cons t p ih => rcases t with ⟨m,d⟩; simp [scale, eval, ih, Int.cast_mul]; ring

def monoTimes (m : Monomial) (c : Int) : Poly → Poly
  | [] => []
  | (n,d)::p => (mulMon m n,c*d)::monoTimes m c p

theorem eval_monoTimes (x : Nat → ℝ) (m : Monomial) (c : Int) (p : Poly) :
    eval x (monoTimes m c p) = (c : ℝ)*mon x m*eval x p := by
  induction p with
  | nil => simp [monoTimes, eval]
  | cons t p ih =>
    rcases t with ⟨n,d⟩
    simp [monoTimes, eval, ih, mon_mulMon, Int.cast_mul]; ring

def mul : Poly → Poly → Poly
  | [], _ => []
  | (m,c)::p, q => merge (monoTimes m c q) (mul p q)

theorem eval_mul (x : Nat → ℝ) (p q : Poly) :
    eval x (mul p q) = eval x p * eval x q := by
  induction p with
  | nil => simp [mul, eval]
  | cons t p ih =>
    rcases t with ⟨m,c⟩
    simp [mul, eval_merge, eval_monoTimes, ih, eval]; ring

/-- Remove explicit zero coefficients; no orderedness hypothesis is needed. -/
def trim : Poly → Poly
  | [] => []
  | (m,c)::p => if c=0 then trim p else (m,c)::trim p

theorem eval_trim (x : Nat → ℝ) (p : Poly) : eval x (trim p) = eval x p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    rcases t with ⟨m,c⟩
    by_cases h : c=0 <;> simp [trim, h, eval, ih]

/-- Cubic multiplication is checked by the kernel, not native evaluation. -/
theorem cubic_control : trim (mul [([0],1),([1],1)]
    (mul [([0],1),([1],1)] [([0],1),([1],1)])) =
    [([0,0,0],1),([0,0,1],3),([0,1,1],3),([1,1,1],1)] := by decide +kernel

end APPT.SparsePolynomial
