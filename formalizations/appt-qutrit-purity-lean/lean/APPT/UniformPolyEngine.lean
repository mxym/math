import Mathlib
set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace APPT.UniformPolyEngine

/-- Exactly eleven variables: nine ordered-spectrum gaps and two populations. -/
abbrev Exponents := Vector Nat 11
abbrev Term := Exponents × Int
abbrev Polynomial := List Term

def zeroExp : Exponents := Vector.ofFn (fun _ => 0)
def oneExp (i : Fin 11) : Exponents := Vector.ofFn (fun j => if i = j then 1 else 0)
def addExp (u v : Exponents) : Exponents := Vector.zipWith (· + ·) u v

def monomial (e : Exponents) (c : Int) : Polynomial :=
  if c = 0 then [] else [(e,c)]

/-- Insert and collect a coefficient, retaining lexicographic order. -/
def insertTerm (t : Term) : Polynomial → Polynomial
  | [] => monomial t.1 t.2
  | (e,c)::xs =>
    if h : t.1 = e then
      if t.2 + c = 0 then xs else (e,t.2+c)::xs
    else if compare t.1.toList e.toList == Ordering.lt then
      if t.2 = 0 then (e,c)::xs else t::(e,c)::xs
    else (e,c)::insertTerm t xs

def add (p q : Polynomial) : Polynomial :=
  q.foldl (fun acc t => insertTerm t acc) p

def const (c : Int) : Polynomial := monomial zeroExp c
def varPoly (i : Fin 11) : Polynomial := monomial (oneExp i) 1

def scale (c : Int) (p : Polynomial) : Polynomial :=
  p.foldl (fun acc t => insertTerm (t.1,c*t.2) acc) []

def mul (p q : Polynomial) : Polynomial :=
  p.foldl (fun acc t =>
    q.foldl (fun acc s => insertTerm (addExp t.1 s.1, t.2*s.2) acc) acc) []

def power (p : Polynomial) : Nat → Polynomial
  | 0 => const 1
  | n+1 => mul p (power p n)

private def x := varPoly 0
private def y := varPoly 1

theorem cubic_binomial :
    power (add x y) 3 =
      add (add (add (power x 3) (scale 3 (mul (power x 2) y)))
        (scale 3 (mul x (power y 2)))) (power y 3) := by
  decide +kernel

theorem signed_parameter :
    mul (power (add x (scale (-18) y)) 2) (add x (scale (-1) y)) =
      mul (add x (scale (-1) y)) (power (add x (scale (-18) y)) 2) := by
  decide +kernel

end APPT.UniformPolyEngine

[executed on device: mxym (f1959ca3-d2c5-4728-a27e-5728accff85c)]
