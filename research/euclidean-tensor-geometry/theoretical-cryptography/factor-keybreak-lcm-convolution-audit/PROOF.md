# Exact audit of KeyBreak (C.59)

## 1. Printed statement

In Lemma C.12 the paper sets

[
 r'=rac r{gcd(r,ell)},qquad
 s'=rac s{gcd(s,2)},qquad
 L=operatorname{lcm}(H_1r',H_2s')
]

and the fixed PDF page 76 prints the nested-root bound

[
rac{rs}{2L}
le
rac{sqrt{rssqrt{gcd(r,ell)gcd(s,2)}}}
     {2sqrt{H_1H_2}}.
	ag{printed C.59}
]

## 2. Exact counterexample

Take a prime (ell>9), and set

[
H_1=H_2=1,qquad r=ell,qquad s=3,qquad t=3.
]

Then (r'=1), (s'=3), and (L=operatorname{lcm}(1,3)=3).
The divisibility conditions used immediately before (C.59) hold:
(H_1r'mid t) and (H_2s'mid t).

The printed inequality becomes

[
rac{ell}{2}le rac{sqrt3}{2}ell^{3/4},
]

equivalently (ellle9), contradicting (ell>9). The smallest prime
example is (ell=11). These conductors are compatible with the surrounding
setup: (r=11) divides the rational modulus (33), and (s=3) divides the
even algebraic modulus (6).

## 3. Correct inequality

Let

[
a=gcd(r,ell),qquad b=gcd(s,2).
]

Since an lcm is at least the geometric mean of its arguments,

[
L
ge sqrt{(H_1r')(H_2s')}
=sqrt{rac{H_1H_2rs}{ab}}.
]

Therefore

[
rac{rs}{2L}
le
rac{sqrt{rsab}}{2sqrt{H_1H_2}}
=
rac{sqrt{rs,gcd(r,ell)gcd(s,2)}}
     {2sqrt{H_1H_2}}.
]

Because (ble2),

[
rac{sqrt{rsab}}{2sqrt{H_1H_2}}
le
rac{sqrt{rsa}}{sqrt{H_1H_2}}.
]

This proves the repaired two-step inequality.

## 4. Mapping to (C.58)

If (ell
mid r), then (a=1). After the convergent (H_1,H_2)
sums this contributes the ordinary product (M_aM_b).

If (ellmid r), then (a=ell), since (ell) is prime. The repaired
inequality contributes one factor (sqrtell). Averaging over the prime band
gives precisely the second term printed in (C.58),

[
rac{sqrt{2U_0}}{|J|}M_b
sum_{rge U_0}sqrt r,a(r)omega_J(r).
]

The sentence immediately following (C.59) in the fixed PDF already states
this same condition, (ellmid r), correctly.

## 5. Scope

This audit establishes an exact counterexample to the printed intermediate
inequality and a local repair whose output is already the displayed bound
(C.58). It does not independently certify all of Lemma C.12, Theorem 3.1, or
either global factoring complexity theorem.
