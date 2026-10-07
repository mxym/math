# Proof audit — entry 002 version 4

**Date:** 7 October 2026  
**Claim:** the smallest common scalar period of a successful finite
principal-ideal periodic sieve for Gaussian \(F_8\) is 130.

This audit is model-assisted mathematical checking, not external peer review
or formal verification.

## 1. Algebraic reduction

For \(\alpha=a+bi\), version 3 proves that
\[
t(\alpha)=\frac{a^2+b^2}{\gcd(|a|,|b|)}
\]
is the least positive scalar period, so
\(t(\alpha)\mathbb Z[i]\subseteq(\alpha)\).

If \(\pi\) is any Gaussian prime divisor of \(\alpha\), then
\(\pi\mid t(\alpha)\). The rational prime \(p\) below \(\pi\) divides the
integer \(t(\alpha)\):

- for inert \(\pi=p\), this is immediate;
- for split \(N\pi=p\), norm divisibility gives \(p\mid t(\alpha)^2\);
- for \(\pi\sim1+i\), divisibility of an integer by \(1+i\) forces evenness.

Thus \(p\) divides the radical of every common scalar period containing
\(t(\alpha)\), and
\[
(\alpha)\subseteq(\pi).
\]

**Audit direction check:** the maximal prime sieve excludes *more* points,
so its avoiding set is a subset of the original avoiding set. Hence an
infinite walk in the maximal prime avoiding set survives in every original
principal-list avoiding set with that period radical. This is the direction
needed for the lower bound.

Composite generators therefore cannot evade the reduction.

## 2. Completeness of the finite range

If a principal list has common scalar period \(Q<130\), then
\[
q=\operatorname{rad}Q
\]
is squarefree and \(q<130\). The exact certificate covers \(q=1\) and every
squarefree integer \(2\le q<130\), with no gaps. There are 79 such values in
total.

Prime powers do not require separate cases: the maximal excluded union is
already determined by the Gaussian prime ideals above the rational primes
dividing \(q\).

## 3. Negative witness verification

For every failed radical, the stored object contains

- the exact rational-prime factorization;
- canonical Gaussian prime generators;
- a starting lattice point;
- an ordered list of \(F_8\) steps;
- the nonzero quotient voltage;
- the number of allowed residues modulo \(q\).

The checker reconstructs the prime generators independently. Ideal
membership for \(\alpha=a+bi\) is checked from the two adjugate congruences
\[
 ax+by\equiv0\pmod{a^2+b^2},
\qquad
 -bx+ay\equiv0\pmod{a^2+b^2}.
\]
It checks every visited point, every step, quotient closure, nonzero voltage,
and the full allowed-residue count.

A quotient-closed walk with displacement \(qv\), \(v\ne0\), repeats by
translation because the avoiding set is \(q\)-periodic. It therefore gives
an infinite component, not merely a failed potential search.

The 79 witnesses contain 5009 steps in total; the longest has 129 steps.

## 4. Positive endpoint

The endpoint list is
\[
1+i,\quad2+i,\quad2-i,\quad3+2i,\quad3-2i.
\]
Its scalar periods are \(2,5,5,13,13\), so the lcm is exactly 130.

The v4 checker loads the frozen v3
gaussian_eight_steps_principal.json, checks that its data are exactly this
list and \(F_8\), and invokes the independent v3 verifier on the complete
potential. It recomputes:

- \(Q=130\);
- 4608 allowed residues;
- maximum quotient component size 580;
- Gaussian finite-exception component bound 92820.

Thus the lower bound and attainment use independent certificate types:
explicit nonzero-voltage walks below 130 and a full integer potential at
130.

## 5. Sharp-period generator rigidity

If a successful period-130 list had fewer than five generators, choose one Gaussian prime divisor of each generator and replace each principal ideal by that larger prime ideal. The avoiding set only shrinks, so success would persist. The exact endpoint certificate rules out all 31 proper subsets of the five prime ideals above 2, 5 and 13. Hence at least five generators are required.

For equality, factor
\[
130\sim(1+i)^2(2+i)(2-i)(3+2i)(3-2i).
\]
Up to associates this has exactly 48 divisor ideals, 47 of them nonunit. The independent endpoint checker reconstructs this complete divisor list directly from the exponents. If a five-generator successful list is given, its chosen prime divisors must be the five distinct endpoint primes. If one generator is a proper subideal of its assigned prime ideal, enlarge the other four generators to the remaining four prime ideals. The resulting avoiding set is still a subset of the original one. The certificate supplies a nonzero-voltage walk for every such replacement: 31 possibilities inside the ramified prime and 23 inside each of the four split primes, 123 cases total. Thus every containment must be equality, proving uniqueness up to associates and order.

The endpoint-rigidity package contains 154 exact failure witnesses, 23016 steps in total, with maximum walk length 186. Ordinary and optimized Python reports are byte-identical.

## 6. Gaussian replays

Ordinary Python and optimized Python produce byte-identical output:

~~~text
{"arithmetic": "exact integer", "failed_radicals": 79, "largest_failed_radical": 129, "max_failure_walk_length": 129, "positive_allowed_residues": 4608, "positive_avoiding_bound": 580, "positive_gaussian_component_bound": 92820, "positive_period": 130, "status": "PASS"}
~~~

SHA-256 of code/period_optimality.json:

d5d90d7c15cce9d69f92ed83197d8b7b66e9b6040fdb54a06ffcfb7eb60f11f2.

## 7. Real-quadratic period and endpoint audit

For \(R=\mathbb Z[\sqrt2]\), the scalar-period formula inherited from v3 is
\[
t(a+b\sqrt2)=\frac{|a^2-2b^2|}{\gcd(|a|,|b|)}.
\]
The same radical-domination argument is valid because \(R\) is a PID and,
for a prime element \(\pi\), the contraction
\[
(\pi)\cap\mathbb Z=(p)
\]
for the rational prime below it. Since
\(t(\alpha)\in(\pi)\cap\mathbb Z\), that rational prime divides
\(t(\alpha)\).

The lower-period checker exhausts the nine squarefree radicals
\[
1,2,3,5,6,7,10,11,13.
\]
It independently reconstructs the ramified prime over \(2\), both split
primes over \(7\), and the inert ideals over \(3,5,11,13\). Every maximal
prime sieve in this range has a stored nonzero-voltage \(F_8\) walk.

At period \(14\),
\[
14=(\sqrt2)^2(3+\sqrt2)(3-\sqrt2).
\]
Unique factorization therefore gives exactly
\(3\cdot2\cdot2=12\) divisor ideals up to associates, 11 nonunit. The
endpoint checker reconstructs all 11 from the exponent triples, rather than
from a coefficient box.

Among prime subsets of size at most two, the only successful pairs are
\[
\{\sqrt2,3+\sqrt2\},\qquad
\{\sqrt2,3-\sqrt2\}.
\]
The empty set, all three singletons, and the pair of the two conjugate
norm-seven primes have explicit nonzero-voltage failures.

For each of the two successful pairs, replacing either prime ideal by any
proper nonunit divisor ideal of \((14)\) contained in it also has an exact
nonzero-voltage witness. There are 24 such replacement cases. This proves
the two-generator endpoint classification: any successful period-14
two-generator list must, up to associates and order, be one of the two
displayed pairs.

The package contains 38 real-quadratic failure witnesses, 464 \(F_8\) steps
in total, with maximum length 14. Ordinary and optimized Python reports are
byte-identical. The frozen v3 positive certificate is replayed independently
and gives period 14, avoiding quotient bound 6, and inherited conservative
irreducible-component bound 351232.

## 8. Nonclaims

The audit does not establish:

- optimality of the true Gaussian or real-quadratic irreducible component size;
- optimality among periodic obstructions not expressible as finite unions of
  principal ideals;
- a lower bound for arbitrary proofs of the Gaussian moat theorem;
- bibliographic novelty or priority;
- Lean formalization.

No floating-point comparison, random search, SAT/SMT output, or unchecked
solver result is a proof dependency.
