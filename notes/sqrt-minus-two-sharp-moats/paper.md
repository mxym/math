# Exact small-radius prime graphs and complete optimal periodic sieves in Z[sqrt(-2)]

A research note, 8 October 2026. Model-assisted written mathematics with exact,
independently replayable finite witnesses. No originality priority, external
referee, or proof-assistant completion is asserted.

## 1. Results and conventions

Put `t = sqrt(-2)` and `R = Z[t]`. Identify `a+bt` with `(a,b)` and use
its complex-plane Euclidean squared norm

\[
                  N(a,b)=a^2+2b^2.
\]

An *irreducible element* of R is a nonzero nonunit not expressible as a
product of nonunits. Graph vertices are **elements**, not elements modulo
associates. For a real radius `D >= 0`, let `G_D` be the graph on all
irreducibles, with distinct vertices adjacent when the complex Euclidean
distance is at most D. For each `0 <= D < 2`, the possible nonzero
squared step norms are in `{1,2,3}`. At `sqrt(3) <= D < 2` the complete
step set is

\[
 F_8=\{-1,0,1\}^2\setminus\{(0,0)\},
\]

in coefficient coordinates. Let `t` denote `(0,1)`, let
`u=1+t` denote `(1,1)`, and let `v=1-t` denote `(1,-1)`.

**Theorem A (complete infinite-graph classification).** For every
`1 <= D < 2` the graph `G_D` has precisely two three-vertex connected
components,

\[
 \{t,t+1,t-1\},\qquad \{-t,-t+1,-t-1\}.
\]

All other connected components have cardinality at most two. More
precisely:

1. For `1 <= D < sqrt(2)`, every vertex outside the displayed triples
   is isolated.
2. For `sqrt(2) <= D < 2`, every other nontrivial component is a
   **single vertical edge** between `(a,b)` and `(a,b+1)`, where
   `a` is an odd multiple of three, `b = 1 (mod 3)`, and both
   `a^2+2b^2` and `a^2+2(b+1)^2` are rational primes. Every such pair
   is a component, and all remaining vertices are isolated.
3. Crossing the geometric step threshold `D=sqrt(3)` adds **no new
   prime-prime edges**. For `0 <= D < 1`, all components are singletons.

Consequently the sharp start-independent component bound is

\[
 \boxed{\max_{C\in\pi_0(G_D)}|C|=1\ (0\le D<1),\qquad
             \max_{C\in\pi_0(G_D)}|C|=3\ (1\le D<2).}
\]

The pair `(3,1),(3,2)` has respective rational prime norms 11 and 17,
so two-vertex components are actually attained as soon as
`D >= sqrt(2)`.

We also determine all minimal periodic-sieve solutions, not just one
finite successful example. For a nonzero nonunit generator `g`, let
`q(g)` be the least positive integer with `g | q(g)` in R. A finite
list `H` has *common scalar period* `Q(H)=lcm_g q(g)`. Its allowed
graph includes **every lattice element** outside the union of its
principal ideals `(g)`, with steps in `F_8`. Call the list
*successful* if all allowed components are finite. This is a
stronger requirement than finiteness of the irreducible graph.

**Theorem B (sharp period and complete optimal-period ideal classification).**
The smallest possible common scalar period of a successful finite
principal-ideal sieve for `F_8` is exactly **6**. For a successful
list with common period 6, its generator ideals must include at
least one of these three collections:

\[
 \boxed{\begin{aligned}
  \mathcal A&=\{(t),(1+t)\},\\
  \mathcal B&=\{(t),(1-t)\},\\
  \mathcal C&=\{(2),(1+t),(1-t)\}.
 \end{aligned}}
\]

Conversely **any** list of nonzero nonunit generators dividing 6
whose ideal list contains one of these collections is successful.
There are no other inclusion-minimal successful ideal lists at period
6, even with composite generators or redundant ideals allowed.
In particular, the minimum generator count is two, attained only by
`{t,1+t}` and `{t,1-t}` up to associates and reordering.

For A and B the allowed lattice graph has components of size exactly
two. For C its allowed lattice graph has components of sizes four
and eight, both occurring. The complete assertion about *all* lists
is proved with three finite positive quotient partitions and four
explicit infinite-path witnesses, rather than relying on an
uninterpreted enumeration flag.

## 2. Divisibility and prime arithmetic in R

**Lemma 2.1 (norm Euclideanity).** The ring R has unique
factorization; its only units are `+1,-1`. For nonzero
`beta=c+dt`, the divisibility condition
`beta | alpha=a+bt` is equivalent to the two integer conditions

\[
 c^2+2d^2\mid ac+2bd,\qquad c^2+2d^2\mid bc-ad.       \tag{2.1}
\]

*Proof.* For any element `alpha/beta=x+yt` of the quotient field,
choose integers `m,n` with `|x-m|,|y-n| <= 1/2`. The remainder from
`m+nt` has norm at most `1/4+2/4=3/4<1` relative to beta. Therefore
the usual Euclidean algorithm applies, giving unique factorization.
The norm-one solutions are `(+-1,0)`, giving the units. Multiplying
`alpha` by the conjugate `c-dt` and dividing by `N(beta)` gives (2.1).
All these operations are integral except the intermediate quotient.
`□`

We have the factorizations

\[
        2=-t^2,\qquad 3=(1+t)(1-t).                     \tag{2.2}
\]

The three factors `t`, `u=1+t`, `v=1-t` have rational prime norms
`2,3,3`, so they are irreducible; `u` and `v` are not associates.
Two elementary congruence tests are

\[
 \begin{aligned}
   t\mid(a+bt) &\iff a\equiv0\pmod2,\\
   u\mid(a+bt) &\iff a-b\equiv0\pmod3,\\
   v\mid(a+bt) &\iff a+b\equiv0\pmod3.
 \end{aligned}                                             \tag{2.3}
\]

The first follows by division by `t`; the other two follow from
`t=-1 (mod u)` and `t=1 (mod v)`, or immediately from (2.1).

**Lemma 2.2 (the six exceptions).** If an irreducible `z` has
`gcd(N(z),6)>1`, then it belongs to

\[
                 E=\{\pm t,\ \pm(1+t),\ \pm(1-t)\}.       \tag{2.4}
\]

*Proof.* `2 | N(a,b)` forces `a` even, hence `t | z`. Meanwhile
`3 | N(a,b)` is equivalent to `a^2-b^2=0 (mod 3)`, hence `a=+b`
or `a=-b (mod 3)`. Thus `u|z` or `v|z`. An irreducible divisible
by one of these nonunits must be its associate. The only units
are `+-1`, giving precisely E. `□`

In particular, every other irreducible belongs to the set

\[
       V_6=\{(a,b):\gcd(a^2+2b^2,6)=1\}.                 \tag{2.5}
\]

The **exact** description of this set is

\[
 (a,b)\in V_6\iff a\text{ odd and }
 \begin{cases}
   b\equiv1,2\pmod3,&a\equiv0\pmod3,\\
   b\equiv0\pmod3,&a\not\equiv0\pmod3.
 \end{cases}                                              \tag{2.6}
\]

Indeed `2 | N` is exactly `a` even, and modulo three
`N=a^2-b^2`.

## 3. Proof of the global small-radius graph theorem

We first work with the largest allowed radius, the full eight-step
set `F_8`. Every irreducible outside E has odd first coordinate by
Lemma 2.2. An edge that changes its first coordinate by `+-1` lands
at an even-first-coordinate element, which could be irreducible only
if it is `+t` or `-t`, by (2.3) and irreducibility.

The two exceptional triples are closed. To verify this directly,
consider `t=(0,1)`: its eight possible neighbors are the two
units `(+-1,0)`, zero, the two primes `(+-1,1)`, and the
composites `(0,2),(+-1,2)` of norms 8 or 9. The prime
`(1,1)=1+t` has exactly one prime neighbor in `F_8`, namely
the central `t`; its other neighbors are zero, units, or
composites of norms 4,6,8,9,12. Reflection across either coordinate
axis and negation preserve the norm and eight-step adjacency, so
the other members of E have the symmetric neighbors. Hence the
**only** prime components meeting E are exactly the displayed two
three-vertex paths.

All other irreducible edges must preserve the (odd) first coordinate,
so the step is necessarily vertical `(0,+-1)`. At any fixed odd `a`,
formula (2.6) gives either one allowed residue class of `b mod 3`,
or a pair of consecutive classes separated by one forbidden class.
Thus every vertical connected run has at most two vertices. In the
second case its two positions must be `b=1,2 (mod 3)` and `a=0
(mod 3)`; these are outside E, and their norms are rational primes
exactly when they are irreducible. To justify the last equivalence,
note that both `a,b` are nonzero, `gcd(N,6)=1`, and the Euclidean
prime-factorization theorem in R implies an irreducible of this
kind has **rational prime norm**: this follows directly from unique factorization: any irreducible
`pi` divides the rational integer `N(pi)=pi*conj(pi)`, hence divides
some rational prime `p` in the ordinary integer factorization of
`N(pi)`. If `pi` is not associate to the rational integer `p`, then
`p=pi*beta` with both factors nonunits. Taking norms gives
`p^2=N(pi)N(beta)`, and each positive integer factor exceeds one;
since `p` is prime, necessarily `N(pi)=p`. If `pi` *is* associate
to `p`, it lies on the real axis `b=0`. Our two candidate vertices
have nonzero b, so their irreducibility is equivalent to having
rational prime norm. Conversely, norm a rational prime immediately
forces irreducibility. The pair `(a,b)=(3,1)` and `(3,2)` gives norms 11 and
17, showing the bound two is attained. This completes the exact
classification for the largest step set.

For smaller D, the only possible nonzero step norms below four are
1,2,3; their entire coefficient solutions are respectively
`(+−1,0)`, `(0,+−1)` and `(+−1,+−1)`. Both exceptional three-vertex
paths use only steps of norm one, so they persist for all `D>=1`.
At `D<sqrt(2)` no vertical steps are available, and other vertices
are isolated. At `D=sqrt(2)` the vertical edges appear. At
`D=sqrt(3)` the four diagonal directions are added, but their
first-coordinate parity flip prevents any new prime-prime edge,
as already checked above for the exceptional vertices. For `D<1`
there are no edges at all. Theorem A follows. `□`

## 4. Infinite obstruction from a nonzero period

**Lemma 4.1 (voltage-walk criterion).** If A is a periodic subset of
the integer lattice, invariant under `qZ^2`, and a finite allowed
F-step walk begins at z and ends at `z+qv` for nonzero integer
vector v, then the allowed infinite graph has an infinite component.

*Proof.* Translate the walk successively by `qv` and concatenate.
Periodicity preserves every vertex, and the points `z+nqv` are
distinct. `□`

**Lemma 4.2 (periodic partition criterion).** If finite nonempty sets
`C_1,...,C_s` of allowed lattice points have distinct residues modulo
q, jointly cover *all* allowed residues, and each is closed under
all allowed F-steps, then every infinite allowed component has at
most `max |C_i|` vertices. If each `C_i` is connected, the translates
of these `C_i` are exactly the infinite graph's components.

*Proof.* Every allowed point is a translate by `qZ^2` of exactly
one listed representative. Translate its set as well; periodicity
and the closure condition trap its entire connected component.
Connectivity gives equality. `□`

**Lemma 4.3 (no smaller scalar period).** Every finite principal-
ideal sieve with period `Q<6` fails for `F_8`.

*Proof.* Every nonunit generator g divides its own scalar period,
and hence `Q`. If `z` is a multiple of g, then `N(g)` divides
`N(z)`. A rational prime dividing `N(g)` must divide `Q`, since
`N(g)` divides `Q^2`. Therefore the entire set
`V_Q={z:gcd(N(z),Q)=1}` survives every generator ideal.
It is enough to exhibit a nonzero-voltage walk in V_Q.

For `Q=1,2,4,5`, use the vertical line `(1,b)`, `b in Z`:
`N(1,b)=1+2b^2` is always odd, and it is never zero modulo
five (two is not a quadratic residue modulo five). For `Q=3`,
use the three consecutive steps

\[
 (0,1)\to(1,0)\to(2,0)\to(3,1),
\]

whose intermediate norms are `2,1,4,11`, all coprime to three.
Their net displacement is `(3,0)`, so repetition produces an
infinite path in V_3. These paths also have exact indexed step
certificates in `code/certificate.json`. Lemma 4.1 finishes the
argument. `□`

## 5. Complete classification of the optimal-period sieves

By (2.2) and Euclidean unique factorization,

\[
                 6\sim t^2uv.
\]

Every generator appearing in a list of common scalar period six
divides six, so, **up to associates**, it is

\[
       t^{e_0}u^{e_1}v^{e_2},\quad
       0\le e_0\le2,\ e_1,e_2\in\{0,1\},\quad
       (e_0,e_1,e_2)\ne(0,0,0).                         \tag{5.1}
\]

There are exactly **11** proper divisor ideals (some composite).
We identify a finite sieve with the subset of these eleven ideals
appearing in its list: repetitions have no effect.

Write `A=(t)`, `B=(u)`, `C=(v)` and `D=(t^2)=(2)`.
For the three proposed successful lists:

* `A,B` and `A,C` force `a` odd, so allowed edges may change only b;
  the complementary linear congruence modulo three forbids exactly
  one class of b on each such line. Every run has size at most two.
  Modulo six there are six lifted components, all size two.
* `D,B,C` leave exactly 12 residues modulo six. A complete set of
  representatives in **two closed connected components** is

\[
 C_4=\{(-1,0),(0,-1),(0,1),(1,0)\},
\]
\[
 C_8=\{(1,3),(2,3),(3,1),(3,2),(3,4),(3,5),(4,3),(5,3)\}.
\]

The congruences (2.3) and membership in `(2)`, equivalent to
`a,b` both even, allow a direct check of all twelve points and their
eight neighbors. They lie in distinct residues modulo six and
exhaust the allowed residue classes. The checker also proves
connectivity and closure with exact integer division. Lemma 4.2
therefore supplies the full positive proof, not a bounded-window
experiment. Adding more generator ideals only removes vertices, so
any list containing one of these three bases is successful.

It remains to prove **there are no further successful lists**. Take
the four maximal generator subsets of the eleven divisor ideals:

| Label | Ideals omitted from the full eleven-ideal list | Initial point | Step indices | Final point |
| --- | --- | --- | --- | --- |
| M1 | A,D | (0,1) | 4,2,7,4,2,7 | (0,7) |
| M2 | A,B | (0,1) | 2,2,0,2,2,2,2,7 | (-6,7) |
| M3 | A,C | (0,1) | 7,7,5,7,7,7,2,7 | (6,7) |
| M4 | B,C | (1,0) | 4,4,4,4,4,4 | (1,6) |

The step indices are for the ordered list

\[
 0=(-1,-1),\ 1=(-1,0),\ 2=(-1,1),\ 3=(0,-1),
 \ 4=(0,1),\ 5=(1,-1),\ 6=(1,0),\ 7=(1,1).
\]

For each row, **every intermediate vertex** avoids *all nine*
remaining generator ideals; this is checked with the explicit
integral divisibility criterion (2.1) in the independent verifier.
Every final point differs from the initial point by a nonzero vector
in `6Z^2`. Since all eleven ideals have period dividing six,
Lemma 4.1 shows that each maximal subset M1--M4 is unsuccessful.

Now let H be a list not containing A,B or A,C or D,B,C as a
subcollection. If A is present, then both B and C must be absent,
so H is a subset of M4. If A is absent and D is also absent, H
is a subset of M1. Otherwise A is absent and D is present; since
D,B,C is not contained in H, either B is absent (H subset M2)
or C is absent (H subset M3). Therefore **every** list avoiding the
three positive bases is contained in one of M1--M4 and admits an
infinite allowed walk. This completes the classification in
Theorem B. The three bases are plainly inclusion-minimal.
Combined with Lemma 4.3, their common scalar period six is sharp.
`□`

## 6. Reproduction, audit scope and prior-method distinction

The core proof consists of norm-Euclidean factorization, modular
prime divisibility, an infinite graph decomposition, and two general
periodic-graph lifting lemmas. The finite data are exactly **twelve witnesses**: three complete
positive component partitions, four maximal-failure nonzero-displacement
walks, and five short lower-period walks. They are small enough for a
reader to check by hand, with the actual finite data shipped in
`code/certificate.json`.

The independent standard-library Python verifier
`code/check_exact.py` checks all positive components, every literal
integer principal-ideal predicate along the negative paths, all
lower periods, and the exceptional-prime neighborhood. As a *separate
redundant check*, it exhaustively examines all `2^11=2048` subsets
of divisor ideals with a literal 36-residue quotient BFS. Exactly
**896** subsets are successful, agreeing with the three-base
criterion. This number is diagnostic, not a substitute for the four
witnesses and the universal subset argument.

The methods are developed relative to OpenAI/math result family 028,
*Bounded-Step Walks on Gaussian Primes* (public reference commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`), and the existing
mxym/math manuscript 002 on quadratic-order moats. This note is a
new specific exact-classification investigation within that broader
programme. Other authors have studied finite-radius Eisenstein prime
walks, including S. Prasad (2014, arXiv:1412.2310) and N. Bandara
(2026, *Step-Norm Thresholds and Prime-Walk Connectivity in the
Eisenstein Integers*); their numerical truncations are not used in
our proofs. No claim of historical first discovery is made; broader
literature comparison and human referee review remain outstanding.

The reported theorem is **not** a proof that Gaussian or Eisenstein
moat walks are universally bounded for arbitrary step radius, nor
an exact classification at radius two or beyond. The finite
certificates are independently replayable integer arithmetic; the
infinite arguments are written mathematics, not a Lean formalization.
