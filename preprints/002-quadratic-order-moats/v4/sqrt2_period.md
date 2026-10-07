# Sharp principal-sieve period in \(\mathbb Z[\sqrt2]\)

**Supplement to entry 002 version 4 — 7 October 2026.**

This note gives the real-quadratic counterpart of the Gaussian period
optimality theorem in the main version-4 note. For the eight-neighbor
coefficient step set
\[
 F_8=\{-1,0,1\}^2\setminus\{(0,0)\}
\]
in the coefficient lattice of
\[
 R=\mathbb Z[\sqrt2],
\]
the smallest common scalar period of any successful finite principal-ideal
periodic sieve is exactly
\[
 \boxed{14}.
\]
At this sharp period a successful sieve needs at least two generators. With
exactly two generators, there are precisely two possibilities up to
associates and reordering:
\[
 \boxed{\{\sqrt2,\,3+\sqrt2\}},
 \qquad
 \boxed{\{\sqrt2,\,3-\sqrt2\}}.
\]

The positive endpoint is the version-3 certificate. All lower-period and
endpoint-rigidity failures are supplied here as exact nonzero-voltage walks.

## 1. Scalar periods and prime ideals

Write
\[
 \alpha=a+b\sqrt2,\qquad
 N(\alpha)=a^2-2b^2.
\]
Version 3 proves that the least positive scalar period of a nonzero nonunit
\(\alpha\) is
\[
 t(\alpha)
 =
 \frac{|a^2-2b^2|}{\gcd(|a|,|b|)}.
 \tag{1.1}
\]
Thus
\[
 t(\alpha)R\subseteq(\alpha),
 \qquad
 \alpha\mid t(\alpha)
 \quad\text{in }R.
 \tag{1.2}
\]

The ring \(R\) is a Euclidean domain, hence a PID and UFD. For the rational
primes relevant below the factorization is explicit:
\[
 (2)=(\sqrt2)^2,
 \tag{1.3}
\]
\[
 (7)=(3+\sqrt2)(3-\sqrt2),
 \tag{1.4}
\]
while \(3,5,11,13\) remain prime in \(R\). Equivalently,
\(X^2-2\) is irreducible modulo \(3,5,11,13\) and splits modulo \(7\).

For a squarefree positive integer \(q<14\), let
\(\mathcal P_R(q)\) contain all prime ideals above the rational primes
dividing \(q\). Thus:

- above \(2\): \((\sqrt2)\);
- above \(7\): \((3+\sqrt2)\) and \((3-\sqrt2)\);
- above \(3,5,11,13\): the inert ideals \((p)\).

Put
\[
 A_{\max,R}(q)
 =
 R\setminus\bigcup_{\mathfrak p\in\mathcal P_R(q)}\mathfrak p.
 \tag{1.5}
\]

### Lemma 1.1. Radical domination in \(\mathbb Z[\sqrt2]\)

Let \(\mathcal G\) be a finite list of nonzero nonunits in \(R\), let
\[
 Q=\operatorname{lcm}_{\alpha\in\mathcal G}t(\alpha),
 \qquad q=\operatorname{rad}Q,
\]
and let
\[
 A(\mathcal G)
 =
 R\setminus\bigcup_{\alpha\in\mathcal G}(\alpha).
\]
Then
\[
 \boxed{A_{\max,R}(q)\subseteq A(\mathcal G).}
 \tag{1.6}
\]

**Proof.**
Fix \(\alpha\in\mathcal G\) and choose a prime element
\(\pi\mid\alpha\). By (1.2),
\[
 \pi\mid t(\alpha).
\]
The prime ideal \((\pi)\) lies over a unique rational prime \(p\), so
\[
 (\pi)\cap\mathbb Z=(p).
\]
Because the rational integer \(t(\alpha)\) belongs to \((\pi)\),
\[
 p\mid t(\alpha),
\]
hence \(p\mid q\). Moreover
\[
 (\alpha)\subseteq(\pi).
\]
Taking unions over the generator list gives (1.6). \(\square\)

Consequently, an infinite \(F_8\)-walk in the maximal prime avoiding set
survives in every principal-generator avoiding set having the same period
radical.

## 2. Exact exclusion of every period below 14

### Proposition 2.1. Lower-period obstruction

For every squarefree
\[
 q<14,
\]
the \(F_8\)-graph on \(A_{\max,R}(q)\) has an infinite connected component.

The complete list of radicals is
\[
 1,2,3,5,6,7,10,11,13.
 \tag{2.1}
\]
For each value, code/sqrt2_period_endpoint.json stores a finite walk whose
projection modulo \(q\) is closed but whose total displacement is
\[
 qv,\qquad v\in\mathbb Z^2\setminus\{0\}.
\]
The periodic translates therefore concatenate to an infinite walk.

The checker reconstructs the list (2.1), the prime ideals in (1.3)--(1.4)
and the inert cases, every allowed residue, every \(F_8\) step and every
nonzero voltage using integer arithmetic only.

### Theorem 2.2. Minimal period

If a finite principal-generator \(F_8\) sieve in
\(\mathbb Z[\sqrt2]\) has only finite avoiding components, then
\[
 \boxed{Q\ge14.}
 \tag{2.2}
\]
The bound is attained by
\[
 \{\sqrt2,3+\sqrt2\},
 \tag{2.3}
\]
and, by conjugation, also by
\[
 \{\sqrt2,3-\sqrt2\}.
 \tag{2.4}
\]

**Proof.**
If \(Q<14\), then \(q=\operatorname{rad}Q<14\). Lemma 1.1 places
\(A_{\max,R}(q)\) inside the original avoiding set, while Proposition 2.1
gives an infinite component there, contradiction.

For attainment, version 3 supplies a complete quotient potential for
(2.3), with period \(14\). The coefficient conjugation
\[
 a+b\sqrt2\longmapsto a-b\sqrt2
\]
preserves \(F_8\), sends \((\sqrt2)\) to itself up to a unit, and interchanges
the two norm-seven prime ideals, proving (2.4). \(\square\)

## 3. Rigidity of the two-generator endpoint

Let
\[
 \mathcal P_{14}
 =
 \{(\sqrt2),(3+\sqrt2),(3-\sqrt2)\}.
\]
Among its subsets of size at most two, exact quotient checking gives:

- \(\{(\sqrt2),(3+\sqrt2)\}\): successful;
- \(\{(\sqrt2),(3-\sqrt2)\}\): successful;
- every other subset: a nonzero-voltage failure.

There are five failed subsets in total: the empty set, the three
singletons, and the pair of the two conjugate norm-seven ideals.

The divisor-ideal range at period \(14\) is also finite and exact. From
\[
 14=(\sqrt2)^2(3+\sqrt2)(3-\sqrt2)
 \tag{3.1}
\]
and unique factorization of ideals, the divisors of \((14)\) up to
associates are indexed by
\[
 e_2\in\{0,1,2\},
 \qquad e_+,e_-\in\{0,1\}.
\]
There are \(3\cdot2\cdot2=12\) divisor ideals, exactly 11 of them nonunit.

### Proposition 3.1. Proper-subideal failures

Take either successful prime pair in (2.3)--(2.4). Replace either one of its
two prime ideals by any proper nonunit divisor ideal of \((14)\) contained
in that prime ideal, leaving the other prime ideal unchanged. Every such
replacement has an infinite \(F_8\) avoiding component.

There are exactly 24 replacement cases. The exact certificate supplies a
nonzero-voltage walk for each.

### Theorem 3.2. Two-generator endpoint classification

Let \(\mathcal G\) be a successful principal-ideal \(F_8\) sieve in
\(\mathbb Z[\sqrt2]\) with common scalar period \(14\). Then
\[
 |\mathcal G|\ge2.
\]
If \(|\mathcal G|=2\), then up to associates and reordering,
\[
 \boxed{
 \mathcal G=\{\sqrt2,3+\sqrt2\}
 \quad\text{or}\quad
 \mathcal G=\{\sqrt2,3-\sqrt2\}.}
 \tag{3.2}
\]

**Proof.**
For each generator \(\alpha\), choose a prime divisor \(\pi\mid\alpha\).
By Lemma 1.1 the prime ideal belongs to \(\mathcal P_{14}\), and replacing
\((\alpha)\) by \((\pi)\) only deletes additional vertices. Thus a
successful one-generator sieve would produce a successful prime singleton,
contrary to the exact subset classification. Hence at least two generators
are required.

Now suppose there are exactly two. Replacing both by chosen prime divisors
produces a successful prime subset of size at most two. The exact
classification forces this pair to be one of
\[
 \{(\sqrt2),(3+\sqrt2)\},
 \qquad
 \{(\sqrt2),(3-\sqrt2)\}.
 \tag{3.3}
\]

Relabel the original generators so that
\[
 (\alpha_j)\subseteq(\pi_j)
\]
for the corresponding two primes in (3.3). Since
\(t(\alpha_j)\mid14\) and \(\alpha_j\mid t(\alpha_j)\), each
\(\alpha_j\) divides \(14\). Hence its ideal occurs among the 11 nonunit
divisor ideals from (3.1).

If one containment were strict, enlarge the other original ideal to its
prime ideal and retain this proper subideal. The resulting avoiding set is
a subset of the original one. Proposition 3.1 gives an infinite component
in that smaller set, hence also in the original set, contradiction. Thus
both containments are equalities, proving (3.2). \(\square\)

## 4. Exact replay

The certificate package contains:

- 9 lower-period nonzero-voltage witnesses;
- all 11 nonunit divisor ideals of \((14)\);
- 5 failed prime-subset witnesses;
- 24 proper-subideal replacement witnesses.

There are 38 failure witnesses in total, comprising 464 stored \(F_8\)
steps; the longest witness has 14 steps.

Run from the v4 directory:

~~~sh
python3 code/check_sqrt2_period.py
python3 -O code/check_sqrt2_period.py
~~~

The reports are byte-identical. The positive endpoint is independently
replayed from the historical version-3 sqrt2_eight_steps.json certificate.
That replay gives
\[
 Q=14,\qquad
 |A/Q\mathbb Z^2|=84,\qquad
 B=6,
\]
and the inherited conservative irreducible-component bound
\[
 351232.
\]

No floating-point comparison, random search or solver output is a proof
dependency.

## 5. Scope

The theorem classifies the scalar-period optimum and the two-generator
sharp endpoint inside the finite principal-ideal periodic-sieve framework.
It does not claim that period 14 is forced by every possible proof of the
\(\mathbb Z[\sqrt2]\) moat theorem, nor that 351232 is the true optimal
irreducible-component size.

No novelty, priority, external-referee or proof-assistant-formalization
claim is made.
