# Sharp principal-sieve periods and largest irreducible components in the Eisenstein lattice

Research note, 7 October 2026. Mathematical proof with finite, independently
replayable integer certificates. Not externally peer reviewed; no priority claim.

## 1. Statements

Let \(\omega^2+\omega+1=0\), with \(\omega\ne1\), and write
\(R=\mathbb Z[\omega]\). We identify \(a+b\omega\) with \((a,b)\in
\mathbb Z^2\), and use the multiplicative norm
\[
             N(a,b)=a^2-ab+b^2.
\]
An *irreducible* is a nonzero nonunit of \(R\) that has no factorization
into two nonunits. We consider graphs whose vertices are **elements**,
not classes modulo units. For a finite symmetric step set \(F\subset
\mathbb Z^2\setminus\{0\}\), two distinct vertices are adjacent when
their difference is in \(F\). Put
\[
 F_6=\{\pm(1,0),\pm(0,1),\pm(1,1)\},\qquad
 F_8=\{-1,0,1\}^2\setminus\{(0,0)\}.
\]
Thus \(F_6\) consists of the six units of \(R\). Let \(G_F\) denote
the induced graph on **all irreducibles** of \(R\), with step set \(F\).

For a nonzero nonunit \(g\in R\), its *least positive scalar period*
\(q(g)\) is the least positive integer with \(g\mid q(g)\) in \(R\).
For a nonempty finite list \(\mathcal G\), put
\(Q(\mathcal G)=\operatorname{lcm}_{g\in\mathcal G}q(g)\).
Its principal-ideal sieve graph has all lattice points \(z\) not in
\(\bigcup_{g\in\mathcal G}(g)\), with steps \(F\). A sieve is
*successful* if every connected component of this **full allowed lattice
graph** is finite. This condition is stronger than merely restricting
that graph to irreducibles.

**Theorem A (exact irreducible component maxima).** For the above graph
conventions:

1. \(G_{F_6}\) has a unique component of \(48\) vertices. Every other
   component has at most \(6\) vertices.
2. \(G_{F_8}\) has a unique component of \(132\) vertices. Every other
   component has at most \(74\) vertices.

In particular these numbers are the **exact global largest component
sizes**, not bounds obtained from a finite search radius.

**Theorem B (sharp principal-sieve periods).** Among all finite lists of
nonzero nonunit elements of \(R\) whose sieve succeeds, the minimum
common scalar period is \(6\) for \(F_6\), and \(546=2\cdot3\cdot7\cdot13\)
for \(F_8\). The respective successful lists are
\[
 \{2,1-\omega\},
 \quad
 \{2,1-\omega,3+\omega,2-\omega,4+\omega,3-\omega\}.
\]
For \(F_6\) the allowed lattice graph of the displayed sieve consists
*exactly* of isolated induced hexagonal six-cycles. For \(F_8\),
the six-generator sieve has \(93,312\) allowed residues modulo \(546\),
partitioning into \(16,536\) lifted components, the largest of size
\(74\).

**Theorem C (four generators are necessary and sufficient).** At
\(Q=546\), **every** successful principal-ideal sieve, even with
composite nonzero nonunit generators, has at least four generators.
Exactly four suffice. If the four generators are all irreducible,
then, up to associates and ordering, the four possible lists are
\[
 \{2,1-\omega,u,v\},\quad
 u\in\{3+\omega,2-\omega\},\quad
 v\in\{4+\omega,3-\omega\}.
\]
Their allowed quotient component maxima, in the order
\((u,v)=(3+\omega,4+\omega),(2-\omega,4+\omega),
(3+\omega,3-\omega),(2-\omega,3-\omega)\), are respectively
\(94,125,125,94\). We do **not** classify minimal lists allowing
composite generator elements, nor claim an optimal prime-component bound
for methods other than the stated step graphs.

## 2. Elementary arithmetic

The units are precisely
\(U=F_6\), since \(N(a,b)=1\) has exactly these six solutions. The
multiplication and conjugation rules are
\[
 (a,b)(c,d)=(ac-bd,ad+bc-bd),\qquad
 \overline{(c,d)}=(c-d,-d).
\]
Consequently \(\beta=(c,d)\ne0\) divides \(\alpha=(a,b)\) if and only if
\[
 N(c,d)\mid a(c-d)+bd,\qquad
 N(c,d)\mid bc-ad.                                      \tag{2.1}
\]
This follows simply by writing
\(\alpha/\beta=\alpha\overline\beta/N(\beta)\); it uses no floating point
and no primality oracle.

Write the six generators in the order
\[
  g_0=2,\quad g_1=1-\omega,\quad
  g_2=3+\omega,\quad g_3=2-\omega,\quad
  g_4=4+\omega,\quad g_5=3-\omega.                       \tag{2.2}
\]
Their norms are respectively \(4,3,7,7,13,13\), and their least scalar
periods are \(2,3,7,7,13,13\). Norms \(3,7,13\) are rational primes,
so \(g_1,\ldots,g_5\) are irreducible. The norm is never \(2\), as
\(N(a,b)\equiv0,1\pmod3\); hence \(2\), of norm \(4\), is also irreducible.
Direct multiplication gives
\[
 7=(3+\omega)(2-\omega),\qquad
 13=(4+\omega)(3-\omega),\qquad
 3=(1-\omega)(2+\omega).                                  \tag{2.3}
\]
The two factors of \(3\) are associates. To see that (2.2) contains all
prime divisors of the rational integer \(546\), use the familiar
Euclidean property of \(\mathbb Z[\omega]\), or simply combine (2.3)
with the irreducibility of all displayed factors. For completeness, the
norm is Euclidean: given \(z=\alpha/\beta=x+y\omega\) with real
\(x,y\), round both real coordinates independently to integers
\(m,n\). The squared norm of the error satisfies
\[
 N((x-m)+(y-n)\omega)\le\tfrac34<1
\]
because both rounding errors have absolute value at most \(1/2\).
Thus \(N(\alpha-\beta(m+n\omega))<N(\beta)\). This proves the
Euclidean algorithm, hence unique factorization and the prime property
of irreducible elements, without importing a number-theoretic theorem.

For the full six-generator list, the complement of its union of
principal ideals is exactly
\[
                     V_{546}=\{(a,b):\gcd(N(a,b),546)=1\}.
                                                                    \tag{2.4}
\]
Indeed, the four modular norm tests are
\[
 \begin{array}{ll}
 2\mid N(a,b)&\Longleftrightarrow\quad a\equiv b\equiv0\pmod2,\\
 3\mid N(a,b)&\Longleftrightarrow\quad a+b\equiv0\pmod3,\\
 N(a,b)&\equiv(a+2b)(a+4b)\pmod7,\\
 N(a,b)&\equiv(a+3b)(a+9b)\pmod{13}.
 \end{array}                                                     \tag{2.5}
\]
The ideals \((3+\omega),(2-\omega)\) are the kernels of the quotient
maps \(a+b\omega\mapsto a+4b,a+2b\pmod7\); analogously
\((4+\omega),(3-\omega)\) have kernels \(a+9b,a+3b\pmod{13}\), and
\((1-\omega)\) has kernel \(a+b\pmod3\). The kernel assertion follows
from the displayed generator belonging to the kernel and from both
ideals having index equal to the corresponding prime norm.

**Lemma 2.1 (the exceptional-irreducible lemma).** Let \(S\) be either
the two-element list \((g_0,g_1)\), with \(Q=6\), or the six-element
list (2.2), with \(Q=546\). If \(\alpha\) is irreducible and
\(\gcd(N(\alpha),Q)>1\), then \(\alpha\) is an associate of one of the
members of \(S\). There are respectively exactly \(12\) or \(36\)
such exceptional irreducible elements.

*Proof.* For each prime \(p\mid Q\), the elementary congruences (2.5)
show that \(p\mid N(\alpha)\) forces one of the listed generators over
\(p\) to divide \(\alpha\). Since the generator is a nonunit and
\(\alpha\) is irreducible, the quotient is a unit. Each generator has
six distinct associates; different generators in (2.2) are not
associates because their ideals are different (and those of equal norm
are conjugate but distinct). Hence the counts are \(6\cdot2=12\) and
\(6\cdot6=36\). \(\square\)

## 3. The six-step lattice: an analytic hexagon partition

Put
\[
 L=\{(a,b):a\equiv b\equiv0\pmod2,\ a+b\equiv0\pmod3\}.
\]
This subgroup of \(\mathbb Z^2\) has index \(12\). The six elements of
\(U=F_6\) lie in distinct cosets modulo \(L\). The condition
\(\gcd(N(a,b),6)=1\) excludes exactly the three even-even cosets and
the four \(a+b\equiv0\pmod3\) cosets, with one coset in their
intersection. Thus exactly \(12-3-4+1=6\) cosets remain, and they
are the six \(u+L\), \(u\in U\). Therefore
\[
          V_6=\bigsqcup_{c\in L}(c+U).                    \tag{3.1}
\]
For every \(c\in L\), the six vertices \(c+U\) form an induced
hexagonal cycle under the six unit steps. No permitted edge connects
two such cycles: if \(a+b\equiv1\pmod3\), then among the six candidate
steps exactly three lead to a vertex of nonzero sum modulo \(3\), and
exactly one of these three makes both new coordinates even; hence the
allowed degree is two. The same reasoning works for sum \(2\pmod3\).
Since each hexagon already supplies two neighbors per vertex, all
components of \(V_6\) are these hexagons. This proves its exact
six-vertex component bound without any computation.

The list \(\{2,1-\omega\}\) has common period \(6\) and removes the
complement of \(V_6\). To prove period minimality, let \(Q<6\).
If \(Q=1,2,4,5\), every point on the infinite unit-step line
\((a,1)\), \(a\in\mathbb Z\), has norm coprime to \(Q\): this is
immediate for \(Q=1,2,4\) from \(a^2-a+1\) being odd, and for \(Q=5\)
from the absence of roots of \(a^2-a+1\pmod5\). If \(Q=3\), use the
infinite zigzag path
\[
 (n,1-n)\to(n+1,1-n)\to(n+1,-n),\qquad n\in\mathbb Z,
\]
whose sums of coordinates are \(1,2,1\), so its norms are nonzero
modulo \(3\). In each case the maximally deleted norm sieve retains
an infinite path. Lemma 4.1 below implies that every principal sieve
of smaller scalar period fails. This proves the six-step part of
Theorem B.

## 4. Reduction of arbitrary principal sieves to norm sieves

**Lemma 4.1 (maximal sieve reduction).** Let \(\mathcal G\) be any
nonempty finite list of nonzero nonunits of \(R\) with common scalar
period \(Q\). Then its allowed lattice graph contains, as an induced
subgraph, the graph on
\[
                 V_Q=\{z\in\mathbb Z^2:\gcd(N(z),Q)=1\}.     \tag{4.1}
\]
The latter set depends only on \(\operatorname{rad}(Q)\). In particular,
if the graph on \(V_{\operatorname{rad}(Q)}\) has an infinite component,
\(\mathcal G\) cannot be successful.

*Proof.* Every \(g\in\mathcal G\) divides its scalar period and hence
\(Q\). Thus \(N(g)\mid Q^2\). Because \(g\) is a nonunit,
\(N(g)>1\), so some rational prime \(p\) dividing \(N(g)\) also
divides \(Q\). If \(z\in(g)\), then \(N(g)\mid N(z)\), and therefore
\(\gcd(N(z),Q)\ge p>1\). Hence no member of \(V_Q\) is removed by any
\((g)\). The radical assertion is elementary arithmetic. \(\square\)

We use the following elementary *voltage certificate* lemma. Here
\(V_q\) is \(q\mathbb Z^2\)-periodic because the norm is an integral
polynomial.

**Lemma 4.2 (nonzero-voltage obstruction).** Let \(q\ge1\). Suppose a
finite \(F\)-walk starts at \(z\in V_q\), all its vertices lie in
\(V_q\), and its endpoint is \(z+qv\) with
\(v\in\mathbb Z^2\setminus\{0\}\). Then the \(F\)-graph on \(V_q\)
has an infinite component.

*Proof.* Translate the given walk by \(qv,2qv,\ldots\). All translated
vertices remain in \(V_q\), and the concatenated walk contains the
distinct vertices \(z+nqv\) for every \(n\ge0\). \(\square\)

**Lemma 4.3 (sharp eight-step lower period, certified).** For every
squarefree integer \(1\le q<546\), the graph on \(V_q\) with steps
\(F_8\) has an infinite component.

*Proof.* There are exactly \(333\) such integers \(q\). For **each**
we supply an explicit start \(z_q\) and an ordered list of step
indices in `code/lower_cycles_*.json.gz`. The eight indexed steps,
in order, are
\[
 (-1,-1),(-1,0),(-1,1),(0,-1),(0,1),(1,-1),(1,0),(1,1).
\]
The independent checker `code/check.py` evaluates each integer norm,
confirms \(\gcd(N(z),q)=1\) at the start and after *every* listed
step, and checks that the endpoint differs from the start by a
**nonzero** vector in \(q\mathbb Z^2\). It also checks that the set of
indices \(q\) in the files is precisely the set of squarefree integers
in \([1,545]\), with no duplication. The longest walk has \(594\)
steps. Each recorded integer path is a direct finite witness for the
hypotheses of Lemma 4.2, so that lemma proves the assertion for every
listed \(q\). The finite data and the elementary checker make the
enumeration a replayable proof certificate, not a numerical sample.
\(\square\)

*Proof of the eight-step minimal-period claim in Theorem B.* If a
principal-ideal sieve had common scalar period \(Q<546\), then
\(q=\operatorname{rad}(Q)\) would be a squarefree integer below \(546\).
Lemmas 4.1 and 4.3 force an infinite allowed component. Section 5
constructs a successful sieve with \(Q=546\), proving optimality.
\(\square\)

## 5. A finite partition certificate for the successful eight-step sieve

For each of the masks
\[
                    63,\quad23,\quad27,\quad39,\quad43,
\]
we define a \(546\)-periodic allowed set as follows. The mask bits
\(1,2,4,8,16,32\) select the generators \(g_0,\ldots,g_5\) in
(2.2). A point \((a,b)\) is allowed exactly when it satisfies every
selected condition from the following table:

| Bit | Generator | Required allowed condition |
| --- | --- | --- |
| 1 | \(2\) | not \(a\equiv b\equiv0\pmod2\) |
| 2 | \(1-\omega\) | \(a+b\not\equiv0\pmod3\) |
| 4 | \(3+\omega\) | \(a+4b\not\equiv0\pmod7\) |
| 8 | \(2-\omega\) | \(a+2b\not\equiv0\pmod7\) |
| 16 | \(4+\omega\) | \(a+9b\not\equiv0\pmod{13}\) |
| 32 | \(3-\omega\) | \(a+3b\not\equiv0\pmod{13}\) |

Mask \(63\) specifies precisely \(V_{546}\) by (2.5). The other four
masks give the four-generator sieves in Theorem C.

**Lemma 5.1 (finite partition verification principle).** Let \(A\)
be a \(Q\mathbb Z^2\)-periodic set of integer lattice points with a
finite step set \(F\). Suppose finitely many nonempty finite subsets
\(C_1,\ldots,C_t\subset A\) have these properties:

1. Reduction modulo \(Q\) maps their disjoint union bijectively onto
   all allowed residue classes of \(A\).
2. For every \(z\in C_i\) and \(f\in F\), if \(z+f\in A\), then
   \(z+f\in C_i\).

Then every component of the infinite graph on \(A\) has at most
\(\max_i|C_i|\) points. If each \(C_i\) is connected, its integer
translates by \(Q\mathbb Z^2\) are exactly the components.

*Proof.* Given \(z\in A\), exactly one \(w\) in the finite union
has the same residue modulo \(Q\). Hence \(z=w+Qv\) for some
\(v\in\mathbb Z^2\). Periodicity and (2) show that
\(C_i+Qv\) containing \(z\) is closed under all allowed steps.
Thus the component through \(z\) is contained in this finite set.
Connectivity makes containment equality. Property (1) prevents
unintended overlap between distinct translated sets. \(\square\)

**Lemma 5.2 (endpoint certificates).** For each of the five masks,
the corresponding compressed file `code/endpoint_MASK.json.gz`
contains explicit finite sets satisfying both hypotheses of
Lemma 5.1 for \(Q=546\) and \(F=F_8\), with every set connected.
Their exact data, rechecked by the independent verifier, are:

| Mask | Allowed residues | Components modulo 546 | Largest component |
| ---: | ---: | ---: | ---: |
| 63 | 93,312 | 16,536 | 74 |
| 23 | 117,936 | 4,368 | 94 |
| 27 | 117,936 | 4,368 | 125 |
| 39 | 117,936 | 4,368 | 125 |
| 43 | 117,936 | 4,368 | 94 |

*Proof.* These are explicitly supplied **finite integer sets**, not
solver-reported scalar outcomes. For each set the checker tests every
point's modular membership, tests all eight outward neighbors for
closure, and checks connectivity. It verifies that each allowed
residue \((a,b)\in\{0,\ldots,545\}^2\) occurs exactly once across the
sets, and every forbidden residue occurs zero times. The verifier
calculates each displayed component size from the supplied points.
The two local hypotheses of Lemma 5.1 are therefore true for the
exhaustive finite residue domain. Lemma 5.1 converts the finite
certificates to the infinite-lattice assertions. \(\square\)

The six generators of mask \(63\) have common scalar period \(546\),
so Lemma 5.2 closes the existence direction in Theorem B.

**Lemma 5.3 (prime replacement at the optimal scalar period).**
Let \(R\) be a unique-factorization domain in which each
nonzero element divides some positive rational integer. Fix any
translation-invariant step set and a successful finite principal-ideal
sieve \(\mathcal G=\{g_1,\ldots,g_k\}\). For each \(j\), choose
an irreducible factor \(\pi_j\mid g_j\). Then the list
\(\mathcal P=(\pi_1,\ldots,\pi_k)\) is successful and
\(Q(\mathcal P)\mid Q(\mathcal G)\). If
\(Q(\mathcal G)=Q_0\) is the least successful scalar period
among all principal sieves, then \(Q(\mathcal P)=Q_0\).
Consequently the minimum number of generators among successful
sieves at the optimal period is attained by an irreducible-generator
sieve, even if composite generators were originally permitted.

*Proof.* Divisibility gives
\((g_j)\subseteq(\pi_j)\). Consequently the allowed lattice points
for \(\mathcal P\) form a subset of those for \(\mathcal G\).
Passing to an induced subgraph cannot create an infinite connected
component when all original components are finite, so
\(\mathcal P\) is successful. Because
\(\pi_j\mid g_j\mid q(g_j)\), the least scalar period
\(q(\pi_j)\) divides \(q(g_j)\): divide the latter by
\(q(\pi_j)\) with remainder in \(\mathbb Z\), and use the
minimality of \(q(\pi_j)\) for the zero remainder. Taking least
common multiples gives
\(Q(\mathcal P)\mid Q(\mathcal G)\).
If \(Q(\mathcal G)=Q_0\), minimality forces
\(Q(\mathcal P)\ge Q_0\), proving equality.
The construction uses at most the same number of generators;
duplicate prime factors can be discarded without affecting the
generated sieve. \(\square\)

*Proof of Theorem C.* By Lemma 5.3, to obtain a lower bound
on the number of generators at the optimal period \(546\),
it suffices to consider irreducible generators.
At period \(546\), any irreducible generator
\(g\) divides the rational integer \(546\). By (2.2)--(2.3) and the
Eisenstein unique-factorization property it is an associate of one
of the six \(g_i\). If \(g_0=2\) is omitted, all retained prime ideals
are contained in the maximal norm sieve with period
\(3\cdot7\cdot13=273\); Lemma 4.3 for \(q=273\) forbids success.
Omitting \(g_1=1-\omega\) is excluded by \(q=2\cdot7\cdot13=182\).
If both \(g_2,g_3\) are omitted, \(q=2\cdot3\cdot13=78\) excludes
success, and if both \(g_4,g_5\) are omitted, \(q=2\cdot3\cdot7=42\)
does so. Hence any successful list requires \(g_0,g_1\), at least one
of \(g_2,g_3\), and at least one of \(g_4,g_5\). It uses at least
four prime generators, and a four-generator list must be one of the
four displayed in Theorem C. Their masks are respectively
\(23,27,39,43\); each is successful by Lemma 5.2.
Lemma 5.3 extends the four-generator lower bound from prime lists
to arbitrary composite lists. This proves Theorem C. \(\square\)

**Corollary 5.4 (two generators are optimal for the six-unit sieve).**
Among all successful principal sieves of optimal scalar period \(6\),
at least two generators are necessary, even if composites are
allowed. The pair \(\{2,1-\omega\}\) attains the bound.

*Proof.* By Lemma 5.3, any one-generator successful sieve at the
optimal period \(6\) could be replaced by a one-generator
irreducible sieve of period \(6\). But an irreducible divisor
of \(6\) is associate to either \(2\), of scalar period \(2\),
or \(1-\omega\), of scalar period \(3\). No such generator has
period \(6\). The two-generator example was proved successful
in Section 3. \(\square\)

## 6. Exact largest components of irreducibles

For \((Q,F)=(6,F_6)\) and \((546,F_8)\), let \(E_Q\) denote the finite
set of exceptional irreducibles in Lemma 2.1. Consider the graph on
\[
                          W_Q=V_Q\cup E_Q.
\]
All irreducibles belong to \(W_Q\), but not all vertices of \(W_Q\)
are irreducible. Define the *exceptional closure* \(C_Q\) to be the
union of all graph components of \(W_Q\) that meet \(E_Q\).

**Lemma 6.1 (closure and primality certificates).** The files
`code/exceptional_closure_6.json.gz` and
`code/exceptional_closure_8.json.gz` contain exact finite point sets
\(C_6,C_{546}\) with
\[
 \begin{array}{c|c|c|c|c}
 Q & |E_Q| & |C_Q| & |C_Q\cap\mathrm{Irr}(R)|
   & \text{components on irreducibles in }C_Q\\ \hline
 6 &12&54&48&1\\
 546&36&138&132&1
 \end{array}                                                      \tag{6.1}
\]
In both cases the **only six nonirreducible points** in the closure
are the six units \(U\).

*Proof.* The independent checker first constructs \(E_Q\) from the
explicit generators and all six units by exact Eisenstein
multiplication. It checks that the listed finite \(C_Q\) contains
all \(E_Q\), is reachable from \(E_Q\) within its listed points,
and has the following closure property: whenever \(x\in C_Q\) and
\(x+f\in W_Q\) for \(f\in F\), then \(x+f\in C_Q\).
Therefore the listed set is **exactly** the union of components of
\(W_Q\) touching \(E_Q\), not a truncated spatial search.

Next, for every point \(\alpha\in C_Q\), the checker performs a
complete finite irreducibility test, independently of the generator:
if \(\alpha=\beta\gamma\) with both factors nonunits, the
multiplicativity of the positive integral norm implies that at least
one factor satisfies
\[
                   2\le N(\beta)\le\lfloor\sqrt{N(\alpha)}\rfloor.
\]
For \(N(c,d)\le M\), the inequality
\(N(c,d)\ge\tfrac34\max\{c^2,d^2\}\) bounds both coordinates;
the checker enumerates *all* such pairs \((c,d)\) and applies the
exact divisibility criterion (2.1). This tests reducibility without
a probabilistic integer-prime test or any external algebra package.
The only failures of irreducibility are exactly the six units.
Finally it checks that all \(48\), respectively all \(132\),
irreducibles induce a connected graph under the stated steps. This
establishes all entries of (6.1). \(\square\)

*Proof of Theorem A.* By Lemma 2.1 every irreducible is either in
\(E_Q\) or in \(V_Q\). Every irreducible component that meets
\(E_Q\) lies in the finite closure \(C_Q\). Lemma 6.1 proves that
all exceptional irreducibles belong to one connected component,
containing exactly \(48\) or \(132\) irreducibles, respectively;
no additional irreducible can join it by the closure property.
Any irreducible component **not** meeting \(E_Q\) lies entirely
in \(V_Q\) and is therefore contained in one of its allowed
components. Their maximum sizes are \(6\) by Section 3 and \(74\)
by Lemma 5.2. Since \(48>6\) and \(132>74\), the exceptional
components are the unique maxima and attain their asserted exact
sizes. \(\square\)

## 7. Reproduction, scope and dependencies

The finite claims above have a human-readable reduction to local
integral predicates: membership, adjacency, norm, residues,
divisibility, and connectedness. Their raw finite witnesses are
included, not merely hashes or the output of a search solver.
The file `code/generate.py` is a nontrusted deterministic producer;
`code/check.py` is a separate verifier that **does not import the
producer**. It uses only the Python standard library and integers.
Run from this note's directory:

```sh
python3 code/check.py
python3 -O code/check.py
```

The second invocation tests that all verification decisions remain
active under Python's optimization flag (the checker raises explicit
exceptions rather than using `assert`). Both calls should end with
`ALL EXACT CERTIFICATES VERIFIED`. The derivation of the irreducibility
test and the lifting lemmas above explain exactly why these finite
checks imply the infinite conclusions.

The chosen problem and periodic-sieve strategy are motivated by the
public OpenAI/math Gaussian-prime result (family 028, pinned upstream
commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`) and the
existing mxym/math manuscript 002 on quadratic orders, especially its
Gaussian \(F_8\) endpoint-period verification. This note treats a
different Euclidean quadratic ring and supplies its own proofs and
integer witnesses. It is not a claim to have resolved a previously
unsettled worldwide priority question. It does not prove similar
exact maxima in arbitrary quadratic orders, for other step sets, or
optimality among nonperiodic sieves. The analytic reductions remain
ordinary written mathematics; the finite arithmetic portions are
exactly replayed, not formalized in Lean. Independent human peer
review and systematic literature comparison have not yet occurred.
