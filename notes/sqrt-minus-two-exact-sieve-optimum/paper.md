# The exact optimal finite principal-ideal sieve obstruction is 197 in \(\mathbb Z[\sqrt{-2}]\)

A matching universal lower obstruction and six-stage exact upper certificate.
Research continuation, 8 October 2026; developed with AI assistance, not
externally refereed or presented as a first-in-literature assertion.

## 1. Definitive results and the three distinct optimizations

Put \(t=\sqrt{-2}\), write \(R=\mathbb Z[t]\), and identify its elements
\(a+bt\) with \((a,b)\in\mathbb Z^2\). Its positive multiplicative norm
is \(N(a,b)=a^2+2b^2\). Let
\[
 F_{14}=\{(\pm1,0),(0,\pm1),(\pm1,\pm1),
                      (\pm2,0),(\pm2,\pm1)\},               \tag{1.1}
\]
with independent signs in the displayed pairs. These are precisely
the fourteen lattice differences of squared norm at most six.

For any finite list \(\mathcal G\) of nonzero nonunit principal-ideal
generators, let
\[
 A(\mathcal G)=R\setminus\bigcup_{g\in\mathcal G}(g).
\]
An allowed component is a connected component of the *full lattice*
graph induced by \(A(\mathcal G)\) under \(F_{14}\), irrespective of
which vertices are irreducible. Call \(\mathcal G\) successful if all
allowed components are finite. Define the **method-optimal component
bound**
\[
 \mathfrak M_{14}(R)=\inf_{\mathcal G\ \mathrm{finite,successful}}
              \max_{C\in\pi_0(A(\mathcal G),F_{14})}|C|.
                                                                  \tag{1.2}
\]
This concerns all finite principal-ideal sieves of arbitrary scalar
period, arbitrarily many generators and arbitrary composite factors.

A finite connected configuration \(S\subset R\) is *universally
norm-admissible* if for every rational prime \(p\) there exists some
\(w_p\in(\mathbb Z/p)^2\) such that
\[
                   p\nmid N(z+w_p)\qquad(z\in S).        \tag{1.3}
\]
Set
\[
 \mathfrak A_{14}(R)=\sup\{|S|:S\text{ finite connected under }F_{14},
                       \ S\text{ universally norm-admissible}\}.
                                                                  \tag{1.4}
\]

**Theorem 1 (two exact global optima).** Both of these quantities
have the same finite and attained exact value:
\[
                    \boxed{\mathfrak M_{14}(R)
                           =\mathfrak A_{14}(R)=197}.      \tag{1.5}
\]

More concretely, one particular list of **18 irreducible generators**
\[
\begin{split}
 \mathcal G_{18}=\{&t,1\pm t,3\pm t,3\pm2t,5,\\
                  &1\pm3t,3\pm4t,5\pm3t,
                    3\pm5t,7\pm3t\}                     \tag{1.6}
\end{split}
\]
(here each \(\pm\) gives two separate elements) has scalar period
\[
     Q'=1122\cdot19\cdot5\cdot41\cdot43\cdot59\cdot67
                      =742840526010.                         \tag{1.7}
\]
Its allowed set is exactly
\[
 V_{Q'}=\{(a,b)\in\mathbb Z^2:\gcd(a^2+2b^2,Q')=1\}.
                                                                  \tag{1.8}
\]
**Every** infinite-lattice component of \(V_{Q'}\) has at most
197 vertices, and some such component has exactly 197 vertices.
No finite principal-ideal sieve can achieve a smaller maximum.

Define separately the actual irreducible-only prime graph \(G_D\):
its vertices are *irreducible elements* of \(R\), with edges of
complex Euclidean length at most \(D\). Let
\(B_D=\sup\{|C|:C\text{ is a connected component of }G_D\}\).
This need not equal (1.2), because an allowed sieve includes
composite elements as well as irreducibles.

**Theorem 2 (global prime-graph consequence).** For every real
\(\sqrt6\le D<\sqrt8\),
\[
                              \boxed{90\le B_D\le197}.   \tag{1.9}
\]
The lower witness is the exact previously certified 90-vertex
closed irreducible component, containing all fourteen prime
associates above 2,3,11,17. All **22 additional prime associates**
above 5,19,41,43,59,67 also belong to that *same* 90-vertex
component. Thus every other irreducible lies in \(V_{Q'}\) and
has a connected component of at most 197 vertices. No claim is
made that the true prime-only maximum equals 197 or 90.

Theorems 1 and 2 provide substantially different kinds of
mathematical information: Theorem 1 **settles exactly** the optimal
finite principal-ideal certificate constant and the maximal size
of universally norm-admissible connected configurations; Theorem 2
is a **new strict upper bound**, not a full classification, for
actual irreducible components.

## 2. General lower obstruction and the explicit sharp witness

We import the following *previously proved* exact result, with its
full written proof and independently replayable certificate:

**Input U ([universal 197-point obstruction](../sqrt-minus-two-universal-sieve-barrier/paper.md)).**
There is an explicit connected shape \(S_0\subset\mathbb Z^2\),
containing exactly 197 vertices, such that for every rational
prime \(p\) some integral translation modulo \(p\) avoids
\(p\mid N(z)\) at all 197 vertices. The complete shape and
45 literal admissible shifts for the primes \(p\le197\) are
included in that predecessor. For all \(p>197\), a separate
uniform analytic proof uses split/inert factorization of the
norm polynomial. A general CRT lemma then proves that every
finite principal-ideal sieve leaves a connected translate of
\(S_0\), regardless of scalar period or composite generators.

Consequently, Input U already proves
\[
                  \mathfrak A_{14}(R)\ge197,
               \qquad \mathfrak M_{14}(R)\ge197.            \tag{2.1}
\]
The purpose of this paper is to **close both inequalities from
above**, rather than to present new numerical lower-bound tests.
For clarity we reiterate the logical distinction: Input U constructs
integer points with *norms coprime to any fixed finite product of
primes after a suitable translation*. It does **not** claim the
197 points can be translated so that they are all irreducibles.

Once we construct a successful sieve with all allowed components of
size \(\le197\), we also deduce the upper bound on universally
admissible connected patterns: if such a pattern had more than
197 vertices, choose the finite set of rational primes dividing
\(Q'\). Its local admissibility and the Chinese remainder theorem
would place a connected translate entirely within \(V_{Q'}\),
contradicting the 197 upper bound. This final argument will complete
the second equality in (1.5) without further computation.

## 3. The explicit finite sieve and its ring-theoretic correctness

The norm is Euclidean in \(\mathbb Z[t]\): dividing two elements
and rounding both coefficient coordinates to the nearest integers
gives relative error norm at most \(1/4+2/4=3/4<1\).
Therefore \(R\) is a unique-factorization domain, with only
\(\pm1\) as units. Every rational prime dividing \(Q'\) is either
ramified, split, or inert, with the following complete factor list:

| Rational prime | Prime generators used in \(\mathcal G_{18}\) | Norms |
| --- | --- | --- |
| 2 | \(t\) | 2 |
| 3 | \(1+t,1-t\) | 3 each |
| 11 | \(3+t,3-t\) | 11 each |
| 17 | \(3+2t,3-2t\) | 17 each |
| 5 | \(5\) (inert) | 25 |
| 19 | \(1+3t,1-3t\) | 19 each |
| 41 | \(3+4t,3-4t\) | 41 each |
| 43 | \(5+3t,5-3t\) | 43 each |
| 59 | \(3+5t,3-5t\) | 59 each |
| 67 | \(7+3t,7-3t\) | 67 each |

All displayed norm-prime generators are irreducible, since their
norms are rational primes. The element 5 is irreducible because
\(a^2+2b^2=5\) has no integer solution, so a nonunit
factorization of rational 5 would require two factors of norm 5.
The congruence \(a^2+2b^2\equiv0\pmod5\) forces
\(a\equiv b\equiv0\pmod5\); thus the ideal \((5)\)
removes exactly the norm-zero class modulo 5. For every other
rational prime in the table the two conjugate prime-norm factors
and norm congruence give precisely the norm-zero classes.
The generator \(t\) handles the ramified norm-zero class mod 2.

**Lemma 3 (exact principal/norm equivalence).** The complement of
the union of the 18 displayed principal ideals is exactly
\(V_{Q'}\), and its common least scalar period is \(Q'\).

*Proof.* The factorization identities
\(2=-t^2\), \(3=(1+t)(1-t)\),
\(11=(3+t)(3-t)\), \(17=(3+2t)(3-2t)\), together
with analogous identities at 19,41,43,59,67 and the inert
case at 5, show that an element has norm divisible by a rational
prime \(p\mid Q'\) **if and only if** it belongs to one of the
corresponding listed prime ideals. Their union is precisely the
complement of the norm-coprime set \(V_{Q'}\).
Each split norm-\(p\) generator divides the rational integer \(p\),
and its least scalar period is exactly \(p\). The ramified \(t\)
has least scalar period 2, while the inert generator 5 has least
period 5. Their least-common multiple is (1.7).

For independent verification, `code/check_exact.py` proves by **literal
integer divisibility** that the ideal condition for every new
prime in the table agrees with \(p\mid N(a,b)\) at all
\(p^2\) residue pairs. It also checks the immutable original
prime factorization in the imported parent proof. \(\square\)

The exact constant \(Q'\) has hundreds of billions of integer
periods; enumerating its \((Q')^2\) quotient cells is unnecessary
and computationally inappropriate. We instead use the following
general complete **hierarchical component refinement principle**.

## 4. A complete iterative component-refinement theorem

The predecessor [layered modulus 19/5 theorem](../sqrt-minus-two-prime-bound-241/paper.md)
proved the general finite-component refinement lemma for two
coprime moduli, with a written inductive extension to arbitrarily
many moduli. We restate the exact interface required here.

**Lemma 4 (iterated CRT finite-component lifting).** Suppose a
\(q\mathbb Z^2\)-periodic allowed graph has a certified **complete
partition** into finite closed connected components
\(C_i+qw\), for \(w\in\mathbb Z^2\) and a finite list
\(C_1,\ldots,C_m\). Let \(p_0,\ldots,p_{s-1}\) be distinct
rational primes coprime to \(q\), and let
\(\Phi_j:\mathbb Z^2\to\{0,1\}\) be periodic modulo \(p_j\).
For a target integer threshold \(T\), one may verify that **all**
components of the refined infinite graph have size \(\le T\)
by the following exact finite recursive procedure:

1. Ignore base groups \(C_i\) with \(|C_i|\le T\).
2. At recursion depth \(j\), for every surviving finite connected
   group \(K\subseteq C_i\) and every
   \((u_j,v_j)\in\{0,\ldots,p_j-1\}^2\), compute the connected
   pieces retained by \(\Phi_j\) after translating the lattice
   points by
\[
              q\sum_{\ell=0}^{j}(u_\ell,v_\ell)
                  \prod_{r<\ell}p_r.                       \tag{4.1}
\]
3. Discard each retained component with size \(\le T\); recurse
   on every component larger than \(T\) while \(j<s-1\).
   At the final depth, require that **none** is larger than \(T\).

Exhausting these finite cases implies the claimed upper bound for
every connected component of the **infinite** graph obtained by
requiring \(\Phi_0=\cdots=\Phi_{s-1}=1\).

*Proof.* The input complete partition ensures every initial allowed
component is a translate of one explicit \(C_i\). Write its
translation vector \(w\in\mathbb Z^2\) in mixed-radix form
\[
 w=(u_0,v_0)+p_0(u_1,v_1)+\cdots+
       \left(\prod_{r=0}^{s-2}p_r\right)(u_{s-1},v_{s-1})
       +\left(\prod_{r=0}^{s-1}p_r\right)w',
\]
where \((u_j,v_j)\in\{0,\ldots,p_j-1\}^2\) and
\(w'\in\mathbb Z^2\). This representation follows from
coordinatewise Euclidean division. Every \(\Phi_j\) only depends
on its input modulo \(p_j\), so all higher digits
\(\ell>j\) contribute multiples of \(p_j\) and cannot alter
its truth value; previously imposed predicates remain unchanged
at each subsequent stage for the same reason. Thus the finite
procedure enumerates **exactly** the induced graphs encountered
by every possible translate \(C_i+qw\).

Deleting vertices from a graph cannot increase any connected
component, so discarding a piece of size \(\le T\) is always
safe. Any remaining piece is explicitly traversed at the next
stage. If no piece exceeds \(T\) after the last stage, every
component of the entire refined infinite lattice is bounded
by \(T\). This is induction on the number of added moduli.
\(\square\)

## 5. The six-stage exhaustive exact arithmetic certificate

Fix \(q=1122\), \(T=197\), and order the additional rational
prime filters by
\[
                        (p_0,\ldots,p_5)=(19,5,41,43,59,67).
                                                                  \tag{5.1}
\]
The predicates are
\(\Phi_j(a,b)=1\) if and only if
\(p_j\nmid a^2+2b^2\).
The **input** complete period-1122 partition is precisely the
6,688-family literal finite certificate from the
[sharp-period theorem](../sqrt-minus-two-sqrt6-period/paper.md),
whose 204,800 allowed representatives and full neighbor closure
were independently checked before this continuation.
The new checker pins the exact bytes of its positive certificate
by SHA256
`86f44f88613a6e7f3f4808c6611ac76bd689b1d876eea27f10cf29eb953df314`.

**Lemma 5 (exact complete six-stage computation).** Applying the
finite procedure of Lemma 4 to this immutable input and the six
filters (5.1) yields the following exact counts:

| Stage | Prime filter added | Complete shift configurations actually checked | Connected pieces still larger than 197 | Maximum size after this stage |
| ---: | ---: | ---: | ---: | ---: |
| 1 | 19 | 74,366 | 140 | 298 |
| 2 | 5 | 3,500 | 12 | 241 |
| 3 | 41 | 20,172 | 36 | 217 |
| 4 | 43 | 66,564 | 20 | 205 |
| 5 | 59 | 69,620 | 12 | 201 |
| 6 | 67 | 53,868 | **0** | **197** |

Only **206** of the 6,688 parent pieces initially have more
than 197 vertices. The first-stage enumeration covers exactly
\(206\cdot19^2=74,366\) shift configurations. Every subsequent
configuration count is exactly the number of still-oversized
connected pieces times the square of the next prime. A size-197
piece occurs at parent zero-based index 2228 with mixed-radix
translation digits
\[
   (15,0),(1,0),(9,0),(32,0),(5,0),(41,0).               \tag{5.2}
\]

*Proof by replayable finite certificate.* The independent source
`code/check_exact.py` reads only the SHA256-pinned parent integer
point lists (and the separately pinned exceptional closure).
For each relevant parent \(C_i\), it constructs the fourteen-step
adjacency from **literal integer coordinates**. It applies (4.1)
with integer arithmetic for every shift in the complete Cartesian
product of required residue digits, recomputes each induced graph
by an independent set-based connected-component traversal, and
recursively refines **every** connected piece exceeding 197.
No numerical optimization, random sampling, approximate primes,
truncated spatial window, or claims recorded by the original
C++ discovery implementation enter the checker. For each layer
it recomputes and checks the exact shift count, number of
oversized pieces, and maximum cardinality in the table. If an
oversized piece were present at the final layer, the checker
raises an explicit exception.

The program replays the **entire** computation in standard-library
Python without calling any C++ search program. It also offers
a deterministic `--part ... --parts ...` option to split parent
components for machine-independent parallel auditing; the
published full output uses one part and validates every total.
A separate adversarial test supplies malformed parent hashes,
missing exceptions, duplicate vertices and artificial oversized
last-stage pieces, and checks rejection with ordinary and
optimized Python execution. Thus the table is an exact
replayable finite proof of the stated Lemma 4 hypotheses.
\(\square\)

*Proof of the positive upper half of Theorem 1.* Lemma 3 identifies
the allowed set of the explicit 18 generators (1.6) with
\(V_{Q'}\). The inherited complete base partition and Lemma 5
verify all finite conditions in Lemma 4, with final maximum 197.
Therefore **every** component of the complete allowed infinite
lattice has at most 197 elements. The particular digit vector
(5.2) is an explicit attaining component (alternatively, Input U
already guarantees that this finite sieve has an allowed
connected translate of 197 points). Consequently
\(\mathfrak M_{14}(R)\le197\), matching (2.1).

Finally, if a universally norm-admissible connected finite pattern
had 198 or more points, applying its local translations to the
finite set of rational primes \(p\mid Q'\), and combining them
by CRT, would put a connected translate of more than 197 points
inside \(V_{Q'}\). This contradicts the just-proved global
component bound. Thus \(\mathfrak A_{14}(R)\le197\), also matching
(2.1). Both equalities in Theorem 1 follow. \(\square\)

## 6. The 22 new exceptional prime associates

A principal-ideal sieve includes composite vertices and may exclude
irreducibles dividing its generators. To transfer the sharp sieve
upper bound to the **actual prime graph**, we need to certify its
exceptional irreducible elements separately.

The [original period-1122 proof](../sqrt-minus-two-sqrt6-period/paper.md)
provides a SHA256-pinned 92-point **closed** exceptional overgraph,
with exactly 90 irreducibles forming one entire connected component
\(K_{90}\), and two nonirreducible units \(\pm1\). In particular,
every irreducible whose norm is divisible by one of
\(2,3,11,17\) already belongs to \(K_{90}\).

The six additional rational primes in (5.1) give exactly **22**
additional prime associates:
\[
 \pm5,\quad\pm(1\pm3t),\quad\pm(3\pm4t),\quad
 \pm(5\pm3t),\quad\pm(3\pm5t),\quad\pm(7\pm3t).
                                                                  \tag{6.1}
\]
The new checker independently reconstructs all these elements;
tests their norms, ideal divisibility, and the complete modular
norm-zero condition for **all \(p^2\) residues** at each new
rational prime \(p\); and verifies that all 22 lie inside the
immutable 92-point exceptional closure. All are nonunit
irreducibles and therefore belong to the previously certified
single 90-vertex prime component.

**Lemma 6 (exact prime exceptional reduction).** Every irreducible
outside \(K_{90}\) has norm coprime to \(Q'\).

*Proof.* Let \(\pi\) be an irreducible with \(p\mid N(\pi)\)
for some rational prime \(p\mid Q'\). The complete modular
factorization of \(N\) at that rational prime, from Lemma 3,
shows that one of its listed prime generators \(g\) divides
\(\pi\). Since \(g\) is a nonunit and \(\pi\) is irreducible,
they are associates. Every associate of every listed generator
lies in the inherited 90-vertex component, hence \(\pi\in K_{90}\).
Contrapositively, outside that component the norm is coprime
to all rational prime factors of \(Q'\). \(\square\)

*Proof of Theorem 2.* The known exactly 90-vertex component
certifies \(B_D\ge90\). By Lemma 6, every other prime component
lies entirely within \(V_{Q'}\); hence the finite-sieve bound
proved in Section 5 implies its cardinality is at most 197.
Since 197>90, the entire prime graph satisfies
\(B_D\le197\). No step norms in the range \((6,8)\) are represented
by \(a^2+2b^2\), so the edge set is identical for all real
\(\sqrt6\le D<\sqrt8\). This proves Theorem 2. \(\square\)

## 7. Reproduction and precise remaining questions

From this note's directory run

```sh
python3 code/check_exact.py
python3 -O code/check_exact.py
python3 code/self_test.py
python3 -O code/self_test.py
sha256sum -c SHA256SUMS
```

The run traverses **all six stages** and checks the exact final
maximum. Each invocation uses only standard-library Python
arbitrary-precision integer arithmetic. If desired, the complete
parent list can be split deterministically for independent replay
with `python3 code/check_exact.py --part i --parts 4`, for each
integer `i` between 0 and 3; the full mode validates global
counts automatically. The inherited parent proof and independent
197-point universal-pattern checker can also be replayed from
the two linked preceding notes.

The proof's trusted mathematical inputs are *explicitly stated*:
the prior full period-1122 partition and exceptional closure,
the published universally norm-admissible connected 197-point
configuration, elementary finite-sieve ring arithmetic, CRT,
and the complete iterative finite-component lemma. This note
contributes the **matching constructive upper theorem** and
simultaneously settles two different optimization problems,
rather than merely reporting an improved numerical upper bound.

The exact actual prime-only maximum \(B_D\) remains undetermined
in \([90,197]\); the statement \(\mathfrak M_{14}=197\) does
**not** imply \(B_D\ge197\), because the certifying 197-point
connected configurations need not consist of irreducible elements.
Theorem 1 also does not classify **every** sieve attaining 197,
nor all extremal universally admissible connected patterns.
The larger-step thresholds beyond \(D=\sqrt8\) remain outside
this publication.

The general periodic prime-sieve strategy is attributed to
OpenAI/math family 028, pinned public commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`, and the project's
entry-002 quadratic-order programme. The exact original
universal-obstruction and layered-refinement manuscripts are
preserved as separate disclosures. No novelty-first claim is made;
this is model-assisted traditional mathematics with exact code
checks, not external referee review or full Lean formalization.
