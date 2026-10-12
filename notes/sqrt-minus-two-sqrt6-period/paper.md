# A sharp principal-sieve period jump at the norm-six threshold in the \(\mathbb Z[\sqrt{-2}]\) prime lattice

Research continuation, 8 October 2026. Complete written proof with exact
integer finite-partition and nonzero-voltage certificates; developed with AI
assistance and not claimed to be externally refereed, Lean-formalized, or
first in the literature.

## 1. Definitions and results

Let \(t=\sqrt{-2}\) and \(R=\mathbb Z[t]\); write \(a+bt\) as \((a,b)\) and
\[
                         N(a,b)=a^2+2b^2.                \tag{1.1}
\]
All step lengths are actual complex Euclidean lengths \(\sqrt{N}\).
For \(\sqrt6\le D<\sqrt8\), the integer differences with
\(0<N\le D^2\) are precisely the following **fourteen** steps:
\[
 F_{14}=\{(\pm1,0),(0,\pm1),(\pm1,\pm1),
           (\pm2,0),(\pm2,\pm1)\}.                     \tag{1.2}
\]
Signs in a parenthesized pair are independent. In fact the possible
positive step norms below eight are 1, 2, 3, 4 and 6; norm five
and norm seven have no representations by \(a^2+2b^2\).

For a nonzero nonunit \(g\in R\), define its **least positive scalar
period** \(q(g)\) as the least positive rational integer divisible
by \(g\) in \(R\). For a nonempty finite list
\(\mathcal G=(g_1,\ldots,g_k)\) put
\(Q(\mathcal G)=\operatorname{lcm}_i q(g_i)\). The principal-ideal
sieve is the graph on **every** lattice element outside
\(\bigcup_i(g_i)\), with differences in \(F_{14}\). It is called
*successful* if all its connected components are finite. This
condition is strictly stronger than considering the induced graph
on irreducibles alone.

**Theorem A (sharp period 1122).** The minimum scalar period of
any successful finite principal-ideal \(F_{14}\)-sieve is
\[
                         \boxed{1122=2\cdot3\cdot11\cdot17}. \tag{1.3}
\]
A successful explicit list of seven irreducible generators is
\[
 \mathcal G_*=(t,1+t,1-t,3+t,3-t,3+2t,3-2t).            \tag{1.4}
\]
The full lattice allowed by this list is precisely
\[
 V_{1122}=\{(a,b)\in\mathbb Z^2:
                         \gcd(a^2+2b^2,1122)=1\}.        \tag{1.5}
\]
It contains no infinite \(F_{14}\)-component. More strongly,
its components are exactly the translations of **6,688** finite
connected sets \(C_i\) under \(1122\mathbb Z^2\), with
\[
 \sum_i |C_i|=204800,\qquad
              \max_i |C_i|=\boxed{2283}.                  \tag{1.6}
\]
These are the exact component counts for **this sieve**, not a claim
that its maximum 2283 is the largest component of the prime graph.
No principal-ideal sieve of smaller scalar period can succeed,
including ones with composite generators.

Let \(G_D\) denote the graph on all **irreducible elements** of
\(R\), with edges of complex Euclidean length at most \(D\).
Elements are not quotiented by associates. Define
\(B_D=\sup\{|C|: C\text{ a connected component of }G_D\}\).

**Theorem B (effective global prime-component bound and exact
exceptional component).** For every real \(\sqrt6\le D<\sqrt8\),
\[
                          \boxed{90\le B_D\le2283}.      \tag{1.7}
\]
In fact all fourteen irreducibles dividing the rational integer
1122 (up to associates) lie in one **exactly ninety-vertex**
component \(P\), which is finite and closed in the full infinite
irreducible graph. The corresponding finite *overgraph closure* has
exactly 92 points, of which only the two units \(\pm1\) are not
irreducible. Any prime component not equal to \(P\) has at most
2283 vertices. The exact global maximum \(B_D\) may be larger
than 90; Theorem B does **not** claim to determine it.

**Corollary C (two successive sharp sieve-period phases).** The
previous [radius-two continuation](../sqrt-minus-two-radius-two/paper.md)
proves the least successful principal-sieve period for the ten
steps at \(2\le D<\sqrt6\) is **6**. Theorem A shows that when
the four norm-six steps become available at exactly
\(D=\sqrt6\), that least period jumps sharply to **1122**,
i.e. grows by the exact factor \(187\), and stays there for
\(\sqrt6\le D<\sqrt8\).

## 2. Algebraic sieve reduction

The norm (1.1) is Euclidean: write \(\alpha/\beta=x+yt\) for
\(\beta\ne0\), round each real coordinate to the nearest integer,
and obtain \(r\) with \(N(r)/N(\beta)\le3/4<1\). Thus \(R\)
is a unique-factorization domain and its units are exactly
\(\pm1\).
For \(g=c+dt\ne0\), direct conjugation gives the **exact**
divisibility rule
\[
 g\mid(a+bt)\iff
 \left\{\begin{aligned}
  c^2+2d^2&\mid ac+2bd,\\
  c^2+2d^2&\mid bc-ad.
 \end{aligned}\right.                                         \tag{2.1}
\]
The independent checker uses this two-coordinate integer predicate
rather than floating-point modular inverses.

The following factorizations are literal equalities up to units:
\[
\begin{aligned}
 2&=-t^2,\quad 3=(1+t)(1-t),\\
 11&=(3+t)(3-t),\\
 17&=(3+2t)(3-2t).
\end{aligned}                                               \tag{2.2}
\]
Their seven listed factors have rational prime norms
\[
                        2,3,3,11,11,17,17,                  \tag{2.3}
\]
and are hence irreducible. Their positive scalar periods are
respectively \(2,3,3,11,11,17,17\): in each case (2.1) shows
that the rational integer \(p=N(g)\) is divisible by \(g\),
and no positive smaller integer is. The common period of
(1.4) is therefore 1122.

**Lemma 2.1 (maximal principal-ideal norm sieve).** The complement
of the seven ideals in (1.4) is exactly the set \(V_{1122}\)
in (1.5).

*Proof.* The norm polynomial has the modular factorizations
\[
\begin{array}{rl}
 N(a,b)\equiv0\pmod2&\iff a\equiv0\pmod2,\\
 N(a,b)\equiv(a+b)(a-b)&\pmod3,\\
 N(a,b)\equiv(a+3b)(a-3b)&\pmod{11},\\
 N(a,b)\equiv(a+7b)(a-7b)&\pmod{17}.
\end{array}                                                \tag{2.4}
\]
The seven factors in (2.2) are nonassociate prime generators
above those four rational primes. A prime-norm ideal has index
\(p\) and its modular quotient is the kernel of the corresponding
linear congruence in (2.4); alternatively (2.1) verifies each
one directly. Thus an element belongs to at least one of the
seven ideals **if and only if** its norm is divisible by at
least one of the rational primes \(2,3,11,17\). This is precisely
the negation of (1.5). The independent checker also verifies
this ideal/norm equivalence for **every one of the 1,258,884
residues** modulo 1122. \(\square\)

**Lemma 2.2 (inclusion for arbitrary principal sieves).** For every
finite nonempty list \(\mathcal G\) of nonzero nonunits with common
scalar period \(Q\), its allowed lattice contains
\[
                      V_Q=\{z:\gcd(N(z),Q)=1\}.           \tag{2.5}
\]
Furthermore \(V_Q=V_{\operatorname{rad}Q}\).

*Proof.* Since \(g\mid q(g)\mid Q\) for every list member \(g\),
we have \(N(g)\mid Q^2\). As \(g\) is a nonunit,
\(N(g)>1\) and some rational prime \(p\) divides both
\(N(g)\) and \(Q\). Every multiple of \(g\) has norm divisible
by \(p\), so none of the norm-coprime points (2.5) can be
removed by its ideal. This applies to all generators.
The radical equality is a direct gcd identity. \(\square\)

## 3. Obstructing every lower scalar period

We isolate the finite-to-infinite implication independently of
the computer program.

**Lemma 3.1 (nonzero-voltage walk).** Let \(q\ge1\) and
let \(A\subseteq\mathbb Z^2\) be invariant under every
translation in \(q\mathbb Z^2\). Suppose a finite \(F\)-walk
starts at \(z\in A\), every intermediate point belongs to
\(A\), and the endpoint is \(z+qv\) with nonzero
\(v\in\mathbb Z^2\). Then the full allowed graph on \(A\)
has an infinite component.

*Proof.* Translate the finite walk by \(nqv\) for
\(n=0,1,\ldots\). Every translated path is still admissible
and consecutive paths concatenate. The resulting connected
component contains infinitely many pairwise distinct points
\(z+nqv\). \(\square\)

**Lemma 3.2 (exact exhaustive lower obstruction).** For **every**
squarefree integer \(1\le q<1122\), the norm-coprime graph
on \(V_q\) with steps \(F_{14}\) has an infinite connected
component.

*Proof with a complete finite certificate.* There are **682**
squarefree integers in this range. For each one, the file
`code/lower_cycles.json.gz` records
\[
 (q,z_q,i_1,\ldots,i_\ell),\qquad
 z_q\in\{0,\ldots,q-1\}^2,                              \tag{3.1}
\]
where the ordered step indices refer to the **fixed fourteen-step
list**, lexicographically ordered in (1.2), equivalently the explicit
list in `code/check_exact.py`. The integer checker examines each
path *point by point*: it checks the start and every intermediate
position satisfy \(\gcd(N(\cdot),q)=1\), and that the endpoint
differs from the start by a **nonzero** vector in
\(q\mathbb Z^2\). It checks uniqueness and complete equality of
the recorded index set with the mathematically defined set of
all squarefree integers \(q<1122\), not just a success count.
The longest witness contains 561 steps; all 682 actual lists
are included in the frozen compressed JSON file, without any
solver or numerical approximation.

These are therefore 682 explicit instantiations of the finite
hypotheses of Lemma 3.1. Since \(V_q\) is
\(q\mathbb Z^2\)-periodic, that lemma proves the infinite
component assertion for each of the exhaustive values of \(q\).
\(\square\)

*Proof of the lower half of Theorem A.* Suppose a successful
principal-ideal sieve had scalar period \(Q<1122\).
Then \(q=\operatorname{rad}(Q)\) is squarefree and
\(1\le q<1122\). By Lemma 2.2, the sieve leaves all points
of \(V_q\) allowed. Lemma 3.2 gives an infinite component in
that allowed subgraph, contradicting success. This rules out
**all** scalar periods below 1122, including all nonsquarefree
periods and all lists of composite ideal generators. \(\square\)

## 4. A complete positive finite partition at period 1122

**Lemma 4.1 (periodic component-lifting principle).** Let
\(A\subseteq\mathbb Z^2\) be invariant under
\(q\mathbb Z^2\), and let \(F\subset\mathbb Z^2\) be finite.
Suppose finite nonempty sets \(C_1,\ldots,C_s\subset A\)
have the following properties:

1. Reduction modulo \(q\) maps their *disjoint union*
   bijectively onto **all** allowed residue classes of \(A\).
2. For each \(x\in C_i\), each \(f\in F\) with \(x+f\in A\)
   satisfies \(x+f\in C_i\).
3. Each \(C_i\) is connected under \(F\)-adjacency.

Then the entire infinite allowed graph is the disjoint union of
translations \(C_i+qv\), for \(v\in\mathbb Z^2\), and its
component sizes are precisely the sizes \(|C_i|\), repeated
periodically. In particular it has a uniform finite component
bound \(\max_i|C_i|\).

*Proof.* Every \(z\in A\) is congruent to a unique point
\(x\) of a unique \(C_i\), so \(z=x+qv\). Periodicity and
property 2 imply that the translate \(C_i+qv\) is closed
under every allowable edge. Property 3 says that this closed
finite set is connected. Hence it is the entire connected
component of \(z\). Unique residue representatives prevent
such translated components from overlapping unless they are
the same component. \(\square\)

**Lemma 4.2 (positive certificate at 1122).** There are exactly
6688 nonempty finite connected subsets \(C_i\subset V_{1122}\)
satisfying Lemma 4.1 with \(q=1122\) and \(F=F_{14}\), such
that the total number of points is 204800 and their largest
cardinality is exactly 2283.

*Proof by exact complete finite data.* The file
`code/positive_q1122.json.gz` contains **the integer coordinates
of every point in every one of the 6688 candidate components**.
The independent checker uses that literal data and tests:

- each point's norm is coprime to 1122;
- no allowed residue is represented twice across any groups;
- all fourteen allowed neighbors of *every* listed point stay
  in the **same** group, including at the infinite lattice boundary;
- each group is connected by an independently computed traversal;
- every residue in \(\{0,\ldots,1121\}^2\) is examined and is
  present exactly once if and only if its norm is coprime to 1122.

There are \(1122^2=1,258,884\) such residue pairs. The checker
obtains, from the explicit finite point lists, **204800** allowed
residues, **6688** groups, and maximum group size **2283**, and
rejects any difference. The tests use arbitrary-precision integer
gcds and do not call or import the C++ search which produced
these lists. Thus every hypothesis of Lemma 4.1 is verified
by reproducible finite arithmetic, and that lemma converts
them to the claimed full infinite-lattice decomposition.
\(\square\)

*Completion of Theorem A.* Lemma 2.1 identifies the complement
of the seven-generator sieve (1.4) with \(V_{1122}\).
Lemma 4.2 and Lemma 4.1 prove that sieve is successful and that
its exact periodic component-size maximum is 2283. The lower
period obstruction was proved in Section 3. This completes
Theorem A. \(\square\)

## 5. Handling exceptional prime elements exactly

The prime-ideal factors of the rational integer 1122 are exactly
the seven nonassociate irreducibles in (1.4), up to sign.
Let
\[
 E=\{\pm t,\ \pm(1+t),\ \pm(1-t),\
       \pm(3+t),\ \pm(3-t),\ \pm(3+2t),\ \pm(3-2t)\}.      \tag{5.1}
\]
Thus \(|E|=14\). If an irreducible \(\pi\) has
\(\gcd(N(\pi),1122)>1\), one of the rational primes
\(2,3,11,17\) divides \(N(\pi)\). The modular factorization
(2.4) forces the corresponding nonunit factor from (2.2) to
divide \(\pi\). Since \(\pi\) is irreducible, it is an
associate of that factor. Hence **every irreducible in the
entire infinite ring** belongs to
\[
                         W=V_{1122}\cup E.                \tag{5.2}
\]

**Lemma 5.1 (exact exceptional closure).** Let \(C\) be the union
of connected components of the *overgraph* induced by
\(W\) that meet the 14 elements of \(E\). Then \(C\)
contains **exactly 92 lattice points**, including exactly
**90 irreducibles** and the two units \(\pm1\). The 90
irreducibles induce a **single connected component** in the
original \(F_{14}\) irreducible graph.

*Proof by a finite complete closure witness.* The file
`code/exceptional_closure.json` contains all 92 literal lattice
coordinates. Its independent verifier reconstructs \(E\) from
the seven explicit factors and their two signs, checks that
all fourteen exceptional elements are present, and confirms
every listed point lies in \(W\). It then tests for each point
and all fourteen steps that **every neighbor belonging to W**
is in the same 92-point finite set. Conversely a complete
traversal within that set from the fourteen exceptional roots
reaches **every** listed point. These two conditions prove the
listed set is *exactly the entire closure C*, not a truncated
search window.

For each of the 92 points, the checker performs a **complete
finite irreducibility test**. A nonunit factorization
\(z=ab\) with \(N(a),N(b)\ge2\) necessarily has some
\(2\le N(a)\le\lfloor\sqrt{N(z)}\rfloor\). Because
\(N(c+dt)=c^2+2d^2\), the checker enumerates **all** integer
coefficient pairs with norm in this range and applies the
exact divisibility criterion (2.1). This tests irreducibility
without a heuristic or floating-point primality routine.
It finds that the only nonirreducibles in \(C\) are
\((1,0)\) and \((-1,0)\), the units. Finally a separate
connectivity traversal finds that all the other **90** elements
belong to **one** connected prime subgraph. By the closure
property no prime outside \(C\) can be adjacent to this
component. \(\square\)

*Proof of Theorem B.* The finite irreducible subgraph of
Lemma 5.1 supplies a global **component of size 90**, proving
\(B_D\ge90\). Every other prime component avoids \(E\),
so by (5.2) it lies within the allowed lattice \(V_{1122}\).
Lemma 4.2 bounds each component of that lattice by 2283.
Therefore all remaining prime components have size at most
2283, and \(B_D\le2283\). The same fourteen steps remain
the only possible edges for all
\(\sqrt6\le D<\sqrt8\), giving the stated uniform interval.
The theorem makes no assertion that 90 is globally optimal.
\(\square\)

## 6. Reproduction and research boundaries

The complete exact verifier is `code/check_exact.py` (standard-library
Python only). From the directory containing this paper run:

```sh
python3 code/check_exact.py
python3 -O code/check_exact.py
python3 code/self_test.py
python3 -O code/self_test.py
sha256sum -c SHA256SUMS
```

The two large compressed JSON files include **actual finite
witnesses**, not a stored Boolean result: 682 ordered lower-period
lattice walks and 6688 complete positive finite subsets containing
204800 lattice points. The third small JSON records all 92
exceptional closure points. The checker never invokes the distinct
C++ producers; it validates integer paths, full quotient coverage,
local closure, connectivity, factorization predicates and the
relevant universal finite-index sets. Its mutation tests explicitly
reject altered paths, missing points, repeated positive
representatives and false exceptional closures even with Python
assertions disabled. The mathematical reductions behind every
finite check are stated above, so a program's success result is
*not* substituted for a proof.

The producers are published as `code/generate_negative.cpp`,
`code/generate_positive.cpp`, and
`code/generate_exceptional.py`. They are **discovery/rebuilding
utilities, not trusted theorem checkers**. The source, binary
witness data, replay logs and SHA256 hashes allow independent
reconstruction and tamper testing.

The work continues our earlier
[small-radius classification](../sqrt-minus-two-sharp-moats/README.md)
and [radius-two extension](../sqrt-minus-two-radius-two/README.md),
which are preserved independently and not rewritten. The broader
quadratic-order approach is inherited from entry 002, following
the finite periodic prime-sieve strategy of OpenAI/math family
028, pinned at public commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
We claim no first discovery or absence of prior literature.

**Open gap.** The true maximum prime-component size for the
fourteen-step graph remains somewhere in the rigorously
certified interval \([90,2283]\). Identifying it, classifying
minimum-generator lists at the sharp period 1122, and deriving
analogous certificates at the next Euclidean threshold
\(D=\sqrt8\) are further research questions. None is
silently asserted solved by the current sieve calculations.
This research note is model-assisted, not externally peer
reviewed and not fully formalized in Lean.
