# A sharp radius-two transition for prime graphs in \(\mathbb Z[\sqrt{-2}]\)

Research continuation, 8 October 2026. A complete written proof with exact
replayable finite witnesses. Work prepared with AI assistance; no novelty,
priority or external peer-review claim.

## 1. Definitions and main theorems

Let \(t=\sqrt{-2}\) and \(R=\mathbb Z[t]\). Identify \(a+bt\) with
\((a,b)\in\mathbb Z^2\). Its positive norm is
\[
                         N(a,b)=a^2+2b^2.                  \tag{1.1}
\]
Irreducibles are nonzero nonunits not expressible as products of
nonunits; the graph vertices are **elements**, not classes modulo
associates. For real \(D\ge0\), the graph \(G_D\) joins distinct
irreducibles \(z,w\) if \(N(z-w)\le D^2\).

For \(2\le D<\sqrt6\), exactly ten nonzero differences are permitted:
\[
 F_{10}=\{(-2,0),(2,0)\}\ \cup\
         (\{-1,0,1\}^2\setminus\{(0,0)\}).                  \tag{1.2}
\]
Indeed, the represented positive norms below six are precisely
\(1,2,3,4\): norm five cannot be represented as \(a^2+2b^2\).
The three norm-one/norm-two/norm-three thresholds below two were
fully treated in our [preceding note](../sqrt-minus-two-sharp-moats/paper.md).

**Theorem A (complete radius-two transition).** Define
\[
\begin{aligned}
 S_+&=\{t,\ 1+t,-1+t,\ 3+t,-3+t,\ 3+2t,-3+2t\},\\
 S_-&=\overline{S_+}
       =\{-t,\ 1-t,-1-t,\ 3-t,-3-t,\ 3-2t,-3-2t\}.
\end{aligned}                                               \tag{1.3}
\]
For every real \(2\le D<\sqrt6\):

1. \(S_+\) and \(S_-\) are two **distinct connected components** of
   \(G_D\), each with exactly **seven** vertices.
2. Every other connected component has at most **two** vertices.
   The remaining possible nontrivial components are precisely those
   pairs of irreducibles, disjoint from \(S_+\cup S_-\), lying in one
   of the two types of pairs
\[
\begin{aligned}
 &\{(6k+3,3j+1),(6k+3,3j+2)\},\\
 &\{(6k-1,3j),(6k+1,3j)\},\qquad k,j\in\mathbb Z.
\end{aligned}                                               \tag{1.4}
\]
   When both elements of such a pair are irreducible, the pair is a
   component; when only one is irreducible it is isolated.
3. The seven-vertex components are the only components of size greater
   than two. Thus the **exact universal maximum** throughout the
   interval \([2,\sqrt6)\) is seven, with precisely two maximizers.

Combining with the previous note gives the following sharp phase
transition through \(\sqrt6\), the first unhandled threshold:
\[
\boxed{\max_{C\in\pi_0(G_D)}|C|=
  \begin{cases}
    1,&0\le D<1,\\
    3,&1\le D<2,\\
    7,&2\le D<\sqrt6.
  \end{cases}}                                              \tag{1.5}
\]
In particular the size jump from \(3\) to \(7\) occurs **exactly at
radius two**. The geometrically admissible norm-three directions do
not themselves introduce prime edges before this transition.

We also classify finite principal-ideal sieves for the enlarged ten-step
set. For a nonzero nonunit \(g\in R\), define its least positive scalar
period \(q(g)\) as the least positive integer divisible by \(g\) in
\(R\). For a finite nonempty generator list \(\mathcal H\), set
\(Q(\mathcal H)=\mathrm{lcm}_{g\in\mathcal H}q(g)\). The *allowed lattice
sieve graph* uses **all lattice elements** outside the union of ideals
\((g)\), with differences in \(F_{10}\). The sieve is *successful* if
all allowed connected components are finite. This is stronger than
merely bounding the components on irreducibles.

**Theorem B (optimal period and unique minimal generator list).**
For \(F_{10}\), the smallest possible common scalar period of a
successful finite principal-ideal sieve is again \(6\). Among *all*
nonempty finite lists of nonzero nonunit generators with
\(Q(\mathcal H)=6\), the sieve is successful **if and only if**
\[
          (t),\quad (1+t),\quad (1-t)                     \tag{1.6}
\]
all occur among its generator ideals. This includes arbitrary
composite generators and redundant elements. Consequently the
three-generator list \(\{t,1+t,1-t\}\) is, up to associates and
ordering, the **unique inclusion-minimal** successful list at the
sharp period, and the smallest possible number of generators is
exactly three.

For this list the entire infinite allowed lattice graph is a
disjoint union of two-vertex components. Its quotient modulo six has
exactly eight allowed residues organized into four lifted components.

**Corollary C (change in sieve complexity at radius two).** For the
eight coefficient-neighbor steps \(F_8\) (equivalently, Euclidean
radii \(\sqrt3\le D<2\)), the earlier result found two distinct
minimal two-generator lists and a third minimal three-generator list
at scalar period six. For the ten-step set \(F_{10}\) (radii
\(2\le D<\sqrt6\)), **only** the three-prime list (1.6) survives.
Thus the least scalar period stays six while the least successful
generator count rises **sharply from two to three**, and the family
of minimal solutions collapses from three lists to one.

## 2. Algebraic inputs and the norm-six sieve

The ring \(R\) is Euclidean for the norm (1.1): if
\(\alpha/\beta=x+yt\) in its quotient field, rounding \(x,y\) to
the nearest integers gives a remainder \(r\) with
\(N(r)/N(\beta)\le1/4+2/4=3/4<1\). The usual norm-Euclidean
algorithm implies unique factorization. The only units are
\(\pm1\).

The product of two coefficient pairs is
\[
 (a,b)(c,d)=(ac-2bd,ad+bc).
\]
Multiplying by the conjugate shows that a nonzero \(c+dt\) divides
\(a+bt\) **if and only if**
\[
 c^2+2d^2\mid ac+2bd,
 \qquad c^2+2d^2\mid bc-ad.                              \tag{2.1}
\]
This is the exact integer predicate used in the standalone checker.

Put \(u=1+t\), \(v=1-t\). Then
\[
         2=-t^2,\qquad 3=uv,\qquad 6\sim t^2uv,            \tag{2.2}
\]
where \(\sim\) denotes association by a unit. The three factors
\(t,u,v\) have norms \(2,3,3\) and are pairwise nonassociate
irreducibles. Their membership predicates are
\[
\begin{aligned}
 t\mid(a+bt)&\iff a\equiv0\pmod2,\\
 u\mid(a+bt)&\iff a-b\equiv0\pmod3,\\
 v\mid(a+bt)&\iff a+b\equiv0\pmod3.
\end{aligned}                                               \tag{2.3}
\]
In particular, every irreducible \(z\) with
\(\gcd(N(z),6)>1\) is associate to one of \(t,u,v\).
There are exactly six such *exceptional* irreducibles:
\[
                         E=\{\pm t,\pm u,\pm v\}.        \tag{2.4}
\]
The proof is elementary: even norm forces an even first coordinate
and hence divisibility by \(t\); norm divisible by three forces
\(a^2-b^2\equiv0\pmod3\) and hence divisibility by \(u\) or
\(v\). Irreducibility reduces that factorization to association.

All remaining irreducibles belong to the periodic **norm-six sieve**
\[
               V_6=\{(a,b)\in\mathbb Z^2:
                              \gcd(a^2+2b^2,6)=1\}.        \tag{2.5}
\]
A complete residue description is
\[
(a,b)\in V_6\iff
 \begin{cases}
 a\equiv3\pmod6,\quad b\equiv1,2\pmod3;\quad\text{or}\\
 a\equiv1,5\pmod6,\quad b\equiv0\pmod3.
 \end{cases}                                               \tag{2.6}
\]
There are only eight allowed residue pairs modulo six. This follows
from the norm being odd exactly when \(a\) is odd, and
\(N(a,b)\equiv a^2-b^2\pmod3\).

**Lemma 2.1 (exact two-point lattice decomposition).** The graph on
\(V_6\) with steps \(F_{10}\) is the disjoint union of precisely the
two-point components appearing in (1.4). Every component contains
exactly two points.

*Proof.* Each allowed point has odd \(a\), so a step changing \(a\)
by \(\pm1\) enters an even-first-coordinate point and is forbidden.
Only the steps \((0,\pm1)\) and \((\pm2,0)\) remain. For
\(a\equiv3\pmod6\), the allowed \(b\)-classes are 1 and 2 modulo
three. Each pair \((a,3j+1),(a,3j+2)\) is connected by a vertical
step; its vertical outer neighbors and both horizontal
\(\pm2\)-neighbors are forbidden by (2.6). For
\(a\equiv1,5\pmod6\), the allowed \(b\) is a multiple of three,
and the consecutive allowed odd horizontal positions form exactly
\((6k-1,3j),(6k+1,3j)\). The same inspection proves that both
outer horizontal neighbors and both vertical neighbors are forbidden.
These pairs are disjoint and exhaust (2.6), giving an analytic proof
of the full infinite partition. \(\square\)

A separate exact certificate contains the four allowed quotient
components, each of size two, and the independent checker verifies
every allowed residue and every outward neighbor. The certificate
is a *cross-check* of the preceding infinite analytic proof.

## 3. The two exceptional seven-vertex components

Define the periodic **overgraph**
\[
                       W=V_6\cup E.                      \tag{3.1}
\]
Every irreducible of \(R\) belongs to \(W\). Let \(C\) be the
union of connected components of the \(F_{10}\)-graph on \(W\)
which meet \(E\).

**Lemma 3.1 (a closed finite exceptional certificate).** Exactly
sixteen points occur in \(C\):
\[
\begin{aligned}
 C=\{ &(\pm1,0),\ (0,\pm1),\
       (\pm1,\pm1),\\
      &(\pm3,\pm1),\ (\pm3,\pm2)\}.
\end{aligned}                                               \tag{3.2}
\]
Here signs within each \((\pm a,\pm b)\) are independent. The
only *nonirreducible* points in \(C\) are the units \((\pm1,0)\).
The fourteen irreducibles induce exactly the two connected
seven-vertex sets \(S_+,S_-\) in (1.3).

*Proof.* The finite set on the right of (3.2) contains each of
the six exceptional irreducibles \(E\). For every point in the
set and every one of the ten steps, direct application of
(2.5) shows that the neighbor either belongs to this finite set
or is outside \(W\). Thus the displayed set is closed under
all **allowed infinite-graph** steps. Each of its points is
reachable from some member of \(E\), as can be read directly
from the two connected prime graphs and the two adjacent units.
Hence this set is *exactly* the closure \(C\), with no unsearched
region or coordinate cutoff.

Irreducibility of the fourteen claimed primes is checked by their
rational prime norms \(2,3,11,17\); the two units \((\pm1,0)\)
are not irreducible. All fourteen lie in the two seven-point sets
(1.3), and explicit step adjacency shows both are connected.
Their mutual separation follows from the neighbor closure and
literal step inspection. For reproducibility, `code/check_exact.py`
independently checks all 16 points, all 160 neighboring positions,
connectivity, the exceptional reachability closure, and the
irreducibility of every listed point using a **complete norm-bounded
factor test** derived from (2.1), not simply the claimed norm labels.
\(\square\)

*Proof of Theorem A.* Every irreducible belongs to \(V_6\cup E\)
by the exceptional-prime classification in Section 2. Every
irreducible component meeting \(E\) belongs to the finite closed
set \(C\), and by Lemma 3.1 those are precisely the two distinct
seven-point components \(S_+,S_-\). Any other irreducible component
lies completely within \(V_6\), and therefore has cardinality at
most two by Lemma 2.1. Moreover Lemma 2.1 identifies exactly its
possible partner in (1.4). Conversely if both points in a pair
are irreducible and the pair does not meet \(S_+\cup S_-\), no
further irreducible neighbor exists. Hence (1.4) is the complete
classification of all other possible nontrivial components.
The two seven-element sets themselves attain the maximum.
The step set stays \(F_{10}\) throughout \([2,\sqrt6)\), so this
proves the theorem for **every real radius in the interval**.
The earlier paper supplies the sharp bounds for \(D<2\), yielding
(1.5). \(\square\)

## 4. Sharp periodic-sieve existence and minimum scalar period

The factorization (2.2) implies that \(t,u,v\) have scalar
periods \(2,3,3\). Their lcm is six. A point is outside all
three principal ideals exactly when its norm is coprime to six,
by (2.3). Therefore their allowed graph is precisely the
\(V_6\) graph of Lemma 2.1, and is successful with every component
of size two. This proves **existence at period six**.

**Lemma 4.1 (maximal-norm-sieve inclusion).** For any finite nonempty
principal-ideal sieve of scalar period \(Q\), its allowed lattice
contains
\[
               V_Q=\{z:\gcd(N(z),Q)=1\}.                 \tag{4.1}
\]

*Proof.* Each generator \(g\) divides its scalar period \(q(g)\),
which divides \(Q\), so \(g\mid Q\). Thus
\(N(g)\mid Q^2\). A nonunit generator has \(N(g)>1\), so a rational
prime \(p\) divides both \(N(g)\) and \(Q\). Every multiple of
\(g\) has norm divisible by \(p\), and hence no point of \(V_Q\)
belongs to its ideal. The same holds for all generators. \(\square\)

**Lemma 4.2 (nonzero-voltage obstruction).** If \(A\subseteq
\mathbb Z^2\) is invariant under translations by \(q\mathbb Z^2\),
and a finite allowed-step walk starts at \(z\in A\) and ends at
\(z+qv\) for some nonzero \(v\in\mathbb Z^2\), then the full
graph on \(A\) has an infinite component.

*Proof.* Translate the walk repeatedly by \(qv\), producing the
distinct vertices \(z+nqv\), \(n=0,1,\ldots\), all connected
in the allowed graph. \(\square\)

**Lemma 4.3 (all smaller periods fail).** For each
\(Q=1,2,3,4,5\), the graph on \(V_Q\) has an infinite component
using steps in \(F_{10}\). Therefore no finite principal-ideal
sieve with scalar period less than six is successful.

*Proof.* Each \(V_Q\) is \(Q\mathbb Z^2\)-periodic. The vertical
line \(\{(1,b):b\in\mathbb Z\}\) lies in \(V_Q\) for
\(Q=1,2,4,5\): \(N(1,b)=1+2b^2\) is odd and never vanishes
modulo five (since two is not a quadratic residue modulo five).
For \(Q=3\), the three-step path
\[
        (0,1)\to(1,0)\to(2,0)\to(3,1)                  \tag{4.2}
\]
has norms \(2,1,4,11\), each coprime to three, and ends three
horizontal units beyond its start. Lemma 4.2 applies in each
case. Equivalently, the finite JSON file gives five explicit
indexed step paths, all independently verified against exact
norm gcd tests. Lemma 4.1 transfers each of these infinite
obstructions to **every** sieve of the corresponding scalar period.
\(\square\)

Together with the period-six construction, this proves the sharp
scalar-period assertion in Theorem B.

## 5. Complete classification of every optimal-period sieve

As \(R\) is a unique-factorization domain and
\(6\sim t^2uv\), every generator whose scalar period divides
six is associate to an element
\[
 t^{e_0}u^{e_1}v^{e_2},\qquad
 0\le e_0\le2,\quad e_1,e_2\in\{0,1\},\quad
 (e_0,e_1,e_2)\ne(0,0,0).                              \tag{5.1}
\]
There are exactly **eleven** nonunit divisor ideals. A sieve
list is equivalent to a subset of these eleven ideals:
repetition and multiplication by units do not alter its allowed
graph. Thus no nonprincipal or inaccessible ideals are silently
assumed in the classification.

The list \(\{(t),(u),(v)\}\) succeeds by Lemma 2.1.
Any larger ideal list containing all three likewise succeeds,
because deleting allowed vertices cannot create an infinite
component. It remains to exclude **all** lists omitting at least
one of the three prime ideals, including lists of composite ideals.

**Lemma 5.1 (three maximal-failure certificates).** For each
\(g\in\{t,u,v\}\), form the sieve whose list contains **all ten**
nonunit divisor ideals from (5.1) *except* \((g)\). Each of
these three maximal lists has an infinite allowed \(F_{10}\)
component.

*Proof.* The following table specifies three exact nonzero-period
walks. The ten F10 steps are indexed as
\[
\begin{array}{c|rrrrrrrrrr}
\text{index}&0&1&2&3&4&5&6&7&8&9\\\hline
\text{step}&(-2,0)&(-1,-1)&(-1,0)&(-1,1)&(0,-1)&
(0,1)&(1,-1)&(1,0)&(1,1)&(2,0).
\end{array}                                                \tag{5.2}
\]

| Missing ideal | Starting vertex | Indexed steps | Endpoint |
| --- | --- | --- | --- |
| \((t)\) | \((1,3)\) | \(7,9,7,9\) | \((7,3)\) |
| \((u)\) | \((1,0)\) | \((5,9)\) repeated six times | \((13,6)\) |
| \((v)\) | \((1,0)\) | \((4,9)\) repeated six times | \((13,-6)\) |

For each row, the independent checker constructs **all ten**
retained generators literally from the eleven exponent vectors,
and uses (2.1) to check that the start and **every intermediate
vertex** are outside every retained principal ideal. Its endpoint
comparison verifies displacement in \(6\mathbb Z^2\setminus\{0\}\).
This is finite certificate evidence for precisely the hypotheses
of Lemma 4.2; it requires neither solver correctness nor numerical
optimization. Each allowed set is six-periodic because every
generator divides six. Lemma 4.2 proves the three infinite
obstructions. \(\square\)

*Completion of Theorem B.* Let \(\mathcal H\) have scalar period
six. If it includes all three ideals \((t),(u),(v)\), it is
successful by Lemma 2.1. Otherwise it omits at least one,
say \((g)\). Since all its generator ideals are among the
other ten ideals of (5.1), its allowed graph contains as an
induced subgraph the graph allowed by the maximal ten-ideal
list omitting \((g)\). That maximal list has an infinite
component by Lemma 5.1, which remains infinite in the
superset. Hence \(\mathcal H\) is unsuccessful.

The three distinct prime ideals are therefore **individually
necessary and jointly sufficient**. This simultaneously proves
the exact inclusion-minimal classification and the sharp minimum
generator count of three, without excluding composite lists by
assumption. \(\square\)

As an additional completely independent finite diagnostic,
`code/check_exact.py` enumerates all \(2^{11}=2048\) subsets
of the eleven divisor ideals and traverses the complete
36-residue quotient graph by integer lifts, checking for nonzero
translation voltage. Exactly \(2^8=256\) subsets succeed:
those containing the three required prime ideals. This
finite enumeration is **not** used as a replacement for
Lemma 5.1 and the universal subset argument.

## 6. Exact certificates, dependencies and boundaries

The explicit `code/certificate.json` provides the finite lattice
sets and paths used in the proofs: four positive two-vertex
components covering **all eight** allowed residues; the complete
sixteen-vertex exceptional closure; three failure walks of lengths
4, 12, 12; and five lower-period walks. Every certificate is
checked by `code/check_exact.py`, which imports neither
`code/produce.py` nor a closed-source number-theoretic library.

The checker verifies the **literal** exact divisibility formula
(2.1), all finite connectedness, closure of every allowed neighbor,
unique residue coverage, exceptional reachability, and irreducibility
of all finite exceptional points by bounded exhaustive factor
tests. These finite properties imply the full unbounded claims
by the explicitly proved lifting Lemmas 4.1 and 4.2 and the
norm-six pairing Lemma 2.1. The recorded replay runs with and
without Python assertions enabled, and deliberate tampering tests
confirm malformed certificates are rejected.

This result is an additive continuation of the frozen earlier note
[Z[sqrt(-2)] small-radius graph](../sqrt-minus-two-sharp-moats/README.md),
which covers \(D<2\). The general principal-ideal approach is
inspired by OpenAI/math family 028 (pinned public commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`), and the
quadratic-order transfer in repository entry 002. Both prior
descriptions and public source attribution are preserved.

The new results do **not** classify all component sizes at
\(D=\sqrt6\) or larger, do not prove an optimal sieve period for
arbitrary larger step sets, and do not constitute a resolution of
unrelated open moat problems. The written analytic proofs are
not Lean-formalized, and human referee review or a full literature
novelty search has not been performed. No first-discovery claim
is made.
