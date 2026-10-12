# An exact finite-sieve–admissible-pattern minimax theorem for lattice graphs

A general CRT and finite-shape compactness duality, with a sharp
quadratic-prime-sieve application. Research note, 8 October 2026.
Model-assisted traditional proof; not externally refereed, not a
claim of historical first priority, and not fully formalized in Lean.

## 1. General framework and exact theorem

Let \(d\ge1\), and let \(F\subset\mathbb Z^d\setminus\{0\}\) be
any finite symmetric set of allowable differences. For every rational
prime \(p\), prescribe an **arbitrary** set of locally allowed
residues \(U_p\subseteq(\mathbb Z/p\mathbb Z)^d\). No norm,
unique-factorization property, probability distribution or prime
number theorem is needed in the abstract statement.

For every finite set \(P\) of rational primes, define
\[
 V_P=\{x\in\mathbb Z^d: x\bmod p\in U_p
                                   \text{ for every }p\in P\}.
                                                                  \tag{1.1}
\]
The graph on \(V_P\) is induced by differences in \(F\).
Define its **maximal component size** in the extended natural numbers:
\[
 M(P)=\sup\{|C|:C\text{ is a connected component of }V_P\},
                                                                  \tag{1.2}
\]
where \(M(P)=0\) for the empty allowed set, and \(M(P)=\infty\)
if component cardinalities are unbounded (including the presence
of an infinite component). The finite-sieve optimum is
\[
                         M_* =\inf_{P\text{ finite}}M(P). \tag{1.3}
\]
The empty set \(P=\varnothing\) is allowed; it gives the full
underlying integer lattice.

A finite nonempty **connected shape** \(S\subset\mathbb Z^d\) is
**universally locally admissible** if for every rational prime
\(p\) there exists a translation \(t_p\in(\mathbb Z/p)^d\) such
that
\[
                          t_p+(S\bmod p)\subseteq U_p. \tag{1.4}
\]
The translations \(t_p\) need not coincide for different primes.
Define
\[
 A_* = \sup\bigl(\{0\}\cup\{|S|:
         S\subset\mathbb Z^d\text{ finite, connected and satisfying (1.4)}\}\bigr).
                                                                  \tag{1.5}
\]

**Theorem 1 (exact finite periodic sieve–admissible pattern duality).**
For *every* finite symmetric lattice step set \(F\) and *every*
choice of local residue sets \((U_p)_{p\text{ prime}}\),
\[
                               \boxed{M_*=A_*}.          \tag{1.6}
\]
More strongly, if \(A_*<\infty\), the infimum in (1.3)
is **attained by one finite set of rational primes** \(P_*\):
\[
                                M(P_*)=A_*.             \tag{1.7}
\]
If \(A_*=\infty\), then every finite sieve has unbounded
component sizes. These statements include the edge case
\(A_*=0\).

**Corollary 2 (finite-sieve boundedness criterion).** There exists
*some* finite residue sieve with uniformly bounded components
if and only if there is a uniform upper bound on cardinalities
of all finite connected universally locally admissible shapes.
No stronger global compactness or infinite-dimensional
optimization hypothesis is required.

The theorem is an exact **minimax identity**, not just a one-sided
sieve obstruction. Its key inputs are two elementary finite
principles: coordinatewise CRT in the lower direction and the
finiteness of connected lattice shapes of fixed cardinality
up to translation in the upper direction.

## 2. Lower bound by CRT

**Lemma 2.1.** For every universally locally admissible connected
shape \(S\) and every finite set of rational primes \(P\),
there is an integer translation \(t\in\mathbb Z^d\) such that
\[
                                    S+t\subseteq V_P.     \tag{2.1}
\]
Consequently \(M(P)\ge|S|\), for *all* finite \(P\).

*Proof.* For each \(p\in P\), choose a translation \(t_p\)
satisfying (1.4). The moduli in \(P\) are distinct rational
primes and hence pairwise coprime. Apply the ordinary Chinese
remainder theorem independently to the \(d\) coordinates
to obtain \(t\in\mathbb Z^d\) with \(t\equiv t_p\pmod p\)
for every \(p\in P\). All points of \(S+t\) then satisfy
every local sieve condition, giving (2.1).
The set \(S+t\) is connected because the step differences
are translation invariant. All \(|S|\) distinct vertices
lie in a single allowed component, so \(M(P)\ge|S|\).
For \(P=\varnothing\), choose \(t=0\). \(\square\)

Taking the supremum over all such \(S\), then the infimum over
finite \(P\), yields the first half of (1.6):
\[
                                  A_*\le M_*.             \tag{2.2}
\]
This is the rigorous source of the observation that a
universally admissible connected pattern survives **every**
finite congruence sieve, regardless of how many primes are used.

## 3. The converse: finitely many rooted connected shapes

**Lemma 3.1 (finite connected-shape types).** Fix \(k\ge1\).
There are only finitely many \(F\)-connected sets
\(S\subset\mathbb Z^d\) with \(|S|=k\) and \(0\in S\).
Moreover every finite \(F\)-connected set with \(k\) vertices
is a translation of at least one of these rooted sets.

*Proof.* Let \(S\) be connected, with \(|S|=k\) and \(0\in S\).
Choose a spanning tree of its induced graph, rooted at zero.
Every vertex is joined to zero in this tree by a path using at
most \(k-1\) edges, each a member of the **finite** set \(F\).
Thus every vertex lies in the finite lattice set
\[
 B_{k-1}(F)=\{f_1+\cdots+f_\ell:
       0\le\ell\le k-1,\ f_i\in F\}.                  \tag{3.1}
\]
Only finitely many \(k\)-element subsets of this finite set
exist, proving the first assertion. For any connected set
\(T\) with \(|T|=k\), translate one of its vertices to zero;
the resulting rooted set is included in the finite family.
\(\square\)

**Lemma 3.2 (finite obstruction to every forbidden size).**
Suppose **no** universally locally admissible \(F\)-connected
shape has \(k\) vertices. Then there exists a **finite**
set \(P_k\) of rational primes for which the graph on \(V_{P_k}\)
has no connected component with \(k\) or more vertices.

*Proof.* Let \(\mathcal T_k\) be the finite family of rooted
\(F\)-connected \(k\)-element shapes from Lemma 3.1.
None is universally locally admissible by hypothesis.
Hence, for each \(T\in\mathcal T_k\), choose **one rational prime**
\(p_T\) for which
\[
      \text{no translation }t\in(\mathbb Z/p_T)^d
                       \text{ satisfies }t+T\subseteq U_{p_T}.
                                                                  \tag{3.2}
\]
Let \(P_k=\{p_T:T\in\mathcal T_k\}\); it is finite,
and multiple shapes may use the same obstruction prime.

Suppose a component \(C\) of \(V_{P_k}\) had at least \(k\)
vertices. Because its graph is locally finite, it contains a
finite connected vertex subset \(S\subseteq C\) of **exactly**
\(k\) vertices. For example, take the first \(k\) vertices
of a breadth-first spanning traversal from any chosen root.
Translate one vertex of \(S\) to zero, obtaining some
\(T\in\mathcal T_k\). The actual placement of \(S\) in
\(V_{P_k}\) provides a translation of \(T\) whose every point
is allowed modulo **every** \(p\in P_k\), in particular modulo
\(p_T\). This contradicts (3.2). Thus every component
has fewer than \(k\) vertices. \(\square\)

**Completion of Theorem 1.** If \(A_*=m<\infty\), then
no universally admissible connected shape has \(k=m+1\)
vertices. Apply Lemma 3.2 to obtain a finite \(P_{m+1}\)
with \(M(P_{m+1})\le m=A_*\).
The lower inequality (2.2) gives
\(M(P_{m+1})\ge A_*\), hence equality and attainment.
This includes \(m=0\), since a connected shape of size one
exists only if the local allowed sets can all be translated
nontrivially.

If instead \(A_*=\infty\), the lower bound (2.2), interpreted
in extended natural numbers, implies \(M(P)=\infty\) for
every finite \(P\). Hence \(M_*=A_*=\infty\).
The corollary follows immediately. \(\square\)

**Quantitative finite-form consequence.** The proof supplies
an existence bound on the number of distinct rational primes
needed to attain the minimum when finite:
\[
      |P_*|\le|\mathcal T_{A_*+1}|\le
                  2^{|B_{A_*}(F)|}.                         \tag{3.3}
\]
This upper bound is extremely crude and does **not** give
numerically small sieve periods or efficiently identify the
obstruction primes. But it makes the finite attainment part
of the theorem fully explicit as a finite combinatorial
selection principle.

**Example 3.3 (one-dimensional exact one-component minimax).**
Take \(d=1\), \(F=\{-1,1\}\), and choose
\(U_2=\{1\}\subset\mathbb Z/2\mathbb Z\), whereas
\(U_p=\mathbb Z/p\mathbb Z\) for all odd primes. Every
singleton is universally locally admissible: choose its parity
by translating it modulo two. No connected two-point set is
admissible modulo two, since the only possible such set is a
translate of two consecutive integers, which cover *both*
parity classes. Therefore \(A_*=1\). The finite sieve
\(P=\{2\}\) leaves precisely the odd integers, every one
isolated under the \(\pm1\) step graph. Hence \(M(P)=1\),
explicitly attaining the predicted minimum. The same theorem
also handles the degenerate cases of all local sets empty or
all local sets full.

## 4. From rational norm sieves to finite principal ideals

The abstract statement does not require algebraic rings.
To connect it with the quadratic-prime graph, let
\(R=\mathbb Z[\sqrt{-2}]\), identified with \(\mathbb Z^2\),
with positive multiplicative norm
\[
                          N(a,b)=a^2+2b^2.                \tag{4.1}
\]
For each rational prime \(p\), set
\[
 U_p=\{(a,b)\bmod p:p\nmid N(a,b)\}.                 \tag{4.2}
\]
Then \(V_P\) is precisely the norm-coprime sieve
\(\{z:\gcd(N(z),\prod_{p\in P}p)=1\}\).

A **finite principal-ideal sieve** is a finite list \(\mathcal G\)
of nonzero nonunits \(g\in R\) and its allowed lattice graph
on \(A(\mathcal G)=R\setminus\bigcup_{g\in\mathcal G}(g)\).
Let \(M_{\rm princ}\) be the infimum of maximal allowed-component
sizes over all successful finite principal-ideal sieves
(the value \(\infty\) is allowed if no successful sieve exists).

**Lemma 4.1 (norm/principal-sieve equivalence in \(\mathbb Z[\sqrt{-2}]\)).**
\[
                    M_{\rm princ}=\inf_{P\text{ finite}}M(P).
                                                                  \tag{4.3}
\]

*Proof, first direction.* Every nonzero \(g\in R\) divides a
positive rational integer: \(g\mid N(g)=g\bar g\). For any
finite nonempty generator list let
\(Q=\operatorname{lcm}_{g\in\mathcal G}q(g)\), where
\(q(g)\) is the least positive rational integer divisible
by \(g\). Each \(g\mid Q\), so
\(N(g)\mid Q^2\). Since \(N(g)>1\), some rational prime
\(p\mid Q\) also divides \(N(g)\). If \(z\in(g)\), then
\(N(g)\mid N(z)\), so \(p\mid N(z)\). Therefore the
norm-coprime set \(V_P\) for the finite set \(P\) of
rational prime divisors of \(Q\) lies entirely in
\(A(\mathcal G)\). Its induced graph cannot have larger
components than the supergraph on \(A(\mathcal G)\), hence
\(M(P)\le M(A(\mathcal G))\). Taking the infimum gives
\(\inf_P M(P)\le M_{\rm princ}\).

*Second direction.* The ring \(R\) is Euclidean in the norm:
nearest-integer rounding of both real coefficients bounds the
relative norm of the division remainder by
\(1/4+2/4=3/4<1\). Hence \(R\) is a PID and UFD.
For each rational prime \(p\), the norm-zero condition modulo
\(p\) is exactly a union of finitely many principal prime-ideal
membership conditions:

- \(p=2\): \(p\mid N(a,b)\iff a\equiv0\pmod2\), which is
  exactly the principal ideal \((\sqrt{-2})\).
- Odd inert \(p\): if \(-2\) is a quadratic nonresidue modulo
  \(p\), norm zero modulo \(p\) forces
  \(a\equiv b\equiv0\pmod p\), namely membership in \((p)\).
- Odd split \(p\): if \(r^2\equiv-2\pmod p\), then
  \(N(a,b)\equiv(a+rb)(a-rb)\pmod p\). The two linear
  kernels are prime ideals of index \(p\); since \(R\) is a
  PID they have principal generators, and the norm-zero set
  is exactly their union.

For a finite \(P\), collect all those finitely many generators
into a single principal-ideal list \(\mathcal G_P\). Its
allowed lattice set is **exactly** \(V_P\), so
\(M_{\rm princ}\le M(P)\). Taking the infimum gives the
reverse inequality, proving (4.3). \(\square\)

**Corollary 3 (universal norm-admissible connected-shape duality).**
For any finite symmetric step set \(F\) on \(\mathbb Z^2\),
\[
\boxed{\quad \inf_{\mathcal G\text{ successful finite principal-ideal sieve}}
                   M(A(\mathcal G))
 =\sup_{S\text{ finite, connected, universally norm-admissible}} |S|.
\quad}                                                       \tag{4.4}
\]
The right-hand condition means that for every rational prime
\(p\), there is a coordinate translation \(w_p\) for which
\(p\nmid N(s+w_p)\) for all \(s\in S\). If this supremum is
finite, a successful finite principal-ideal sieve **attains** it.

*Proof.* Apply Theorem 1 to (4.2), then Lemma 4.1. \(\square\)

## 5. Application: exact value 197 without a remaining duality gap

In the concrete 14-step graph for true Euclidean radii
\(\sqrt6\le D<\sqrt8\), two separately published results
supply **independent** witnesses:

- The [universal 197-point pattern](../sqrt-minus-two-universal-sieve-barrier/paper.md)
  contains 197 connected integer lattice sites and has an exact
  norm-avoiding translation modulo every rational prime.
  Its 45 small-prime shift certificates and large-prime
  split/inert lemma are independently reproducible.
- The [six-stage complete 197-sieve construction](../sqrt-minus-two-exact-sieve-optimum/paper.md)
  exhibits an explicit finite principal-ideal sieve whose
  entire infinite allowed lattice has component maximum
  exactly 197. Its SHA256-pinned 204,800-point base partition
  and every refined congruence shift are independently
  certified with exact integer traversal.

Corollary 3 now explains the matching numbers as one instance
of the exact abstract minimax duality, rather than a numerical
coincidence. Both extremal quantities are exactly 197:
\[
             A_*=M_{\rm princ}=197.                          \tag{5.1}
\]
The proof of Theorem 1 itself uses **no** special feature of
197, unique factorization, quadratic forms, or bounded-prime
arithmetic beyond the local set definition. Thus the same
finite-obstruction principle applies to many other periodic
combinatorial covering graphs and arithmetic norm sieves.

**Important distinction.** The theorem concerns *finite
principal-ideal allowed lattice graphs*, which include
composite elements. It does not assert a connected graph of
197 actual irreducible elements. The separately proved true
prime-only graph bound remains unconditional
\[
                       90\le B_D\le197.
\]
An additional [Schinzel-H conditional theorem](../sqrt-minus-two-conditional-prime-197/paper.md)
explains exactly what still blocks the unconditional prime-only
maximum and, under the unproved hypothesis, gives
\(B_D=197\) and infinitely many prime components of every
cardinality from 1 through 197. These **conditional** claims
must not be substituted for the unconditional minimax equality.

## 6. Verification, historical context and limits

The abstract minimax theorem is a **complete elementary written
proof** in Sections 2–3; it requires no finite computer search.
The ring-theoretic bridge is proved in Section 4. The concrete
197 example is replayed by the independent Python integer
checkers in the linked predecessor note directories:

```sh
(cd ../sqrt-minus-two-universal-sieve-barrier && python3 code/check.py && python3 code/check_projection.py)
(cd ../sqrt-minus-two-exact-sieve-optimum && python3 code/check_exact.py && python3 code/self_test.py)
```

Both computer certificates are frozen and versioned; this
structural theorem does not copy or modify their raw witness
files. Their full run modes, source hashes and negative controls
are documented in the linked directories. The new abstract
theorem is independently verifiable from the above finite-shape
and CRT arguments, not from a Boolean solver answer.

No claim is made that the elementary compactness principle is
historically first in the literature; a systematic novelty
assessment remains to be performed. The concrete quadratic
sieve program is part of repository entry 002 and draws on the
public Gaussian-prime work of OpenAI/math family 028 (pinned
upstream snapshot `adc7f1241b42e322a6451854ab7e4b4c146bf78a`).
The true prime-only exact maximum, extremal shapes up to
translation, best periods subject to constrained generator
numbers, and complete Lean formalization remain outside
this note.
