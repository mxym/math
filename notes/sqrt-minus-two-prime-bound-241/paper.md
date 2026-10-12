# Layered congruence refinement for prime-component bounds in \(\mathbb Z[\sqrt{-2}]\)

An effective improvement at the norm-six step threshold.
Research note, 8 October 2026; AI-assisted, with independently replayable
integer verification, not externally refereed.

## 1. Result and precise scope

Let \(t=\sqrt{-2}\), \(R=\mathbb Z[t]\), and use the norm
\(N(a+bt)=a^2+2b^2\). Let \(G_D\) be the graph whose vertices are
**all irreducible elements** of \(R\) (not associate classes),
joining distinct elements when their actual Euclidean distance
is at most the positive real number \(D\). Write
\[
 B_D=\sup\{|C|:C\text{ is a connected component of }G_D\}.
\]
For \(\sqrt6\le D<\sqrt8\) its fourteen possible steps are precisely
\[
 F_{14}=\{(\pm1,0),(0,\pm1),(\pm1,\pm1),
                (\pm2,0),(\pm2,\pm1)\},                 \tag{1.1}
\]
with pair signs independent.

Our [preceding sharp-period proof](../sqrt-minus-two-sqrt6-period/paper.md)
established the complete finite-component partition of
\(V_Q=\{(a,b):\gcd(a^2+2b^2,Q)=1\}\) for
\(Q=1122\), with \(6688\) finite components of maximum
size \(2283\). It also proved an **exactly 90-vertex closed
irreducible component** containing all prime factors of 1122.
The predecessor obtained \(90\le B_D\le2283\).

**Theorem 1 (layered 19/5 improvement).** For every real
\(\sqrt6\le D<\sqrt8\),
\[
                         \boxed{90\le B_D\le241}.       \tag{1.2}
\]
In particular, **every irreducible component outside the known
90-vertex component has at most 241 vertices**. The upper-bound
constant comes from a complete deterministic integer certificate,
not from sampling primes in a finite coordinate window.

Moreover, the **refined norm-coprime lattice sieve**
\[
 A=\{(a,b)\in\mathbb Z^2:
                     \gcd(a^2+2b^2,1122\cdot5\cdot19)=1\} \tag{1.3}
\]
has full infinite-lattice connected components of size at most
**241**, and some component has size **exactly 241**.
The latter sharpness assertion concerns *this sieve*, not the
irreducible-only graph, whose exact largest component remains
unresolved.

## 2. Reusable hierarchical periodic-component lemma

**Lemma 2 (iterated finite-component sieve refinement).** Let
\(F\subset\mathbb Z^2\) be a finite symmetric step set, and let
\(A\subset\mathbb Z^2\) be periodic under translations by
\(q\mathbb Z^2\). Suppose explicit finite connected sets
\(C_1,\ldots,C_m\subset A\) give one representative modulo
\(q\) for every allowed residue, and are **closed under all
allowed \(F\)-steps**. Thus the entire infinite graph on \(A\)
consists of the translates \(C_i+qv\), \(v\in\mathbb Z^2\).

Let \(p_1,p_2\) be distinct rational primes coprime to \(q\),
and let \(P_k:\mathbb Z^2\to\{0,1\}\) be any predicate invariant
under translations by \(p_k\mathbb Z^2\). Define the refined
allowed set
\[
 A'=\{z\in A:P_1(z)=P_2(z)=1\}.
\]
Fix an integer threshold \(T\). To prove that every connected
component of the infinite graph on \(A'\) has at most \(T\)
vertices, it suffices to perform these **finite** checks:

1. Ignore every base component \(C_i\) with \(|C_i|\le T\).
2. For each remaining \(C_i\) and each
   \(u\in\{0,\ldots,p_1-1\}^2\), find the connected
   components of the induced graph on
   \(\{x\in C_i:P_1(x+qu)=1\}\). Ignore every such
   first-stage component with at most \(T\) vertices.
3. For each first-stage component \(K\) having more than
   \(T\) vertices, and for each
   \(v\in\{0,\ldots,p_2-1\}^2\), verify that all connected
   components of the graph induced on
\[
       \{x\in K:P_2(x+qu+qp_1v)=1\}                 \tag{2.1}
\]
   contain at most \(T\) vertices.

These finite tests imply the desired global bound on \(A'\).
The argument generalizes inductively to arbitrarily many
pairwise coprime moduli, pruning a component as soon as its size
falls below the desired threshold.

*Proof.* Every allowed point \(z\in A\) is in a unique translate
\(C_i+qw\). Write the translation vector
\(w=u+p_1v+p_1p_2r\), with
\(u\in\{0,\ldots,p_1-1\}^2\),
\(v\in\{0,\ldots,p_2-1\}^2\) and
\(r\in\mathbb Z^2\). Since \(P_1\) is periodic modulo
\(p_1\), the allowed part of \(C_i+qw\) under the first
predicate is a translated copy of the first-stage graph for
\((i,u)\). Any connected component of \(A'\) stays inside
this graph because the original \(C_i+qw\) was already
closed. Its first-stage connected component \(K\) is finite.
If \(|C_i|\le T\) or \(|K|\le T\), further deletions cannot
increase its size. Otherwise the second predicate on this
translate, modulo \(p_2\), is exactly the predicate in
(2.1). The checked bound on each of its connected components
therefore applies. Translating back preserves connectedness
and cardinalities. Since the choice of \(i,u,v,r\) was
arbitrary, all infinite-lattice components satisfy the bound.
The induction for additional moduli repeats the same argument.
\(\square\)

The lemma is a general *finite certificate interface*: an
upstream complete periodic partition can be refined by additional
local congruences without enumerating the enormous full product
period \(qp_1p_2\).

## 3. Applying mod 19 and mod 5

Let \(Q=1122\), \(p_1=19\), \(p_2=5\),
\[
 P_{19}(z)=[19\nmid N(z)],\qquad P_5(z)=[5\nmid N(z)],
 \quad T=241.                                           \tag{3.1}
\]
The underlying parent quotient partition has **204800** points
in **6688** explicitly listed connected sets \(C_i\), and
all of its allowed neighbors are certified to stay in the
same \(C_i\). The exact byte contents of its certificate
`../sqrt-minus-two-sqrt6-period/code/positive_q1122.json.gz`
are pinned in the new checker by SHA256
`86f44f88613a6e7f3f4808c6611ac76bd689b1d876eea27f10cf29eb953df314`.
The parent complete-partition checker supplies the hypotheses
of Lemma 2, so we do **not** present the C++ generator's output
as a substitute for them.

**Lemma 3 (exact finite 19/5 audit).** The three checks of Lemma 2
hold for the data in the preceding paragraph, with the following
exactly replayed counts:

| Check | Exhaustive result |
| --- | ---: |
| Original \(C_i\) with size greater than 241 | **190** |
| First-stage mod-19 shift/component checks | **68,590** shift configurations |
| First-stage connected components exceeding 241 | **8** |
| Largest first-stage component | **298** |
| Second-stage mod-5 shift configurations on the eight large components | **200** |
| Largest second-stage component | **241** |

*Proof.* The standalone program `code/check_exact.py` loads the
literal prior positive partition, verifies its immutable hash and
its cardinality, and constructs independently all fourteen
adjacency relations within each relevant \(C_i\). It
enumerates **every** \(u\in\{0,\ldots,18\}^2\).
Since \(Q\equiv1\pmod{19}\), the first-stage membership
test is simply
\[
 ((a+u_1)^2+2(b+u_2)^2)\not\equiv0\pmod{19}.
\]
It computes every connected component of this literal induced
graph using a fresh exact integer traversal. Only eight
first-stage components have more than 241 points. For each
of those eight components it checks every one of the
25 second-stage \((v_1,v_2)\in\{0,\ldots,4\}^2\)
against the **literal** predicate
\[
 5\nmid N((a,b)+1122u+1122\cdot19v).                \tag{3.2}
\]
All connected components of these 200 graphs have at most
241 vertices. One actually attains 241, at parent component
index 2228 and shifts \(u=(15,0)\), \(v=(1,0)\)
(zero-based indexing into the pinned parent JSON).

The verifier enumerates all the stated finite domains,
checks the exact count of oversized groups and CRT shift cases,
and **raises an exception** if any final component exceeds
241. It neither trusts a stored maximum nor invokes any
search/optimization program. The arithmetic is integral, with
no approximation. This proves Lemma 3. \(\square\)

*Proof of the refined-sieve statement in Theorem 1.* The
parent partition and Lemma 3 satisfy all hypotheses of Lemma 2.
Thus every connected component of the complete infinite
refined sieve (1.3) has at most 241 vertices. Since \(Q\)
is relatively prime to 95, the shifts giving the equality
case in Lemma 3 correspond to an actual translate of the
parent \(C_{2228}\) in the full lattice. That finite
component is closed by the parent partition and by the
refinement conditions, so size 241 is **attained**. \(\square\)

## 4. Exceptional irreducibles and the true prime graph

To pass from the norm-coprime sieve to *all* irreducibles,
we must handle primes whose norms are divisible by
\(Q\cdot5\cdot19\). The predecessor proves that all
irreducibles with \(\gcd(N,1122)>1\) belong to a single
**exactly ninety-vertex closed prime component** \(K_{90}\),
whose explicit 92-point overgraph closure is in
`../sqrt-minus-two-sqrt6-period/code/exceptional_closure.json`.

For the two new rational primes, the algebra is elementary:

- Modulo \(5\), the only solution of
  \(a^2+2b^2\equiv0\) is \(a\equiv b\equiv0\).
  Hence an irreducible whose norm is divisible by 5 is an
  associate of the rational inert prime \(5\), namely
  \(\pm5\).
- Modulo \(19\), since \(6^2\equiv-2\pmod{19}\),
\[
  a^2+2b^2\equiv(a+6b)(a-6b)\pmod{19}.                 \tag{4.1}
\]
  The prime-norm elements \(1+3t\) and \(1-3t\) generate
  the two corresponding split prime ideals. Any irreducible
  with norm divisible by 19 is associate to one of these,
  giving the four elements \(\pm(1+3t),\pm(1-3t)\).

All **six** new exceptional elements lie inside the original
90-point prime component \(K_{90}\). This follows by directly
checking membership in the predecessor's immutable 92-point
closure; `code/check_exact.py` performs that check, and also
verifies both modular norm conditions by exhaustive finite
integer congruences. The predecessor's irreducibility and
connectivity certificate establishes that all six are in the
**same** 90-vertex prime component, not merely near it.

**Lemma 4.** Every irreducible outside \(K_{90}\) has norm
coprime to \(1122\cdot5\cdot19\).

*Proof.* If a rational prime dividing the product divides
the norm of such an irreducible, unique factorization and
the explicit prime decompositions above force it to be
associate to one of the seven inherited prime factors,
the inert \(5\), or a split prime over \(19\). Every such
element belongs to \(K_{90}\), contradiction. \(\square\)

*Completion of Theorem 1.* \(K_{90}\) gives the lower bound
\(B_D\ge90\). Lemma 4 shows that every other prime component
lies within the induced graph of the refined sieve (1.3),
whose full infinite components have at most 241 vertices by
Lemma 3 and Lemma 2. Therefore \(B_D\le241\).
The step set (1.1) is unchanged over the entire specified
real-radius interval. \(\square\)

## 5. Reproduction and remaining gaps

Run the upstream complete positive proof checker followed by
the layered checker:

```sh
(cd ../sqrt-minus-two-sqrt6-period && python3 code/check_exact.py)
python3 code/check_exact.py
python3 -O code/check_exact.py
python3 code/self_test.py
python3 -O code/self_test.py
sha256sum -c SHA256SUMS
```

The new computation does not need a giant certificate for the
period \(1122\cdot19\cdot5=106590\), which would have more
than eleven billion potential residue pairs. It reuses a
**fixed and SHA256-pinned complete parent partition** and
explicitly tests only the necessary finite component
refinements, whose count and maximum are independently
recomputed. This exact-arithmetic local-to-global method can
be repeated for further rational prime moduli.

The bound \(241\) is proven **only as an upper bound on the true
irreducible prime graph**, not asserted to be sharp there.
The known 90-prime component remains the lower witness;
\(90<B_D\le241\) is not excluded by this research note.
Further congruence refinement, an exact prime-only maximum
classification, and a general theory of which moduli split
large periodic pieces are natural next problems.

This is additive to the published sharp-period theorem and
the separate seven-generator rigidity note; their historical
source bytes are not altered here. The prime-sieve method is
attributed to OpenAI/math family 028 and repository entry 002.
No world-first claim, external human referee or full Lean
formalization is asserted.
