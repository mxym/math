# Conditional exactness of the \(\sqrt6\)-prime graph from a single explicit Schinzel-H instance

**Research note, 8 October 2026.** This note gives an unconditional and fully
replayable reduction, but the existence of the promised prime-valued
specialization is explicitly **conditional on Schinzel's Hypothesis H**, which
is unproved. No unconditional determination of the true prime graph maximum
is claimed.

## 1. Three distinct statements

Set \(t=\sqrt{-2}\), \(R=\mathbb Z[t]\) and
\(N(a+bt)=a^2+2b^2\). Let \(F_{14}\subset\mathbb Z^2\) consist of all
fourteen nonzero differences with \(N\le6\):
\[
 F_{14}=\{(\pm1,0),(0,\pm1),(\pm1,\pm1),
                    (\pm2,0),(\pm2,\pm1)\}.                 \tag{1.1}
\]
For every real \(\sqrt6\le D<\sqrt8\), let \(B_D\) be the supremum of
connected-component cardinalities in the graph of all *irreducible
elements* of \(R\), with edges at genuine complex Euclidean distance at
most \(D\). The separately published exact integer-sieve proof gives
the **unconditional** result
\[
                         90\le B_D\le197.                   \tag{1.2}
\]
It also exhibits a connected **197-point norm-admissible lattice
configuration**. A norm-admissible pattern need not actually be a pattern
of prime elements.

Here we close the precise conditional gap:

**Theorem A (single-instance conditional exact prime maximum).** There
is an **explicit list of 197 distinct, monic, irreducible quadratic
polynomials** \(f_1,\ldots,f_{197}\in\mathbb Z[T]\) with these
properties:

1. Their product \(F(T)=\prod_j f_j(T)\) has **no fixed rational
   prime divisor**: for every rational prime \(p\), some integer
   \(n_p\) satisfies \(p\nmid F(n_p)\).
2. If there exists **one** integer \(n\) such that *all 197* values
   \(f_j(n)\) are rational primes, then for every
   \(\sqrt6\le D<\sqrt8\),
\[
                          \boxed{B_D=197}.                  \tag{1.3}
\]
3. If the **classical one-variable Schinzel–Sierpiński Hypothesis H**
   holds for this **specific explicitly provided family** of
   polynomials, then (1.3) holds and the irreducible graph has
   **infinitely many distinct components of exactly 197 vertices**.

In particular, assuming Hypothesis H **in its usual full generality**
implies the exact value \(B_D=197\). Conversely, a proof that
\(B_D\le196\) would furnish a counterexample to Hypothesis H for
this explicit admissible quadratic family. This logical consequence
is not a claim that Hypothesis H has been proved or refuted.

The prerequisite in item 2 is more concrete (and strictly less
logically demanding as an assumption) than the full hypothesis:
**one finite simultaneous rational-primality certificate** would
suffice for an unconditional exact solution. The note does *not*
supply such an \(n\), and it does not treat its existence as a
completed theorem.

## 2. Explicit 197-polynomial construction

Import the 197-point connected integer configuration
\(S\subset\mathbb Z^2\) from the earlier
[universal admissible-pattern proof](../sqrt-minus-two-universal-sieve-barrier/paper.md).
The full list of its 197 integer coordinates is pinned at
`../sqrt-minus-two-universal-sieve-barrier/code/connected_shape.json`,
with SHA256
`b8036dcfa082e1329126041d8c7992139da6121e4ebf71599458619e7af93df0`.
That proof gives, for every rational prime \(p\), at least one local
translation \((u_p,v_p)\in(\mathbb Z/p)^2\) satisfying
\[
         (a+u_p)^2+2(b+v_p)^2\not\equiv0\pmod p
                  \quad\text{for all }(a,b)\in S.          \tag{2.1}
\]
For the 45 primes \(p\le197\), explicit translations are already
recorded in that predecessor. For all larger primes, the predecessor
proves existence by a finite-field split/inert argument.

Set \(m=|S|=197\). For each of the **77 rational primes**
\(p\le2m=394\), select a local shift satisfying (2.1). The file
`code/schinzel_affine_family.json` fixes a deterministic choice for
**every** one of those 77 primes. Apply coordinatewise CRT to obtain
nonnegative integers \(X,Y_0<M\), where
\[
            M=\prod_{p\le394,\ p\text{ prime}}p,
     \qquad (X,Y_0)\equiv(u_p,v_p)\pmod p.                 \tag{2.2}
\]
Choose \(Y=Y_0+M\), so that \(Y+b>0\) for every point
\((a,b)\in S\) (all \(b\) are between \(-34\) and 34).
All of \(M,X,Y\) are concrete positive integers of approximately
159 decimal digits, recorded **exactly** as strings in the JSON
certificate. Its separate producer is `code/build_polynomials.py`;
the independent verifier does not import the producer.

For each \(z=(a,b)\in S\), define
\[
\boxed{\quad f_z(T)=(T+X+a)^2+2(Y+b)^2
 =T^2+2(X+a)T+(X+a)^2+2(Y+b)^2.\quad}                    \tag{2.3}
\]
The 197 integer polynomials (2.3) are the promised explicit family.
Their full coefficients need not be independently printed in a
many-page table: the **frozen** values of \(X,Y\) and the full
197-point list uniquely specify them, and `code/check_polynomials.py`
reconstructs and tests every coefficient with exact integers.

**Lemma 2.1 (irreducible, distinct, positive quadratic forms).**
Every \(f_z\) in (2.3) is monic, nonconstant, irreducible over
\(\mathbb Q[T]\), and positive for all integer \(T\). Moreover,
the 197 polynomials are pairwise distinct.

*Proof.* Their discriminants are
\[
                 \Delta_z=-8(Y+b)^2<0.                    \tag{2.4}
\]
Because their degree is two and they have negative discriminant,
each is irreducible over \(\mathbb Q[T]\). Since \(Y+b>0\), all
values are positive. If two monic polynomials \(f_{(a,b)}\) and
\(f_{(a',b')}\) were equal, comparison of their linear
coefficients would give \(a=a'\), and comparison of the
remaining constants would give \((Y+b)^2=(Y+b')^2\). Both
bases are strictly positive, so \(b=b'\). Thus distinct points
of \(S\) give distinct polynomials. \(\square\)

**Lemma 2.2 (no fixed prime divisor of the product).** For every
rational prime \(p\), there is some integer \(n\) with
\(p\nmid\prod_{z\in S}f_z(n)\).

*Proof.* If \(p\le394\), take \(n=0\). By construction of the
CRT shift and (2.1),
\[
       f_{(a,b)}(0)=N((X+a)+(Y+b)t)\not\equiv0\pmod p
                   \quad\text{for every }(a,b)\in S.
\]
Hence their product is nonzero modulo \(p\).

If \(p>394\), reduce the product
\(F(T)=\prod_{z\in S}f_z(T)\) modulo \(p\). Because every
factor is monic quadratic, this is a **nonzero monic polynomial
of exact degree** \(2\cdot197=394\) over \(\mathbb F_p\).
A nonzero polynomial of degree 394 has at most 394 roots in
\(\mathbb F_p\). Since \(p>394\), some
\(n\in\{0,\ldots,p-1\}\) is not a root of \(F\), which is
exactly the claim. These cases cover every prime. \(\square\)

The certificate checker independently verifies every CRT
congruence, all \(197\cdot77\) small-prime modular nonzero tests,
all negative discriminants, and pairwise distinctness. The
argument for *infinitely many* primes \(p>394\) is the elementary
polynomial root bound in Lemma 2.2, not experimental
extrapolation or an unverified claim by the checker.

**Proposition 2.3 (general one-variable reduction for imaginary
quadratic norm patterns).** Let \(d\ge1\) be an integer and let
\(S\subset\mathbb Z^2\) be any nonempty finite set of cardinality
\(m\). Assume that for **every** rational prime \(p\) there is a
translation \((u_p,v_p)\in\mathbb F_p^2\) satisfying
\[
   (a+u_p)^2+d(b+v_p)^2\not\equiv0\pmod p
                          \quad((a,b)\in S).                  \tag{2.5}
\]
Then there exist fixed integers \(X,Y\) such that the \(m\)
polynomials
\[
             (T+X+a)^2+d(Y+b)^2,\qquad(a,b)\in S           \tag{2.6}
\]
are distinct monic irreducible polynomials in \(\mathbb Z[T]\)
with positive values and with **no fixed prime divisor of their
product**. Consequently, under classical Schinzel H, infinitely
many translates of \(S\) consist entirely of elements of
rational-prime norm in \(\mathbb Z[\sqrt{-d}]\).

*Proof.* Select local translations for the finitely many primes
\(p\le2m\), and combine them via coordinatewise CRT to fixed
integers \(X,Y\). Increase \(Y\) by a sufficiently large multiple
of their product so that \(Y+b>0\) for every point of \(S\).
For each polynomial in (2.6), the discriminant is
\(-4d(Y+b)^2<0\), establishing irreducibility over \(\mathbb Q\),
and its leading coefficient is one. As in Lemma 2.1, positivity
of the \(Y+b\) and comparison of coefficients establish pairwise
distinctness. The CRT translation ensures the product is nonzero
at \(T=0\) modulo every prime \(p\le2m\). For \(p>2m\), that
product is monic of degree \(2m<p\), so it is nonzero at
some residue \(T\bmod p\). Thus the complete conditions of
Schinzel H hold. Under that *unproved* hypothesis, infinitely
many positive integers \(T\) give rational-prime norm values.
Any element of rational-prime norm in
\(\mathbb Z[\sqrt{-d}]\) is irreducible by multiplicativity
of its positive integral norm. \(\square\)

This proposition isolates the reusable arithmetic insight: a
**two-variable local admissibility certificate** for a finite
pattern in a positive quadratic norm reduces to a **single
explicit one-variable Schinzel-H instance**. It neither assumes
unique factorization in the quadratic order nor changes the
logical status of the unproved prime-value existence conclusion.

## 3. What Hypothesis H would supply—and what it would not

We state explicitly the only unproved ingredient:

**Schinzel's Hypothesis H (classical form; unproved).** If
\(g_1,\ldots,g_k\in\mathbb Z[T]\) are nonconstant irreducible
polynomials with positive leading coefficients, and their product
has no fixed rational prime divisor, then infinitely many positive
integers \(n\) make **all** \(g_j(n)\) positive rational primes.

The hypotheses are *exactly* Lemmas 2.1–2.2. Therefore,
**if Hypothesis H is assumed**, infinitely many positive integers
\(n\) make all 197 values
\(f_z(n)=N((X+n+a)+(Y+b)t)\) rational primes.

A nonunit element of \(R\) whose positive multiplicative norm
is a rational prime is irreducible: in any factorization
\(w=uv\), \(N(w)=N(u)N(v)\), and positive integer primality
forces one of the factors to have norm one, hence to be a
unit. Thus every point of the translate
\[
             S+(X+n,Y)                                  \tag{3.1}
\]
is an **irreducible element** of \(R\) for any such specialization.
The original \(S\) is connected with differences in \(F_{14}\),
and translation preserves those differences. Therefore (3.1)
is a connected **197-prime subgraph**. The unconditional
[exact finite-sieve optimum theorem](../sqrt-minus-two-exact-sieve-optimum/paper.md)
proves *every* prime component has at most 197 vertices;
accordingly each such connected subgraph is **exactly a full
prime component** of size 197.

Since Hypothesis H gives infinitely many *unbounded* positive
solutions \(n\), we may select an infinite subsequence for
which any two \(n\)-values differ by more than the 44-unit
horizontal extent of \(S\). The translates (3.1) are then
pairwise disjoint, giving infinitely many distinct prime
components of size 197. This completes the conditional part
of Theorem A. Its upper bound and the construction of the
admissible polynomials are **unconditional**; only the
simultaneous *primality of their values* is conditional.

## 4. Under H, every component size 1 through 197 occurs infinitely often

The preceding theorem gives 197-prime *components* because the
unconditional upper bound is also 197. A stronger conclusion is
possible: conditional on **full** classical Hypothesis H, every
smaller admissible connected pattern can be forced to be an
**entire** component by making all of its immediate outside
neighbors demonstrably composite.

**Theorem B (conditional complete component-size spectrum).** Under
the classical Schinzel–Sierpiński Hypothesis H, for each integer
\(1\le k\le197\), the true irreducible-element graph of
\(\mathbb Z[\sqrt{-2}]\) has **infinitely many distinct connected
components of exactly \(k\) vertices** for every real
\(\sqrt6\le D<\sqrt8\). Combined with the unconditional bound
\(B_D\le197\), the complete positive component-size spectrum
under Hypothesis H is exactly
\[
                          \boxed{\{1,2,\ldots,197\}}.       \tag{4.1}
\]
This theorem invokes **full Hypothesis H** (or H separately for the
197 explicitly constructible finite polynomial families below),
not merely the single family in Theorem A. Its conclusion is **not
unconditionally established**.

We prove a more general exact-component principle before verifying
its finite inputs.

**Lemma 4.1 (inert-prime boundary blocking).** Let \(S'\subset
\mathbb Z^2\) be finite, nonempty and connected under \(F_{14}\).
Assume that for every rational prime \(p\), some translation of
\(S'\) modulo \(p\) avoids the norm-zero set of
\(N(a,b)=a^2+2b^2\). Let its **external boundary** be
\[
 \partial_F S'=\{w\notin S':w-z\in F_{14}\text{ for some }z\in S'\}.
\]
For each \(w\in\partial_F S'\), suppose one is given a
**distinct rational prime** \(q_w>2|S'|\) such that \(-2\) is
a nonsquare modulo \(q_w\), and that
\[
                    q_w\nmid N(z-w)\qquad(z\in S').        \tag{4.2}
\]
Then, under classical Hypothesis H, infinitely many translates
of \(S'\) are **full connected components** of the irreducible
graph with steps \(F_{14}\).

*Proof.* Put \(k=|S'|\) and \(B=\partial_F S'\).
Choose a norm-avoiding local translation modulo every rational
prime \(p\le2k\); these exist by the hypothesis on \(S'\).
The \(q_w\) are pairwise distinct and all exceed \(2k\), so
coordinatewise CRT yields integers \(X,Y\) such that:
\[
\begin{aligned}
 &(X,Y)\text{ is norm-avoiding on }S'\text{ modulo every }p\le2k,\\
 &(X,Y)\equiv-w\pmod{q_w}\qquad(w\in B).
\end{aligned}                                                \tag{4.3}
\]
Increase \(Y\) by a sufficiently large multiple of the total CRT
modulus, preserving all congruences, so that
\(Y+b>0\) for every \((a,b)\in S'\), and also
\(Y+w_2>\max_{w\in B}q_w\) for every \(w=(w_1,w_2)\in B\).
Let \(L=\prod_{w\in B}q_w\) (interpreting an empty product as 1)
and define
\[
                f_z(T)=N((X+LT,Y)+z),\qquad z\in S'.       \tag{4.4}
\]
These are positive quadratics with leading coefficient \(L^2\),
negative discriminant \(-8L^2(Y+b)^2\) and pairwise distinct
coefficients. Hence they are irreducible over \(\mathbb Q[T]\).

Their product has no fixed rational prime divisor. For every
\(p\le2k\), the value at \(T=0\) is nonzero modulo \(p\)
by (4.3). For \(p>2k\) **not** dividing \(L\), the product has
nonzero leading coefficient \(L^{2k}\bmod p\) and degree
\(2k<p\); consequently it cannot vanish for every
\(T\in\mathbb F_p\). Finally, if \(p\mid L\), then
\(p=q_w\) for some boundary point \(w\). Modulo \(q_w\),
\(L\equiv0\) and \((X,Y)\equiv-w\), so for all
\(z\in S'\) and all \(T\),
\[
                     f_z(T)\equiv N(z-w)\not\equiv0
                                    \pmod{q_w},              \tag{4.5}
\]
by the explicit assumption (4.2). These cases exhaust
**every** rational prime. Thus classical Hypothesis H applies to
the fixed finite family (4.4) and, if assumed, provides infinitely
many positive integers \(T\) for which all \(f_z(T)\) are
rational primes. As in Theorem A, all corresponding ring elements
\((X+LT,Y)+z\), \(z\in S'\), are irreducible and connected.

Crucially, *none* of their external neighbors is irreducible.
For every \(w\in B\), the element
\(\beta_w(T)=(X+LT,Y)+w\) has both integer coordinates
divisible by \(q_w\), by (4.3) and \(q_w\mid L\). Thus
\(\beta_w(T)=q_w\eta_w(T)\) for a ring integer
\(\eta_w(T)\in R\). The chosen large second coordinate gives
\[
               N(\beta_w(T))\ge2(Y+w_2)^2>q_w^2=N(q_w),
\]
so \(N(\eta_w(T))>1\), and \(\eta_w(T)\) is a nonunit.
Hence \(\beta_w(T)\) is **reducible**, not just of composite
rational norm. Since every possible prime neighbor of the
translated connected \(S'\) is such a boundary element, it is
**exactly an entire connected component**. The infinitely many
unbounded positive specializations may be spaced farther apart
than the width of \(S'\), yielding pairwise disjoint exact
components. \(\square\)

**Lemma 4.2 (certified boundary blockers for all 197 prefixes).**
There exist explicit connected sets
\(S_1\subset S_2\subset\cdots\subset S_{197}=S\), with
\(|S_k|=k\), such that for each \(k\), the boundary
\(\partial_F S_k\) admits the distinct inert-prime blockers
required by Lemma 4.1.

*Proof by independently replayable finite data.* Traverse the
frozen 197-point \(S\) by a deterministic breadth-first
spanning-tree exploration under the fourteen moves (1.1), and
take the first \(k\) vertices as \(S_k\). Every prefix is
connected by construction, and every subset is universally
norm-admissible because \(S\) is. Directly forming the external
neighbor sets shows they have at most **1186** points, with the
maximum occurring at \(k=197\). Assign to the lexicographically
ordered boundary points the first \(|\partial_F S_k|\) entries
of the frozen `code/inert_boundary_primes.json`. This file lists
1186 **distinct, exact rational primes**, the first being 397
and the last 46237, all congruent to 5 modulo 8, hence inert in
\(\mathbb Q(\sqrt{-2})\), and all exceeding
\(2\cdot197=394\).

The independent `code/check_boundary_spectrum.py` reconstructs all
197 connected prefixes, tests the exact primality and quadratic
nonresiduosity of every frozen boundary blocker, and verifies
(4.2) for **every** internal–boundary point pair, a total of
**15,563,538 exact integer norm nonvanishing checks**. This is
finite evidence for every explicitly bounded hypothesis of
Lemma 4.1, without assuming any simultaneous prime values.
The source and complete frozen blocker list are public. \(\square\)

*Proof of Theorem B.* For each \(k\), the set \(S_k\) is
universally norm-admissible by heredity from the published
197-point certificate, and satisfies Lemma 4.1 by
Lemma 4.2. Assuming classical Hypothesis H, infinitely many
full prime components of size \(k\) therefore exist. The
unconditional upper bound 197 rules out larger components.
\(\square\)

## 4. Why existing constellation theorems do not supply the missing step

A theorem of Tao, [*The Gaussian primes contain arbitrarily
shaped constellations*](https://arxiv.org/abs/math/0501314),
and its number-field generalization by Kai–Mimura–Munemasa–Seki–Yoshino,
[*Constellations in prime elements of number fields*](https://arxiv.org/abs/2012.15669),
establish the existence of **translated and dilated**
prime constellations in their respective settings. Their common
geometric form allows a nonzero dilation parameter
\(r\) for a prescribed shape \(S\): \(a+rS\).

Such results do **not** assert that \(r=1\) is possible.
For the bounded-step graph here, a dilation \(|r|>1\)
changes the differences and can destroy adjacency under
\(F_{14}\). Consequently those major unconditional
constellation results do **not** supply the fixed-displacement
197-prime component required here. Nor does a finite sieve
certificate of local admissibility establish the unproved
quadratic prime-value assertion of Hypothesis H.

Our theorem is not intended as a claimed difficulty reduction
to any logically **necessary** conjecture: an unconditional
197-prime component could exist for reasons unrelated to
Hypothesis H, and conversely the global prime graph might
have its maximum realized by a different connected shape.
The precise proven implication is the **sufficient conditional
result** stated in Theorem A.

## 6. Exact reproduction, trust boundary and further research

The verification of the polynomial family is independent of
any unproved prime-value input:

```sh
python3 code/check_polynomials.py
python3 -O code/check_polynomials.py
python3 code/check_boundary_spectrum.py
python3 -O code/check_boundary_spectrum.py
python3 code/self_test.py
python3 -O code/self_test.py
sha256sum -c SHA256SUMS
```

The optional deterministic producer `code/build_polynomials.py`
constructs the 77 local shifts and global CRT coefficients, but
the separate checker reads the **published literal certificate**,
reconstructs all 197 polynomial coefficients, and tests the
exact arithmetic conditions. The proof for large primes and
negative quadratic discriminants is provided above in closed
form; neither component assumes any solver's `True` output.

**What remains unproved:** There is no verified integer \(n\)
for which the 197 polynomials in (2.3) simultaneously take
rational prime values, and Schinzel's Hypothesis H is not
known. The exact **unconditional** value of the real prime graph
maximum \(B_D\) therefore remains somewhere in the proved
interval \([90,197]\). The conditional equality is a
genuinely more precise mathematical deduction, but it must not
be reported as an unconditional solution. The work is
model-assisted and not externally refereed or Lean-formalized.
