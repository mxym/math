# A universally admissible connected 197-point configuration and a barrier for finite principal-ideal sieve bounds

Research continuation, 8 October 2026. A complete written proof with explicit
finite rational-integer witnesses and two separately implemented checkers.
AI-assisted; neither independent external referee review nor worldwide
novelty priority is claimed.

## 1. Precise setting and theorem

Let \(t=\sqrt{-2}\) and identify \(R=\mathbb Z[t]\) with \(\mathbb Z^2\)
by \(a+bt\leftrightarrow(a,b)\). Its positive integral multiplicative
norm is
\[
                       N(a,b)=a^2+2b^2.                   \tag{1.1}
\]
Let \(F\) be the **14-element symmetric step set**
\[
 F=\{(\pm1,0),(0,\pm1),(\pm1,\pm1),
          (\pm2,0),(\pm2,\pm1)\}.                          \tag{1.2}
\]
Within each parenthesized pair the choices of sign are independent.
These are precisely the differences of squared norm at most 6.
The corresponding genuine complex Euclidean radii are
\(\sqrt6\le D<\sqrt8\).

For any finite list \(\mathcal G\) of nonzero **nonunit** elements of
\(R\), its principal-ideal *allowed set* is
\[
 A(\mathcal G)=R\setminus\bigcup_{g\in\mathcal G}(g).
                                                                  \tag{1.3}
\]
We consider the induced \(F\)-graph on **all** allowed lattice elements,
not only the irreducibles. Call \(\mathcal G\) a successful sieve if
all components of this allowed graph are finite. If the list is
nonempty, let \(q(g)\) be the least positive integer divisible by
\(g\) and \(Q(\mathcal G)=\operatorname{lcm}_{g\in\mathcal G}q(g)\).
All such periods exist in this ring, by conjugation. The empty list is
also allowed in the theorem below; its full lattice graph trivially
contains connected subsets of all finite sizes.

**Theorem 1 (universal 197-vertex principal-sieve obstruction).** There
exists an **explicit connected set** \(S\subset\mathbb Z^2\) of
exactly \(|S|=197\) points with the following stronger property:
\[
 \boxed{\ \forall\text{ finite sets }\mathcal P\text{ of rational primes,}
 \quad\exists w\in\mathbb Z^2\quad
 \gcd\!\left(N(z+w),\prod_{p\in\mathcal P}p\right)=1
 \quad\forall z\in S.\ }                                  \tag{1.4}
\]
When \(\mathcal P=\varnothing\), its product is one.
Consequently, **for every finite principal-ideal sieve** \(\mathcal G\),
including arbitrary composite generators and any finite common scalar
period, the allowed graph on \(A(\mathcal G)\) contains a connected
subgraph with **at least 197 vertices**: some translate \(S+w\).
In particular, if \(M(\mathcal G)\) denotes the supremum of
connected-component cardinalities (possibly infinite), then
\[
                         M(\mathcal G)\ge197.             \tag{1.5}
\]
The 197-point obstruction applies simultaneously to **every** possible
finite principal-ideal sieve, but its favorable translation \(w\)
may depend on the sieve. It does **not** assert that these 197
vertices are irreducible elements, nor that one fixed translate avoids
all rational primes at once.

Define the least component bound attainable by this **particular
finite principal-ideal certificate method**:
\[
  \mathfrak M_F(R)=\inf_{\mathcal G\text{ finite, successful}}
           \max\{|C|:C\text{ a component of }A(\mathcal G)\}.
                                                                  \tag{1.6}
\]
Our previously published [exact layered refinement theorem](../sqrt-minus-two-prime-bound-241/paper.md)
constructs a specific successful principal-ideal sieve with component
maximum **241**. Combining it with Theorem 1 gives:

**Corollary 2 (certified structural method interval).**
\[
                    \boxed{197\le\mathfrak M_F(R)\le241}. \tag{1.7}
\]
Thus **no finite principal-ideal sieve can certify a component-size
upper bound 196 for its entire allowed lattice graph**. The exact value
of \(\mathfrak M_F(R)\) is not determined. Crucially, (1.7) is **not**
a lower bound on the actual irreducible-only prime graph, whose
separate proven range remains \(90\le B_D\le241\).

## 2. General admissible-pattern principle

A structural statement explains why the result has little dependence
on the particular quadratic ring.

**Lemma 3 (finite universally norm-admissible patterns obstruct finite
principal sieves).** Let \(R\) be a commutative integral domain,
free of finite rank \(r\) over \(\mathbb Z\), with a multiplicative,
positive integer-valued absolute norm \(N\) satisfying
\(N(n)=|n|^r\) for nonzero \(n\in\mathbb Z\), and
\(N(g)>1\) for every nonunit \(g\). Assume each nonzero element
divides a positive rational integer. Fix a symmetric finite step
set \(F\) in the \(\mathbb Z\)-coordinate lattice of \(R\).
Suppose a finite nonempty \(F\)-connected configuration \(S\subset R\)
has this property: for every rational prime \(p\), there exists a
coordinate translation \(w_p\in R/pR\) such that
\[
                   N(z+w_p)\not\equiv0\pmod p
                     \qquad(z\in S).                       \tag{2.1}
\]
Then every finite principal-ideal sieve in \(R\) leaves some
translate of \(S\) entirely allowed. Consequently every such sieve
has a connected component of size at least \(|S|\).

*Proof.* Let \(\mathcal G\) be a nonempty finite list of nonzero
nonunits, put \(Q=\operatorname{lcm}_{g\in\mathcal G}q(g)\), and let
\(\mathcal P\) be the **finite** set of rational primes dividing \(Q\).
Each \(g\) divides \(q(g)\), which divides \(Q\) as a rational
integer. Multiplicativity of the norm implies
\[
                      N(g)\mid N(Q)=Q^r.                   \tag{2.2}
\]
Since \(g\) is a nonunit, \(N(g)>1\). Choose some rational prime
\(p\mid N(g)\). Equation (2.2) implies \(p\mid Q\), so
\(p\in\mathcal P\). If \(x\in(g)\), norm multiplicativity gives
\(N(g)\mid N(x)\), and in particular \(p\mid N(x)\). Therefore
\[
 \{x:\gcd(N(x),Q)=1\}\ \subseteq\ A(\mathcal G).      \tag{2.3}
\]

For each \(p\in\mathcal P\), choose \(w_p\) as in (2.1).
The coordinatewise Chinese remainder theorem supplies a single
\(w\in R\) whose class modulo \(pR\) equals \(w_p\) for every
\(p\in\mathcal P\). Thus for every \(z\in S\) and every
\(p\in\mathcal P\), the integer \(N(z+w)\) is not divisible by
\(p\). The entire translate \(S+w\) belongs to the norm-coprime
set in (2.3), hence to \(A(\mathcal G)\). Translation preserves
\(F\)-adjacency, so \(S+w\) is connected. Its \(|S|\) distinct
vertices lie in one allowed connected component. For the empty
sieve choose \(w=0\). \(\square\)

No primality conjecture, Dirichlet theorem, positive density argument,
or ring unique-factorization hypothesis is needed for Lemma 3: the
finite-sieve obstruction follows only from norms, CRT, and the
finite local translations. It does not imply any of the elements of
\(S+w\) are irreducible.

## 3. A finite local certificate suffices for **all** rational primes

The configuration S in Theorem 1 has 197 points, so it is enough
to give explicit admissible translations for the 45 rational primes
\(p\le197\). The following lemma rigorously handles all larger
primes, without machine enumeration.

**Lemma 4 (all large primes admit a norm-avoiding translation).**
Let \(S\subset\mathbb Z^2\) have \(|S|=m\). For every
rational prime \(p>m\), there exists \((u,v)\in(\mathbb Z/p)^2\)
such that
\[
               (a+u)^2+2(b+v)^2\not\equiv0\pmod p
                          \qquad((a,b)\in S).                \tag{3.1}
\]

*Proof.* Since \(p>m\ge1\), \(p\) is odd. There are two cases.

If \(-2\) is a quadratic **nonresidue** modulo \(p\), the zero set
of \(x^2+2y^2\) in \(\mathbb F_p^2\) is the origin alone.
Indeed a nonzero \(y\) in such a solution would give
\((x/y)^2=-2\). Each \(z\in S\) then forbids exactly one
translation \((u,v)=-z\). As \(m<p<p^2\), these cannot cover all
\(p^2\) translations.

If \(-2\) is a quadratic **residue**, choose
\(s\in\mathbb F_p\setminus\{0\}\) with \(s^2=-2\). Then
\[
           x^2+2y^2=(x+sy)(x-sy).                           \tag{3.2}
\]
Each of the sets of projected residues
\[
       A_+=\{a+sb:(a,b)\in S\},\qquad
       A_-=\{a-sb:(a,b)\in S\}
\]
has cardinality at most \(m<p\). Choose residues
\(c_+\notin-A_+\) and \(c_-\notin-A_-\).
The linear map
\[
 (u,v)\mapsto(u+sv,u-sv)
\]
is invertible over \(\mathbb F_p\): its determinant
\(-2s\ne0\). Hence there is a translation with
\(u+sv=c_+\), \(u-sv=c_-\). For each \(z=(a,b)\in S\),
\((a+u)+s(b+v)\ne0\) and
\((a+u)-s(b+v)\ne0\); (3.2) then proves (3.1).

These cases exhaust every odd \(p>m\). \(\square\)

For \(p=2\), no large-prime argument is used; it is explicitly
certified in the local table below. This distinction is essential
because the determinant \(-2s\) vanishes in characteristic two.

## 4. The explicit 197-point connected witness

The files `code/connected_shape.json` and `code/local_shifts.json`
are **raw explicit finite data**:

- `connected_shape.json` lists all **197** distinct coordinate pairs
  \((a,b)\), with \(369\le a\le413\) and \(-34\le b\le34\).
- `local_shifts.json` maps **each of the 45 rational primes
  \(2\le p\le197\)** to a particular ordered pair
  \((u_p,v_p)\in\{0,\ldots,p-1\}^2\).

**Lemma 5 (complete exact local witness).** These data satisfy:

1. The 197 coordinates are distinct and connected by the fourteen
   steps (1.2).
2. For every rational prime \(p\le197\), the corresponding
   literal translation satisfies
\[
        ((a+u_p)^2+2(b+v_p)^2)\bmod p\ne0
                       \quad\text{for all 197 points }(a,b). \tag{4.1}
\]
3. The table has no missing prime, extra composite index, or repeated
   lattice vertex.

*Proof by a complete finite arithmetic certificate.*
`code/check.py` is an integer-only verifier **separate from the
untrusted producer** `code/generate_local_shifts.py`. It reads the
197 coordinates, checks their distinctness, computes all
fourteen-neighbor connections and performs a complete graph
traversal. It then independently generates the list of primes
\(p\le197\) by exact integer trial division. For each prime,
it reads its canonical \((u_p,v_p)\) and checks (4.1) for each
of the 197 positions, with exact integer modular arithmetic.
It rejects omissions or extraneous indices. A second independent
checker `code/check_projection.py` does **not read the shift table**:
it checks the equivalent local split/inert projection condition
for every small prime, obtaining 1 ramified, 20 split and
24 inert prime cases. Finally negative mutation controls delete
shape points, repeat points, remove or forge prime indices, and
insert a deliberately norm-zero translation, confirming rejection.
These finite checks are exhaustive for precisely the explicitly
bounded scope stated in the lemma. \(\square\)

*Proof of Theorem 1.* Lemma 5 supplies all local admissible
translations for primes \(p\le197\). Lemma 4 supplies their
existence for **every** prime \(p>197\). Hence the finite connected
pattern S satisfies hypothesis (2.1) of Lemma 3 at every rational
prime. Applying Lemma 3 proves the translation assertion (1.4)
and the universal allowed-component bound (1.5). \(\square\)

*Proof of Corollary 2.* Theorem 1 gives \(M(\mathcal G)\ge197\)
for every successful finite principal sieve. The previously
certified [mod-19/mod-5 refinement theorem](../sqrt-minus-two-prime-bound-241/paper.md)
constructs a successful sieve with allowed component maximum
\(241\) (its seven period-1122 generators plus the prime ideals
above 19 and the inert prime 5), so \(\mathfrak M_F(R)\le241\).
Both bounds hold for the same fourteen-step graph and the same
notion of allowed lattice components. \(\square\)

## 5. Significance, reproduction and limitations

From this directory, run:

```sh
python3 code/check.py
python3 -O code/check.py
python3 code/check_projection.py
python3 -O code/check_projection.py
python3 code/self_test.py
python3 -O code/self_test.py
sha256sum -c SHA256SUMS
```

All checkers use Python standard-library **exact integer arithmetic**;
no optimization solver, random search, floating-point inequalities
or probabilistic primes are used in their proof decisions.
`code/generate_local_shifts.py` is an optional reproducible **untrusted
producer**; `code/check.py` never imports it. The second checker
rederives local feasibility via the different split/inert projection
formalism. The complete 197-point and 45-prime witness data are in
the repository, not a stored Boolean assertion.

The general Lemmas 3 and 4 identify a **structural limitation** of
finite principal-ideal periodic sieves for bounding the prime graph:
no matter how many congruence conditions of this type are added,
the full allowed lattice must retain a connected shape of 197
vertices. This is a genuine universal statement, unlike merely
observing one large finite quotient component for a particular sieve.
But the pattern's elements might be composite at every favorable
CRT translation. Theorem 1 **does not** construct 197 adjacent
irreducibles, nor does it preclude direct primality arguments from
improving the actual prime-only bound below 197. The known actual
prime graph still satisfies the separately proved
\(90\le B_D\le241\).

The 197 configuration is an **explicit nonoptimal candidate** for
maximizing universally admissible connected patterns. Neither the
largest possible such pattern nor the exact infimum
\(\mathfrak M_F(R)\) is established. Further improvements to
these two structurally different optimization problems and new
prime-only arguments are not claimed solved.

The method builds on the public OpenAI/math bounded Gaussian-prime
walk strategy (family 028, pinned version
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`), the quadratic-order
framework of mxym/math entry 002 and the project's preceding
period-1122 and layered-refinement proofs. Earlier moat/prime-walk
studies include Prasad (2014, arXiv:1412.2310); there is no
first-priority or full literature survey assertion. This
model-assisted written proof is not yet fully Lean-formalized
or independently human-refereed.
