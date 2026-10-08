# Every prime ideal is indispensable at the sharp norm-six sieve period

A finite-witness rigidity theorem for \(\mathbb Z[\sqrt{-2}]\).
Research continuation, 8 October 2026; model-assisted, not peer reviewed.

## 1. Definitions and the completed classification

Put \(t=\sqrt{-2}\), \(R=\mathbb Z[t]\), and identify \(a+bt\)
with \((a,b)\in\mathbb Z^2\). The positive multiplicative norm is
\(N(a+bt)=a^2+2b^2\). For any finite symmetric step set \(F\),
the allowed graph of a finite list \(\mathcal H\) of nonzero nonunit
principal-ideal generators has vertices
\[
 A(\mathcal H)=R\setminus\bigcup_{h\in\mathcal H}(h)
\]
and edges between distinct allowed elements differing by a member of
\(F\). A list is **successful** when every component of this *full
allowed lattice* is finite. Define its common scalar period by
\[
 Q(\mathcal H)=\operatorname{lcm}_{h\in\mathcal H}q(h),
 \qquad q(h)=\min\{n\ge1:n\in(h)\}.
\]

We use the **fourteen** differences \(F_{14}\) with
\(0<N(f)\le6\):
\[
 F_{14}=\{(\pm1,0),(0,\pm1),(\pm1,\pm1),
        (\pm2,0),(\pm2,\pm1)\},                           \tag{1.1}
\]
where pair signs are independent. This is the genuine Euclidean
step graph throughout \(\sqrt6\le D<\sqrt8\).

The [predecessor proof](../sqrt-minus-two-sqrt6-period/paper.md)
with its complete independently replayed certificates establishes:

- **Input P:** no successful principal-ideal sieve has
  \(Q(\mathcal H)<1122\);
- **Input S:** the list of all seven prime-norm generators
\[
 \boldsymbol\pi=(t,1+t,1-t,3+t,3-t,3+2t,3-2t)           \tag{1.2}
\]
  succeeds, has common scalar period \(1122\), and its complete
  allowed lattice is a disjoint union of finite components.

Here we solve the more refined question left open there.

**Theorem 1 (complete optimal-period generator rigidity).** Let
\(\mathcal H\) be **any** finite nonempty list of nonzero nonunit
elements of \(R\) with \(Q(\mathcal H)=1122\), with arbitrary
composite generators and repetitions allowed. Then
\[
 \boxed{\quad\mathcal H\text{ is successful}\quad\Longleftrightarrow\quad
     \text{every one of the seven ideals }(\pi_i)
      \text{ occurs literally among the }(h),\ h\in\mathcal H.\quad} \tag{1.3}
\]
Occurrences are understood up to multiplication of a generator by
one of the units \(\pm1\). In particular:

1. At the **globally least successful scalar period** \(1122\),
   the exact minimum generator count is **seven**.
2. Up to associates and ordering, the seven-element list (1.2) is
   the **unique** successful seven-generator list of optimal period;
   every successful list at this period is an enlargement of it.
3. Replacing a required prime generator with a composite element
   **never** yields a new inclusion-minimal successful list, even
   if more than seven generators are permitted.

This is a theorem about the precise finite principal-ideal sieve
framework; it does not assert optimality over unrelated nonperiodic
methods of proving bounded prime walks, nor the exact largest
irreducible component size.

## 2. A general saturated-prime rigidity principle

The abstract reduction is independent of the quadratic ring.

**Lemma 2 (saturated principal-sieve rigidity).** Let \(R\) be a
unique-factorization integral domain containing \(\mathbb Z\)
such that every divisor of a fixed nonzero integer \(Q\) has a
positive scalar period. Factor \(Q\) in \(R\), up to units, as
\[
                          Q\sim\prod_{i=1}^s\pi_i^{e_i},
 \qquad e_i\ge1,                                         \tag{2.1}
\]
where the \(\pi_i\) are pairwise nonassociate irreducibles.
Fix a translation-invariant finite step graph on \(R\).

Suppose the sieve with *all* the singleton prime ideals
\((\pi_1),\ldots,(\pi_s)\) is successful. For each \(i\), let
\(\mathcal M_i\) be the list of all the other singleton primes
\((\pi_j)\), \(j\ne i\), plus \((\pi_i^2)\) **only if**
\(e_i\ge2\). Assume **every** sieve \(\mathcal M_i\) has an
infinite component. Then every successful principal-ideal list
\(\mathcal H\) with scalar period \(Q\) must contain all the
prime ideals \((\pi_i)\) as literal generator ideals, and their
joint presence is sufficient for success.

*Proof.* Each generator \(h\) divides its scalar period
\(q(h)\), and by hypothesis \(q(h)\mid Q\), so \(h\mid Q\).
Suppose \(\mathcal H\) omits the singleton \((\pi_i)\). By unique
factorization, each nonunit \(h\mid Q\) has one of two properties:

- It is divisible by some \(\pi_j\) with \(j\ne i\). Then
  \((h)\subseteq(\pi_j)\).
- All its prime factors are \(\pi_i\). Since it is not
  associate to \(\pi_i\), it is divisible by \(\pi_i^2\),
  so \(e_i\ge2\) and \((h)\subseteq(\pi_i^2)\).

Thus in either case \((h)\) is contained in one of the ideals
of \(\mathcal M_i\). It follows that
\[
       \bigcup_{h\in\mathcal H}(h)
          \subseteq \bigcup_{\mathfrak a\in\mathcal M_i}
                  \mathfrak a,
 \qquad A(\mathcal M_i)\subseteq A(\mathcal H).           \tag{2.2}
\]
The infinite component in the first allowed graph survives in
the second, contradicting success. Consequently all singleton
prime ideals are necessary. Conversely adding any ideals to a
successful sieve only deletes vertices, so the full singleton
prime list is sufficient. \(\square\)

The lemma cleanly separates a general ideal-divisibility mechanism
from the problem-specific finite nonzero-voltage certificates. In
particular, omitting a prime of exponent one requires only the
other singleton prime ideals as a negative witness; a repeated
ramified prime also requires testing its square.

## 3. Explicit eight-case finite obstruction

The ring \(\mathbb Z[\sqrt{-2}]\) is norm Euclidean (round both
coefficients, giving relative error norm at most \(3/4\)), hence a
unique-factorization domain. One has the complete factorization
\[
 1122=2\cdot3\cdot11\cdot17
       \sim t^2(1+t)(1-t)(3+t)(3-t)(3+2t)(3-2t).         \tag{3.1}
\]
The seven factors in (1.2) have rational prime norms
\(2,3,3,11,11,17,17\), respectively. Their least scalar periods
are the corresponding rational primes. Only \(t\) is repeated
in the factorization, with exponent two.

Label the seven factors \(\pi_0,\ldots,\pi_6\) in the order of
(1.2). The explicit finite witnesses in
`code/obstructions.json` establish the following:

| Forbidden singleton prime omitted | Remaining maximal generators | Certified nonzero-1122-voltage walk length |
| --- | --- | ---: |
| \(\pi_0=t\) | The other six primes | 624 |
| \(\pi_1=1+t\) | The other six primes | 567 |
| \(\pi_2=1-t\) | The other six primes | 567 |
| \(\pi_3=3+t\) | The other six primes | 669 |
| \(\pi_4=3-t\) | The other six primes | 669 |
| \(\pi_5=3+2t\) | The other six primes | 759 |
| \(\pi_6=3-2t\) | The other six primes | 759 |
| \(\pi_0=t\), square replacement | The other six primes plus \((t^2)=(2)\) | 854 |

The last case is crucial: a naive six-prime omission check alone
would **not** rule out substituting the composite \(2\) for \(t\).

**Lemma 3 (independent eight-path certificate).** Every sieve in the
above table has an infinite component in its \(F_{14}\)-graph.

*Proof.* Each entry in the JSON file supplies the exact initial
lattice point \(z\) with coordinates between 0 and 1121 and an
ordered list of at most 854 step indices. The fixed lexicographic
step order is
\[
\begin{gathered}
 (-2,-1),(-2,0),(-2,1),(-1,-1),(-1,0),(-1,1),
 (0,-1),(0,1),\\
 (1,-1),(1,0),(1,1),(2,-1),(2,0),(2,1).
\end{gathered}                                              \tag{3.2}
\]
The independent Python program `code/check.py` does **not** call
the program that generated the paths. It tests all seven indexed
cases and the special \(t^2\) case without relying on recorded
Boolean success fields. The checker constructs the actual six
retained generators, adds \(t^2=-2\) in the special case, and
at **every point** along each path checks membership in the
complement of their literal principal ideals using the exact
integer formula
\[
 (c+dt)\mid(a+bt)\ \Longleftrightarrow\
  \begin{cases}
   c^2+2d^2\mid ac+2bd,\\
   c^2+2d^2\mid bc-ad.
  \end{cases}                                               \tag{3.3}
\]
The checker then verifies that the endpoint equals \(z+1122v\)
for some \(v\in\mathbb Z^2\setminus\{0\}\). It explicitly checks
all retained ideals are 1122-periodic, the complete set of eight
cases, the nonzero displacement and every admissible intermediate
vertex. There is no floating point or external solver.

Each allowed vertex set is invariant under \(1122\mathbb Z^2\).
Translate the finite path by \(1122v\), then \(2\cdot1122v\),
and so forth. Every translated path is admissible, and the
successive copies concatenate at their endpoints. The allowed
component contains infinitely many distinct vertices
\(z+n1122v\), so cannot be finite. This converts each explicit
finite certificate into an infinite-graph obstruction. \(\square\)

*Proof of Theorem 1.* The positive input S verifies the seven-prime
sieve is successful and has scalar period 1122; the lower-period
input P identifies it as the **least** possible successful period.
For each factor \(\pi_i\) of the integer 1122, the corresponding
negative maximal sieve \(\mathcal M_i\) from Lemma 2 is precisely
one of the first seven rows of the table, except for \(i=0\),
where it is the final (square replacement) row. Lemma 3 proves all
seven required maximal sieves have infinite components.
Lemma 2 therefore implies that **every** successful sieve of
scalar period 1122 must contain all seven singleton prime ideals,
including when arbitrary composite generators are permitted.
Conversely those seven ideals already give the positive sieve,
and extra ideals cannot create new components. This proves (1.3).
Each of the seven ideals is distinct and necessary, so a successful
list requires at least seven elements, and a successful seven-element
list must be the seven prime factors themselves, up to associates
and ordering. \(\square\)

## 4. Reproduction and scope

From this note's directory run

```sh
python3 code/check.py
python3 -O code/check.py
python3 code/self_test.py
python3 -O code/self_test.py
sha256sum -c SHA256SUMS
```

All eight literal walks and the checker are included as editable
source and JSON. `code/generate.py` is a **nontrusted discovery
program**; a fresh run regenerates the same `obstructions.json`
bytes but is not invoked by the independent checker. The
mutation suite deliberately corrupts omission indices and path
steps and checks rejection, including with Python optimization.
The general rigidity lemma and infinite periodic-walk argument
are written in full above; the parent positive and lower-period
theorems are specifically imported **with** their published
complete independent exact certificates, rather than claimed
reproved here.

The result extends the published sharp period 1122 theorem in
`../sqrt-minus-two-sqrt6-period/`, which previously gave one
successful seven-generator construction but did not prove generator
minimality or uniqueness. This note closes that gap without
changing the parent paper's frozen disclosure record. The
periodic-sieve framework traces to OpenAI/math family 028
(pinned commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`)
and the repository's quadratic-order manuscript 002.

The theorem does **not** identify the maximum connected component
of the actual irreducible graph at the norm-six step threshold,
which is a distinct still-open exact problem. No first-in-literature
claim, external peer review or full Lean formalization is made.
