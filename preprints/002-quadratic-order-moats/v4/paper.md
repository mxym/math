# Optimal scalar period for the Gaussian eight-neighbor principal-ideal sieve

**mxym — AI-assisted research manuscript. Entry 002, version 4, 7 October 2026.**

This note continues entry 002 version 3. The earlier version gave an exact
principal-ideal periodic-sieve certificate for the eight nearest coefficient
steps in \(\mathbb Z[i]\), with common scalar period \(130\), and exhibited
one smaller candidate of period \(30\) having a nonzero-voltage walk. Here we
prove that \(130\) is the **smallest possible common scalar period in the
entire finite principal-ideal certificate class of version 3**.

The proof has two parts. An elementary Gaussian-integer reduction shows that
for lower-bound purposes every finite principal-ideal sieve of period \(Q\)
is dominated by the sieve formed from all Gaussian prime ideals lying over
the rational prime divisors of \(\operatorname{rad} Q\). The remaining
finite statement is certified by explicit nonzero-voltage walks for every
squarefree \(q<130\). The successful \(q=130\) endpoint is the independently
replayed version-3 certificate.

No claim is made that period \(130\) is optimal among every conceivable
proof of bounded Gaussian-prime walks. The theorem is an optimality result
for the precise principal-ideal periodic-sieve framework defined below.

## 1. The finite sieve

Identify \(\mathbb Z[i]\) with \(\mathbb Z^2\). Let
\[
F_8=\{-1,0,1\}^2\setminus\{(0,0)\}.
\]

For a nonzero nonunit
\[
\alpha=a+bi\in\mathbb Z[i],
\]
version 3 defines its scalar period
\[
 t(\alpha)=\frac{a^2+b^2}{\gcd(|a|,|b|)}.
 \tag{1.1}
\]
Equivalently, \(t(\alpha)\) is the least positive integer \(t\) such that
\[
 t\mathbb Z[i]\subseteq(\alpha).
 \tag{1.2}
\]

For a finite list
\[
\mathcal G=(\alpha_1,\ldots,\alpha_m)
\]
of nonzero nonunits, put
\[
 Q(\mathcal G)=\operatorname{lcm}_{j}t(\alpha_j)
\]
and
\[
 A(\mathcal G)
 =
 \mathbb Z[i]\setminus\bigcup_{j=1}^m(\alpha_j).
 \tag{1.3}
\]
The associated avoiding graph is the induced \(F_8\)-step graph on
\(A(\mathcal G)\).

A **successful principal-ideal periodic sieve** means that every connected
component of this avoiding graph is finite. By the voltage theorem in
version 3, this is equivalent to the existence of an integer potential on
the complete quotient graph modulo \(Q(\mathcal G)\).

The empty list has \(Q=1\) and the full lattice as its avoiding graph, so it
is unsuccessful.

## 2. Maximal prime sieve at a fixed radical

For a squarefree positive integer \(q\), define
\(\mathcal P(q)\) as follows. For every rational prime \(p\mid q\), include

- the ideal \((1+i)\) if \(p=2\);
- both conjugate Gaussian prime ideals above \(p\) if
  \(p\equiv1\pmod4\);
- the inert prime ideal \((p)\) if \(p\equiv3\pmod4\).

Choose arbitrary generators for these ideals and put
\[
 A_{\max}(q)
 =
 \mathbb Z[i]\setminus\bigcup_{\mathfrak p\in\mathcal P(q)}\mathfrak p.
 \tag{2.1}
\]
The set is independent of the chosen associate generators.

### Lemma 2.1. Radical domination

Let \(\mathcal G\) be any finite principal-generator list and put
\[
 Q=Q(\mathcal G),\qquad q=\operatorname{rad}Q.
\]
Then
\[
 \boxed{A_{\max}(q)\subseteq A(\mathcal G).}
 \tag{2.2}
\]

Consequently, if the \(F_8\)-graph on \(A_{\max}(q)\) has an infinite
component, then \(\mathcal G\) cannot be a successful sieve.

**Proof.**
Fix \(\alpha\in\mathcal G\). By (1.2),
\[
 t(\alpha)=\alpha\beta
\]
for some \(\beta\in\mathbb Z[i]\). Choose a Gaussian prime
\(\pi\mid\alpha\). Then \(\pi\mid t(\alpha)\) as a Gaussian integer.

Let \(p\) be the rational prime below \(\pi\). We claim
\[
 p\mid t(\alpha)
 \tag{2.3}
\]
in \(\mathbb Z\). This is immediate if \(\pi\) is associate to an inert
rational prime \(p\equiv3\pmod4\). If \(\pi\) lies over a split prime
\(p\equiv1\pmod4\), taking norms gives
\[
 p=N(\pi)\mid t(\alpha)^2,
\]
hence \(p\mid t(\alpha)\). If \(\pi\) is associate to \(1+i\), divisibility
of a rational integer by \(1+i\) forces that integer to be even, so again
\(p=2\mid t(\alpha)\).

Because \(t(\alpha)\mid Q\), equation (2.3) gives \(p\mid q\). Thus
\((\pi)\) is one of the prime ideals appearing in \(\mathcal P(q)\).
Since \(\pi\mid\alpha\),
\[
 (\alpha)\subseteq(\pi).
\]
Therefore every point excluded by \((\alpha)\) is also excluded by the
maximal prime sieve. Taking the union over \(\alpha\in\mathcal G\) gives
\[
 \bigcup_{\alpha\in\mathcal G}(\alpha)
 \subseteq
 \bigcup_{\mathfrak p\in\mathcal P(q)}\mathfrak p,
\]
which is equivalent to (2.2).

An infinite path contained in \(A_{\max}(q)\) is also contained in
\(A(\mathcal G)\). This proves the final assertion. \(\square\)

### Remark 2.2

This reduction explains why composite principal generators cannot improve a
period lower bound. They may be useful for compact explicit certificates,
but every such ideal is contained in a Gaussian prime ideal whose rational
prime already divides the common scalar period.

## 3. Exact finite obstruction below 130

A nonzero-voltage quotient walk gives an explicit infinite component after
periodic lifting. For each squarefree \(q<130\), the accompanying certificate
stores such a walk in \(A_{\max}(q)\).

### Proposition 3.1. Exhaustive radical obstruction

For every squarefree integer
\[
 1\le q<130,
\]
the \(F_8\)-step graph on \(A_{\max}(q)\) has an infinite connected
component.

More precisely, for each of the 79 squarefree integers in this range the
certificate supplies a point \(x_q\in A_{\max}(q)\) and a finite
\(F_8\)-step walk
\[
 x_q=x_0,x_1,\ldots,x_L
\]
such that every \(x_j\in A_{\max}(q)\) and
\[
 x_L-x_0=qv_q
 \qquad\text{for some }v_q\in\mathbb Z^2\setminus\{0\}.
 \tag{3.1}
\]
Hence the projected walk is closed modulo \(q\) with nonzero voltage, and
its periodic translates concatenate to an infinite walk.

**Exact verification.**
The file code/period_optimality.json contains all 79 witnesses.
The independent checker code/check_period_optimality.py:

1. reconstructs the complete list of squarefree \(q<130\);
2. factors each \(q\) by exact integer arithmetic;
3. reconstructs the Gaussian prime generators over every rational
   \(p\mid q\);
4. tests ideal membership directly by
   \[
   a x+b y\equiv0\pmod{a^2+b^2},\qquad
   -b x+a y\equiv0\pmod{a^2+b^2};
   \tag{3.2}
   \]
5. checks every stored step is in \(F_8\);
6. checks every visited lattice point avoids every prime ideal;
7. verifies (3.1) and \(v_q\ne0\);
8. recomputes the number of allowed quotient residues.

There are 5009 stored steps in total, and no witness has more than 129
steps. All decisions are exact integer decisions.

The generator script is included only for reproducibility. The checker does
not import it or trust its search state.

## 4. The sharp period theorem

### Theorem 4.1. Minimal principal-sieve period for Gaussian \(F_8\)

Let \(\mathcal G\) be any finite list of nonzero nonunit Gaussian integers.
If the \(F_8\)-step graph on
\[
 \mathbb Z[i]\setminus\bigcup_{\alpha\in\mathcal G}(\alpha)
\]
has only finite connected components, then
\[
 \boxed{Q(\mathcal G)\ge130.}
 \tag{4.1}
\]

The bound is attained. In particular the minimal common scalar period among
all successful finite principal-ideal periodic sieves for \(F_8\) is exactly
\[
 \boxed{130.}
\]

**Proof.**
Suppose \(Q(\mathcal G)<130\), and put \(q=\operatorname{rad}Q(\mathcal G)\).
Then \(q<130\). Lemma 2.1 gives
\[
 A_{\max}(q)\subseteq A(\mathcal G).
\]
By Proposition 3.1 the \(F_8\)-graph on \(A_{\max}(q)\) has an infinite
component, witnessed by a nonzero-voltage walk. The same walk lies in
\(A(\mathcal G)\), contradicting success.

For the upper endpoint, take
\[
 \mathcal G_0=
 \{1+i,\ 2+i,\ 2-i,\ 3+2i,\ 3-2i\}.
 \tag{4.2}
\]
Their scalar periods are
\[
 2,5,5,13,13,
\]
whose least common multiple is \(130\). Entry 002 version 3 supplies the
complete quotient potential for this list. The present checker independently
replays that historical certificate using the version-3 verifier and
confirms common period \(130\), 4608 allowed residues, and maximum quotient
component size \(580\). Therefore \(\mathcal G_0\) is successful, proving
attainment. \(\square\)

### Corollary 4.2. The period-30 failure is not exceptional

The rejected version-3 \(Q=30\) candidate is one instance of a complete
lower-period obstruction: **every** finite principal-ideal \(F_8\) sieve
with common scalar period below \(130\) fails.

Thus replacing the period-30 generators by other principal generators,
including ramified, inert, split, nonprimitive, or composite-norm elements,
cannot produce a successful certificate of smaller period.

## 5. Relation to irreducible-component bounds

The theorem concerns the finite periodic obstruction used to control the
graph on Gaussian irreducibles. It does not change the successful
version-3 numerical component bound.

For the period-130 certificate, the exact replay gives
\[
 B=580
\]
for the largest avoiding quotient component. The Gaussian finite-exception
enumeration from version 3 has 20 exceptional elements and yields the
conservative full irreducible-component bound
\[
 92820.
\]
The new conclusion is that no certificate in the full finite
principal-ideal class can lower the **common scalar period** below \(130\).
It does not assert that \(92820\) is the optimal component bound, nor that
every proof with a different kind of periodic obstruction must have period
at least \(130\).

## 6. Reproduction and proof boundary

From the v4 directory run

~~~sh
python3 code/check_period_optimality.py
python3 -O code/check_period_optimality.py
~~~

The two outputs must be byte-identical. The recorded output is in
results/replay.txt.

To regenerate the negative witnesses:

~~~sh
python3 code/generate_period_optimality.py
~~~

The generator writes the same schema used by the checker; regeneration is
not required for verification.

The new mathematical dependencies are only the elementary Gaussian-prime
classification and the scalar-period lemma already proved in version 3.
The successful endpoint imports the fixed version-3 exact certificate.
No analytic entropy theorem is needed for the period optimality statement
itself.

This is a research proof draft with exact finite certificates. It is not
Lean-formalized or externally peer reviewed, and no literature-priority
claim is made.
