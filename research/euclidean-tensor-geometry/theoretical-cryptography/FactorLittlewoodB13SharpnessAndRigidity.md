# Sharp one-sided escape and two-sided rigidity at digit cap 12

For an irrational real \(x=[a_0;a_1,a_2,\ldots]\) write
\(B(x)=\limsup_{i\to\infty}a_i\). Define
\[
 J_{12}=\min\{J:\text{every nonquadratic irrational }x
             \text{ has }\max_{0\le j\le J}B(2^jx)\ge13\}.
\]
The adjective nonquadratic excludes quadratic irrationals, not higher
algebraic irrationals. Let \(N(C)\) denote the different, two-sided invariant
in [Giraudin, Hexagon 2611.00009v1, §§1, 3 and 9](https://hexagonmath.org/pdf/2611.00009v1).

**Theorem.** \(J_{12}=41\), and \(41\le N(12)<\infty\).

The upper bound \(J_{12}\le41\) is the previously verified digit-cap-12
calculation in [*A lower bound of 13 in the B-variant of 2-adic Littlewood*](FactorLittlewoodBDoublingBound13.md).
The lower bound has a small exact witness independent of the large search.
The finiteness assertion answers the \(C=12\) case of the two-sided question
explicitly left open in the cited version of Giraudin. We do not give an
upper bound on \(N(12)\) or infer \(N(12)=41\). We do not settle the full
2-adic Littlewood conjecture.

## 1. A real, nonquadratic witness through level 40

Use
\[
 L=\begin{pmatrix}1&1\\0&1\end{pmatrix},\qquad
 R=\begin{pmatrix}1&0\\1&1\end{pmatrix},\qquad
 D_j=\begin{pmatrix}2^j&0\\0&1\end{pmatrix}.
\]
As in the previous note, the lengths of alternating \(L,R\) runs are the
regular continued fraction digits. A nonsingular nonnegative integral matrix
of positive determinant uniquely factors as \(W M\), where \(W\) is a word
in \(L,R\) and the rows of \(M\) are incomparable, or reduced. Repeatedly
subtract the dominated row, recording the correct letter, to compute this
factorization. A transducer state for a matrix \(g\) at an input prefix \(U\)
is the \(M\) in \(gU=WM\); the letters in \(W\) are the emitted output.

The [small companion certificate](verify_factor_littlewood_b13_supplement.js)
gives 40 initial matrices \(M_j\), with output-run counters, together with
two lists of run lengths \(A,B\). Every \(M_j\) is primitive (its entries
have greatest common divisor 1), nonnegative and reduced, and has determinant
\(2^j\). Their row lattices \(\Lambda_j=\mathbb Z^2 M_j\) are nested, with
\(M_0=I\). The two lists have respective lengths 41 and 57 and start with
different digits, 5 and 6. Starting at the given matrices and counters,
each list returns to all the initial states after normalizing the orientation,
and no output run exceeds 12. The companion checks these claims by exact
integer arithmetic, with no graph exploration.

For the orientation convention let \(J_0=\begin{pmatrix}0&1\\1&0\end{pmatrix}\).
At each boundary conjugate the current matrix by \(J_0\) if the next
input letter is \(R\); exchange saved output-letter names in the same case.
A normalized step thus always reads \(L^a\) for the next digit \(a\),
reduces, then conjugates the successor and exchanges the counter's letter
because the next input letter alternates. This is equivalent to the
unfolded calculation, since \(J_0LJ_0=R\), \(J_0RJ_0=L\) and reduction
commutes with this conjugation (with output letters exchanged).
Consequently an arbitrary right-infinite concatenation of \(A,B\) gives
a legitimate infinite input run sequence. The two lists are prefix-free
since their first digits differ; distinct binary choices give distinct run
sequences. There are uncountably many choices and only countably many
eventually periodic run sequences. Choose a non-eventually-periodic one,
and let \(\gamma>0\) be its continued fraction when the first letter is \(L\).
Thus \(\gamma\) is not quadratic.

At each level \(j\), starting from the actual matrix \(M_j\), the emitted
word is a prefix of the continued fraction of \(M_j\gamma\): the
unprocessed tail is positive and the residual matrix maps it to a positive
tail. Output lengths grow without bound. Indeed, the reduced matrices at
a fixed determinant are finite; a sufficiently long nonempty range of input
with no output would repeat a matrix under right multiplication by a
nonidentity positive word, contrary to invertibility. A possibly artificial
initial counter affects only the initial emitted run; after the first actual
output switch the counter records the actual last-run length. Every
later run is at most 12 by the checked transitions. Hence
\(B(M_j\gamma)\le12\) for \(1\le j\le40\), and the input itself has this
bound as well.

The certificate also supplies the unimodular matrix
\[
 P=\begin{pmatrix}-14733&-5926\\1891843&760949\end{pmatrix},
 \qquad \mathbb Z^2M_{40}=\mathbb Z^2D_{40}P .
\]
It checks the equality by testing \(M_{40}(D_{40}P)^{-1}\) integral and of
determinant one. The quotient by \(\Lambda_{40}\) is cyclic
(Smith normal form and primitivity). A finite cyclic \(2\)-group has a
unique subgroup of each order; hence each \(\Lambda_j\) equals
\(\mathbb Z^2D_jP\) by nesting and its index. Matrices with the same row
lattice differ by a left unimodular factor. Serret's continued fraction
equivalence theorem makes \(B\) invariant under all integral unimodular
Möbius maps. It follows that \(x=P\gamma\) is nonquadratic and
\[
                      B(2^j x)=B(M_j\gamma)\le12\qquad(0\le j\le40).
\]
This proves the sharpness assertion for \(J_{12}\). For provenance, the
two lists were extracted as returning walks with distinct first labels
from the level-40 retained graph of the earlier calculation (23,797
vertices and 23,799 internal edges). Their exact replay above, not those
counts or a graph-attribution assumption, certifies the lower bound.

## 2. The one-sided certificate applies to cyclic lattice chains

Now let \(\Lambda_0\supset\Lambda_1\supset\cdots\supset\Lambda_{41}\)
be nested row lattices in \(\mathbb Z^2\) of indices \(2^j\), all with
cyclic quotient, and let \(g_j\) be integer row bases of positive determinant.
If \(B(g_j\gamma)\le12\) for all \(j\) for an irrational real \(\gamma\),
then \(\gamma\) is quadratic and its eventual run-period occurs among
the finitely many cycles of the previous level-41 certificate.

Here is the extra justification required to apply that certificate.
Translate \(\gamma\) by an integer to make it positive, adjusting the row
bases by the same right unimodular coordinate change; neither the hypothesis
nor the eventual period changes. Replace each row basis by a nonnegative
one using row Hermite normal form; this left unimodular change preserves
\(B\). At a long input prefix \(U\), write \(g_jU=W_jM_j\). For
\(l=j-1\) or \(j-2\), \(Q=g_jg_l^{-1}\) is integral of determinant \(2\)
or \(4\); it is primitive because \(\Lambda_l/\Lambda_j\) is cyclic
(the Smith invariant factors can be computed in the row basis \(g_l\)).
As \(U\) lengthens, both columns of \(W_l\), normalized projectively with
positive coordinates, approach the positive ray \((g_l\gamma,1)\)
by shrinking continued fraction cylinders. There are arbitrarily many
output letters, by the fixed-determinant argument in §1.
The matrix \(Q\) maps \((g_l\gamma,1)\) to a positive multiple of
\((g_j\gamma,1)\), since both row bases are nonnegative.
It follows that \(QW_l\) is nonnegative for all sufficiently long prefixes.
It also remains primitive, as \(W_l\) is unimodular.

For determinant 2 or 4 the reachable small transducer states used by the
old certificate exhaust *all* primitive nonnegative reduced matrices of
that determinant. Indeed a reduced matrix of positive determinant \(D\)
satisfies \(a>c,\ d>b,\ 1\le a,d\le D\).
The companion enumerates these inequalities and the determinant,
discards the all-even matrices, and compares with the independent
closure under \(L,R\) starting at \(\operatorname{diag}(D,1)\).
Both sets are equal, of sizes 4 and 12. Thus
\[
                  M_j=\operatorname{red}(\operatorname{red}(QW_l)M_l)
\]
satisfies both the one- and two-level fibre restrictions of the old
certificate, eventually. For the finite chain, a common sufficiently large
prefix works for all \(j,l\). Its remaining digits and all output tails
satisfy the cap. The old suffix seeding, letter normalization and removal
of cross-component edges concern *eventual* forward paths, and therefore
still apply. At level 41 this graph has all out-degrees one among the
retained vertices. This proves the stated eventual-period conclusion.
The argument does not delete cross-component edges from the genuine
two-sided graph.

## 3. A bounded chain at a quadratic endpoint fixes its 2-adic line

Suppose \(g_j\) instead give an infinite chain of the same type.
Modulo \(2^j\), the kernel of \(g_j\) on columns is a primitive rank-one
direct summand by Smith normal form. These kernel lines are compatible
under reduction: from \(g_j=Q g_l\) for \(j>l\), multiplication by
\(\operatorname{adj}(Q)\) sends \(g_jv\equiv0\pmod{2^j}\) to
\(2^{j-l}g_lv\equiv0\pmod{2^j}\).
A primitive vector reducing from level \(j\) therefore generates the
kernel line at level \(l\). Choosing a coordinate that is odd modulo 2
and normalizing it to 1 yields a line \(\xi\) in \(\mathbb P^1(\mathbb Q_2)\).

Let \(\gamma\) be quadratic, with \(B(g_j\gamma)\le12\) for all \(j\).
Take a hyperbolic \(T\in\mathrm{SL}_2(\mathbb Z)\) with real attracting
fixed point \(\gamma\); a continued fraction period matrix, conjugated
by the preperiod and squared if needed, has this property.
We claim that \(\xi\) is an eigenline of \(T\).
If not, take a positive power \(S\) of \(T\) with \(S\equiv I\pmod4\).
The \(2\)-adic logarithm \(A=\log S\) and exponential converge in this
neighborhood and are inverses there. The matrix \(A\) commutes with \(S\)
and is not scalar (otherwise \(S=\exp A\) is scalar). Since \(S\) has
distinct eigenvalues and has the same eigenlines as \(T\), \(A\) has
those same eigenlines, as follows by diagonalizing \(S\) over a splitting
field. The analytic map
\[
                    t\longmapsto \exp(tA)\xi,\qquad t\in\mathbb Z_2,
\]
has nonzero derivative at \(0\) in a local projective coordinate: the
derivative vanishes exactly when \(A\) sends a representative of
\(\xi\) into its own line. Its range therefore contains an open
neighborhood of \(\xi\), by the \(2\)-adic inverse function theorem.
Choose a rational point in that range, represented by a primitive
integer column \(v_0\). Then \(\xi\) lies in the \(2\)-adic closure of
the integer \(S\)-orbit of \(v_0\) (reverse the parameter and use
density of integers in \(\mathbb Z_2\)).

For each \(j\) select an integer exponent placing \(S^n v_0\) in the
kernel line modulo \(2^j\). Adding arbitrarily large positive multiples
of the order of \(S\bmod 2^j\) preserves the congruence.
As \(n\to+\infty\) along this progression, write
\(S^n v_0=(p_n,q_n)^\top\).
Since the rational \(v_0\) is not a real eigenline, hyperbolic
diagonalization shows \(p_n/q_n\to\gamma,\ |q_n|\to\infty\) and
\(|q_n(q_n\gamma-p_n)|\le C_0\) eventually, with \(C_0\) independent of
\(j\). Indeed the growing and decaying real eigenline coefficients scale
as \(\lambda^n,\lambda^{-n}\) in absolute value, with \(\lambda>1\),
and the linear form \(q\gamma-p\) annihilates the growing eigenline.
The column \(g_j(p_n,q_n)^\top/2^j=(p'_n,q'_n)^\top\) is integral.
If \((c,d)\) is the bottom row of \(g_j\), the Möbius determinant identity
gives
\[
 |q'_n(q'_n g_j\gamma-p'_n)|
     =2^{-j}|q_n(q_n\gamma-p_n)|
          \left|\frac{cp_n/q_n+d}{c\gamma+d}\right|.
\]
At fixed \(j\) the last factor tends to one, and
\(|q'_n|\to\infty\) since \(c\gamma+d\ne0\).
It follows that \(\liminf_{q\to\infty}q\|q g_j\gamma\|\le C_0\,2^{-j}\).
This contradicts the continued fraction lower bound
\(1/(B(g_j\gamma)+2)\ge1/14\) for all \(j\).
Thus \(\xi\) is an eigenline of the period matrix. This argument
concerns a general cyclic chain; it does not assume the chain is
the fixed coordinate ray \(D_j\). For the related periodic
eigenvector criterion and degenerate Hecke branches, see
[Badziahin, Theorem 1](https://arxiv.org/abs/1406.3594v2) and
[Aka–Shapira, §4](https://arxiv.org/abs/1201.1280v2).

## 4. Two-sided periodicity at cap 12

By [Giraudin, §3](https://hexagonmath.org/pdf/2611.00009v1#page=2),
\(X_C^{(n)}\) consists of the two-sided digit labels of paths in the
true synchronous automaton from the joint closure of the \(D_j\),
with the bounded output-run counters and bidirectional pruning.
Choose \(w\in X_{12}=\bigcap_n X_{12}^{(n)}\).
For each \(n\) there is a two-sided path for \(w\) through levels \(0,\dots,n\).
For fixed time positions and levels the state sets are finite.
Diagonal extraction gives a compatible path at all positions and
levels. Restore the alternating input letters \(L,R\).
At any run boundary the matrices \(g_j=M_j(0)\) have nested cyclic row
lattices: every finite tuple is in the genuine joint closure, so for
a common prefix \(U\) its states satisfy \(D_jU=W_jM_j(0)\).
The row lattices of these states are exactly the nested lattices of
\(D_jU\), with cyclic quotient.

At the boundary, the future input defines a positive irrational \(\alpha\);
the past inverse word on the negative half-line defines a negative
irrational \(\beta\). Both have bounded digits at every level. For the
future this follows by reading the forward output starting at \(M_j(0)\),
as in §1. For the past, let \(U_m\) be the input segment of \(m\) runs
ending at the boundary, and \(V_{j,m}\) its emitted word. Then
\[
 M_j(-m)U_m=V_{j,m}M_j(0),\qquad
 M_j(0)^{-1}V_{j,m}^{-1}y=U_m^{-1}M_j(-m)^{-1}y .
\]
For fixed \(y<0\), \(M_j(-m)^{-1}y\) stays in the negative half-line,
since the \(M_j(-m)\) are nonnegative of positive determinant.
The intervals \(U_m^{-1}(-\infty,0)\) shrink to \(\beta\) by
continued fraction cylinder convergence: conjugating by negation
transforms \(L^{-1},R^{-1}\) to \(L,R\), in reversed order from the
past segments. Therefore the right-hand side tends to \(\beta\).
Similarly \(V_{j,m}^{-1}y\) tends to the negative output endpoint;
the output lengths tend to infinity by the same finite-state argument
as before, and all output runs are bounded by 12. By continuity of
\(M_j(0)\) at the irrational \(\beta\), this endpoint equals
\(M_j(0)\beta\). Negation preserves \(B\) by unimodular equivalence.
Thus \(B(g_j\alpha),B(g_j\beta)\le12\) at every level for the same chain.

Section 2 now makes both endpoints quadratic, and §3 makes the same
\(\xi\) an eigenline of both integral period matrices. Their irreducible
quadratic fixed-point polynomials share a root in \(\mathbb Q_2\),
so are proportional over \(\mathbb Q\); the root cannot be the
rational point at infinity. The opposite signs of the endpoints
show that they are the two distinct real conjugates.

Choose the boundary immediately before an \(L\)-run, after an \(R\)-run.
Then \(\alpha>1\) and \(-1<\beta<0\). By the Galois criterion the
continued fraction of \(\alpha\) is purely periodic at this boundary.
A period matrix (repeating the digit period twice if necessary to
return to the same letter) has \(\alpha\) as attracting endpoint and
\(\beta\) as the other endpoint. Extending the future period to the
left gives backward limit \(\beta\); its backward digit expansion is
unique, by irrationality and continued fraction coding. Thus the
given two-sided word is exactly that periodic extension.
Section 2 places its eventual right period among the finite level-41
cycle list, so only finitely many two-sided periodic orbits can occur.
It follows from [Giraudin, Proposition 11](https://hexagonmath.org/pdf/2611.00009v1#page=7)
that \(N(12)<\infty\).

Finally use the genuine real witness \(x\) from §1 (translate it by an
integer to be positive, if needed; all the digit bounds are unchanged).
Its actual \(D_j\) transducer tuple follows a right-infinite trajectory in the true
joint-closure graph for \(j\le40\), after discarding a prefix long
enough for every digit cap to hold. It eventually stays in one
strongly connected component; one can extend this suffix infinitely
to the left inside that component by taking a closed walk through its
initial vertex. The resulting path survives bidirectional pruning.
Its future labels are not eventually periodic, since \(x\) is
nonquadratic. Thus \(X_{12}^{(40)}\) contains a nonperiodic word,
and \(N(12)>40\). This last argument is about the true graph, not the
forward enlarged graph used to locate the small witness.

## 5. Reproduction

Run the companion verifier with Node.js to check the two independent
finite ingredients: the small determinant state lists and the explicit
depth-40 witness (both returning blocks across all 40 matrices, nested
lattice tests, and the unimodular change of variable). For the application
of the earlier level-41 cap certificate, run
`node --expose-gc verify_factor_littlewood_b13.js 12 41`.
It ends at level 41 with 23,464 retained states and 23,464 internal edges.
The \(2\)-adic and two-sided arguments above are independent of any
search for \(N(12)\).
