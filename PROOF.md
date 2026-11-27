# Conflict-checkable and local-to-global near-MDS codes

**Theorem.** Fix integers \(n\ge3\), \(2\le d\le n-1\), and
\(\epsilon>0\). For unbounded finite alphabet sizes \(q\), there
is a code \(C\subseteq\mathcal A^n\) of minimum Hamming distance
exactly \(d\) with \(\log_q|C|\ge n-d+1-\epsilon\).
Every assignment on at least \(n-d+1\) positions that is
pairwise compatible extends to a codeword. Compatibility means
that the two symbols occur together in some actual codeword.
In particular, a full assignment is a word precisely when its
conflict graph is empty, so the code is conflict-checkable in the
sense of Applebaum–Kachlon. The partial extendability assertion
is their local-to-global consistency.

Write \(t=n-d\), so \(1\le t\le n-2\). The comparison-based ceiling
in their Theorem 1.8 is \((t+2)/2\); the examples here can have
dimension arbitrarily close to the Singleton upper bound \(t+1\).
They answer the non-endpoint conjecture positively (choose
\(1<d<n-1\) and \(\epsilon<t/2\)). The endpoint \(d=n-1\)
was already settled in the source.

## 1. An order and separated abscissas

There is a totally real number field \(K\) with a monogenic order
\(R=\mathbb Z[\theta]\) such that every residue field of \(R\) at
a maximal ideal has size greater than \(n\). Here an order is a
subring that is free of rank \(s=[K:\mathbb Q]\) over \(\mathbb Z\)
and spans \(K\) over \(\mathbb Q\). For this construction choose
\(s\) with \(2^s>n\) and, for every prime number \(p\le n\),
a monic irreducible polynomial of degree \(s\) over
\(\mathbb F_p\). These polynomials exist by finite-field theory.
Their lower coefficients specify one residue class each modulo
the product \(M\) of these primes. For a large integer \(U\), start
with \(\prod_{j=1}^s(X-jU)\). Change the nonleading coefficients
by integers of magnitude less than \(M\) to fit those classes.
At the ends \((j\pm1/4)U\) of each of \(s\) disjoint intervals,
the starting polynomial has opposite signs and magnitude at least
\(c_s U^s\) for some \(c_s>0\). The changes in its values are
\(O_{s,M}(U^{s-1})\). For sufficiently large \(U\) the new monic
polynomial \(F\) thus has distinct roots in all the intervals,
so all roots are real. It is irreducible over \(\mathbb Q\) by
monicity and irreducibility modulo 2. Put \(K=\mathbb Q(\theta)\)
for any one root. Then \(R\cong\mathbb Z[X]/(F)\) has basis
\(1,\theta,\ldots,\theta^{s-1}\).

For every maximal ideal \(\mathfrak m\) of \(R\), the field
\(R/\mathfrak m\) has positive characteristic: its additive
group is a quotient of the finitely generated abelian group
\(R\), and a characteristic-zero field contains the additive
group \(\mathbb Q\), which cannot be a subgroup of a finitely
generated abelian group. If the characteristic \(p\) is at most
\(n\), then \(R/(p)\cong\mathbb F_p[X]/(F\bmod p)\) is already a
field of size \(p^s>n\) and \(\mathfrak m=(p)\). Otherwise its
residue field contains \(\mathbb F_p\) with \(p>n\).
Every such quotient is finite, since it is a quotient of the
finite ring \(R/(p)\). Integral closure of \(R\) is not needed.

Choose distinct \(x_1,\ldots,x_n\in R\) so that no **three** reduce
to the same value modulo any maximal ideal. This can be done
inductively. A nonzero \(u\in R\) lies in only finitely many
maximal ideals, because \(R/uR\) is a finite abelian group:
multiplication by \(u\) is a nonsingular rational matrix on \(K\)
and an integer matrix on the basis of \(R\). Thus the old nonzero
pair differences meet only finitely many maximal ideals. At
each of those ideals choose a new residue distinct from the
residues of all old abscissas, possible since the residue field
has more than \(n\) elements. Distinct maximal ideals are
comaximal, so the Chinese remainder theorem supplies an element
with the specified residues. Adding any multiple of the product
of the finitely many residue characteristics preserves them
(the empty product is 1); we can therefore make the new point
distinct in \(R\) as well. A triple containing the new point
cannot collide: the ideal would already contain the difference
of the two old points, and was avoided.

## 2. Integral interpolation from divided differences

Let a set of \(h\ge1\) distinct abscissas from §1 be assigned
values \(z_i\in R\). Assume that for each pair,
\[
 z_j-z_i\in(x_j-x_i)R. \tag{1}
\]
Then the unique degree-less-than-\(h\) interpolating polynomial
over \(K\) has all its coefficients in \(R\).

To prove this, fix any maximal ideal \(\mathfrak m\) and work in
the localization \(R_{\mathfrak m}\) at elements outside it.
Group the abscissas by their residues modulo \(\mathfrak m\).
Each group has at most two points. A singleton is fitted by
a constant; for a pair of points the affine line with the
divided difference from (1) fits over \(R\), hence over the
local ring. For a group \(J\) impose this constant or affine
polynomial modulo the monic product
\(\prod_{j\in J}(X-x_j)\). Factors from different groups generate
comaximal ideals: the difference of their abscissas is a
unit in \(R_{\mathfrak m}\). The products for different groups
also generate pairwise comaximal ideals. Indeed, if an ideal
is comaximal with several other ideals, multiplying
representatives of 1 modulo the first in each of the other
ideals shows it is comaximal with their product; apply this
on both sides. Polynomial Chinese remaindering and division
by the product of all monic factors give a polynomial of
degree less than \(h\) over \(R_{\mathfrak m}\) taking the desired
values. Over \(K\) it must be the unique interpolant.

Finally \(\bigcap_{\mathfrak m}R_{\mathfrak m}=R\) inside \(K\).
For if \(v\in K\setminus R\), the proper denominator ideal
\(\{u\in R:uv\in R\}\) lies in a maximal ideal \(\mathfrak m\);
membership in \(R_{\mathfrak m}\) would give a denominator
outside that ideal, a contradiction. Apply the intersection
to each coefficient. The same lemma holds componentwise
for \(R^L\)-valued interpolation.

## 3. Codes from whole Gram levels

Fix integers \(L,T\ge1\) and the number field and abscissas
above. In \(R^L\), for each \(1\le r\le t\) choose initial
coefficient vectors \(A_r\) whose entries in the power basis
have integer coefficients in \([-T,T]\). Among their symmetric
Gram matrices choose one \(G\) realized by at least one
tuple in this box. Define the **whole** Gram level
\[
 \mathcal F_G=\{(A_1,\ldots,A_t)\in(R^L)^t:
                 \textstyle\sum_\ell A_{r,\ell}A_{u,\ell}=G_{ru}
                  \text{ for all }r,u\}.
\]
In every real embedding \(\sigma:K\to\mathbb R\), the initial
box guarantees a bound \(|\sigma(A_{r,\ell})|\le C_0T\)
for a constant \(C_0\) depending only on the power basis.
For an arbitrary member of the whole level, the image of
\(G_{rr}\) is a sum of squares unchanged from that initial
tuple. Thus all such coordinates have
\(|\sigma(A_{r,\ell})|\le\sqrt L\,C_0T\). In particular,
\(\mathcal F_G\) is finite: the map from power-basis coefficients
to all embedding values is invertible, so all basis coefficients
are bounded. We use the positivity of the embeddings rather
than a restriction to the counting box for closure.

For a pair of positions define its genuine lifted difference
\[
 D_{ij}(A)=\sum_{r=1}^{t}(x_j^r-x_i^r)A_r\in (x_j-x_i)R^L.
\]
For fixed \(n,d,L,R,x_i\), every real embedding of every
coordinate of \(D_{ij}(A)\) is bounded in absolute value
by \(C_1T\), with \(C_1\) independent of \(G,T\).
Choose a rational prime \(P\) larger than
\[
 1+3C_1T+2\sqrt L\,C_0T+
               \max_{i<j}|N_{K/\mathbb Q}(x_j-x_i)|.
 \tag{2}
\]
By Bertrand's postulate, it can be chosen \(O(T)\) with a
constant depending only on the fixed parameters, and large
choices of order \(T\) are possible. The norm of a nonzero
element of \(R\) is a nonzero integer: it is the determinant
of multiplication in the chosen integer basis of the order, equivalently the
product of the real embedding values. If a nonzero element
of \(PR\) were of absolute value less than \(P\) in every
embedding, its quotient by \(P\) would have norm of absolute
value less than 1. This is impossible. This observation will
rule out modular wrap even if \(R/(P)\) is not a field.
Each \(x_j-x_i\) is a unit in \(R/(P)\): its multiplication
matrix has determinant coprime to \(P\), hence invertible
modulo \(P\), and so multiplication attains 1.

Take alphabet \(\mathcal A=(R/(P))^L\) of cardinality \(q=P^{sL}\).
The code consists of the vector evaluations
\[
 y_i=Z+\sum_{r=1}^t x_i^r A_r \pmod{PR^L},
       \qquad Z\in(R/(P))^L,\quad (A_1,\ldots,A_t)\in\mathcal F_G.
 \tag{3}
\]
A pair is compatible precisely if its difference modulo \(PR^L\)
comes from a genuine \(D_{ij}(A)\): the free offset can match
the first symbol. A compatible pair's small integer difference
lift \(D_{ij}\) is unique, by the archimedean bound
\(2C_1T<P\) and the observation following (2). In any compatible
triple, \(D_{ij}+D_{jk}-D_{ik}\) is zero modulo \(PR^L\), and
each embedding has coordinate magnitude at most \(3C_1T<P\);
thus the equality also holds in \(R^L\). No congruence of norms
alone is used as a pair test.

## 4. A compatible partial assignment extends

Fix any compatible set of \(h\ge t+1\) observations. Choose a
root index \(o\) (the smallest present) and write
\(U_j=D_{oj}\) for other observed indices, \(U_o=0\).
Then \(U_k-U_j=D_{jk}\) for each other pair \(j<k\).
For any reference tuple \((A^0_r)\in\mathcal F_G\) write
\[
 U_j^0=\sum_r(x_j^r-x_o^r)A_r^0 .
\]
The squared length of each \(D_{jk}\), computed using the
bilinear form \(\langle u,v\rangle=\sum_\ell u_\ell v_\ell\)
over \(K\), is determined by \(G\) and \(x_j,x_k\).
Thus \(\langle U_j,U_j\rangle\) and
\(\langle U_j-U_k,U_j-U_k\rangle\) equal their
reference values. Polarization gives equality of the
entire Gram matrices of \((U_j)\) and \((U_j^0)\).

The difference rows \((x_j^r-x_o^r)_{r=1}^t\) for any
\(t\) distinct non-root indices form an invertible \(t\)-by-\(t\)
matrix \(H\) over \(K\). Indeed a polynomial without constant
of degree at most \(t\) which takes the same value at those
\(t\) abscissas and at \(x_o\) must be constant, hence zero.
Solve \(HA^*=U\) using those rows. Applying the inverse matrix
to the equal Gram matrices shows
\(\langle A_r^*,A_u^*\rangle=G_{ru}\).
For any further index \(j\), write its difference row as a
linear combination of the rows of \(H\).
For the reference values it is the same linear combination.
The difference between the actual \(U_j\) and that combination
of the actual basis values has squared length zero, by the
Gram equality. That vector is zero: apply any real
embedding to its squared length and use positivity of real
sums of squares, then injectivity of the embedding.
Thus a single polynomial with nonconstant coefficients \(A^*\)
and with constant term chosen to vanish at \(x_o\) takes all
the values \(U_j\) at their abscissas.

For the selected \(t+1\) abscissas the value differences are
genuine \(D_{jk}\), so (1) holds. By §2 their unique interpolating
polynomial, degree at most \(t\), has coefficients in \(R^L\).
It is exactly the polynomial just found. In particular
\(A^*\in\mathcal F_G\). Its free offset in (3) can match the
actual residue label at the root, and the small lifted
differences then match every residue label. This proves local
extendability for every \(h\ge t+1\), including \(h=n\).
The latter establishes conflict-checkability.

## 5. Size and minimum distance

Fix \(n,d,L,R,x_i\) while \(T\to\infty\).
In the basis of \(R\), every coordinate of a Gram entry of
the counting box is \(O(T^2)\) by the fixed multiplication
structure constants, number \(L\) of summands, and degree
\(s\). Thus the number of Gram matrices realized by
\((2T+1)^{stL}\) ordered coefficient tuples is
\(O(T^{s t(t+1)})\), using \(t(t+1)/2\) entries and
\(s\) coordinates each. Choose \(G\) with a largest class
in this box. Then \(|\mathcal F_G|\ge c_1 T^{stL-s t(t+1)}\)
for a constant \(c_1>0\).

Reduction of the nonconstant coefficient tuples is injective:
a nonzero difference has magnitude less than \(P\) in each
embedding by (2) and so cannot belong to \(PR\).
Over \(R/(P)\) a Vandermonde matrix on any \(t+1\) inputs
has a unit determinant because all pair differences are
units, so evaluation (3) on those positions is injective
on the polynomial coefficients, including the offset.
Consequently \(|C|=q|\mathcal F_G|\) and the minimum distance
is at least \(n-t=d\). No finite-field hypothesis on \(R/(P)\)
is needed; the unit determinant guarantees invertibility
by the adjugate identity for commutative rings.

Let \(\eta=\min(\epsilon,1/2)\) and choose \(L>t(t+1)/\eta\).
Since \(P\le C_2 T\) with fixed constant \(C_2\), we have
\[
 \frac{|C|}{q^{t+1-\eta}}
 \ge c_3 T^{s(\eta L-t(t+1))}\longrightarrow\infty .
\]
For large \(T\), our code thus has \(k\ge t+1-\eta\)
and more than \(q^t\) words. A projection onto any fixed
\(t\) positions cannot be injective, so some distinct words
agree on these positions. This proves that the minimum
distance is exactly \(d\). Condition (2) and the freedom to
choose increasing primes of order \(T\) give unbounded \(q\).
