# Large odd primes in signed automorphisms of a Hadamard matrix of order 2396

Let \(H\) be a real Hadamard matrix of order \(n=2396=4\cdot599\),
if one exists, and let
\[
G=\{(P,Q):P,Q\text{ signed permutation matrices},\quad PH=HQ\}.
\]
The following are necessary restrictions on the **full signed group**,
not on a prescribed sequence or block construction.

**Theorem.** A prime \(q\ge29\) dividing \(|G|\) must be in the table.
It divides \(|G|\) only to the first power. Every element \(g\) of order
q fixes f row labels and f column labels, with t moving cycles on each
side. If \(C=C_G(g)\), \(N=N_G(\langle g\rangle)\), their odd prime
divisors other than q are contained in the indicated sets.

| q | f | t | allowed other odd primes of C | allowed other odd primes of N |
|---:|---:|---:|:---|:---|
| 29 | 76 | 80 | 3, 5, 19 | 3, 5, 19 |
| 31 | 40 | 76 | 3, 5, 7, 19 | 3, 5, 7, 19 |
| 37 | 28 | 64 | 3, 5, 7 | 3, 5, 7 |
| 59 | 36 | 40 | 3, 5 | 3, 5 |
| 149 | 12 | 16 | 3 | 3 |
| 199 | 8 | 12 | none | 3 |
| 599 | 0 | 4 | none | none |

In particular, elements of two distinct primes from this table cannot
commute. The odd part of \(|N|\) is \(149\) or \(447\) when \(q=149\),
and \(199\) or \(597\) when \(q=199\). For \(q=199\), an order-three
element of N, if present, acts nontrivially by conjugation on
\(\langle g\rangle\), fixes all eight q-fixed positions, preserves
each moving q-orbit as a set, and fixes 20 actual positions on each side.

The smallest unknown order in the
[Egan–Kotsireas–London–Ó Catháin survey](https://arxiv.org/abs/2610.27175v2)
is 2396. We import [Davis's independent exclusion of order 479](https://itsdavis.com/solved-conjectures/results/hadamard-2396/automorphisms/).
For q=599 the existing [order-599 orbit classification](Hadamard2396OrbitNormalizer.md)
already proves a stronger quaternionic normalizer statement; the
q=599 row is included for completeness and is not a new q=599 result.
No matrix is constructed; none of the listed primes is asserted to
occur. In particular, this does not resolve the order-2396 existence
question.

## 1. Pure odd actions and two elementary fixed-block tests

Both projections of G to signed permutations are injective, since
H is invertible. For an odd-order subgroup, simultaneously remove the
signs from its row action by a diagonal sign conjugation: on each label
orbit, orient a single coordinate line and transport its orientation
by the subgroup. This is well-defined, since any point stabilizer has
odd order and acts trivially on the two orientations. Do the same on
columns. Replace H by its corresponding signed row/column transform.
Now the two actions are ordinary permutations. For each element
their traces (and the traces of all powers) coincide since H
intertwines them. In particular, the cycle types on both sides agree.

For an element of odd prime order q, put \(n=f+qt\), \(t>0\).
With A the \(f\times f\) fixed block, let B record one entry at a moved
column orbit in each fixed row. Then \(B\in\{\pm1\}^{f\times t}\) and
\[
AA^{\mathsf T}+qBB^{\mathsf T}=nI_f.
\tag{1}
\]
In particular \(qf\le n\), since every column of B has squared
norm f and \(\|B\|_{\mathrm{op}}^2\le n/q\). The diagonal of
\(AA^{\mathsf T}\) is f and its off-diagonal entries are multiples
of q.

* If \(f<q\), or if f is even and \(f<2q\), these off-diagonal
  entries vanish. For \(f\ge2\), an f-square Hadamard A requires
  \(f=2\) or \(4\mid f\), and \(BB^{\mathsf T}=tI\) requires t
  even for \(f=2\) and \(4\mid t\) for \(f\ge3\). The latter facts
  follow by normalizing the first sign row and considering the
  four sign pairs of the next two rows.
* If f is odd and \(q\le f<3q\), every off-diagonal entry is
  \(\pm q\). Write \(\eta_i\) for the parity sign of the number of
  negative coordinates of row i of A. Modulo four the row dot
  product is \(f\eta_i\eta_j\). Thus \(AA^{\mathsf T}=(f-\sigma q)I+
  \sigma q\,\eta\eta^{\mathsf T}\), where \(\sigma=1\) if
  \(f\equiv q\bmod4\), and \(-1\) otherwise. For \(\sigma=-1\)
  positivity requires \(f-(f-1)q\ge0\). For \(\sigma=1,\ f>q\),
  its determinant \((f-q)^{f-1}(f+(f-1)q)\) must be a square, so
  \(f+(f-1)q\) is a square. These two arguments only use the
  fixed Gram off-diagonal divisibility. In particular, the
  \(\sigma=-1\) contradiction at f=5, q=3 applies also when the
  permutation element has order 9.

After the arithmetic filter in §2, all retained \(q\ge29\) with
\(f>0\) have \(AA^{\mathsf T}=fI\) by the first test, except for
\((q,f)=(29,76)\). In this exception, partition the rows by
their parity sign. A row dot product off the diagonal is \(0\)
within a class, and \(\pm58\) across classes: use the congruences
modulo 4 and 29 and magnitudes at most 76. If both classes have
sizes \(a,b>0\), their rectangular cross matrix has norm at least
\(58\sqrt{\max(a,b)}\ge58\sqrt{38}>76\) by its row and column norms.
The Gram matrix with constant diagonal 76 and that bipartite
off-diagonal block is not positive semidefinite, a contradiction.
Thus \(AA^{\mathsf T}=fI\) and \(BB^{\mathsf T}=tI\) for every
retained q with f positive.

## 2. Cyclotomic parity and the large-prime list

More generally, let an odd-order element have order m. Its primitive
\(m\)-th root eigenspace on either side comes exactly from the cycles
of length m, with multiplicity k the number of such cycles. In the
normalized Fourier basis from these cycles, the H map is represented
by a k-square matrix over \(\mathbb Z[\zeta_m]\): an entry is a
length-m cyclic block Fourier sum, and equal orbit lengths cancel
the normalization factor. Orthogonality gives \(XX^\ast=nI\), so
\(\alpha\bar\alpha=n^k\) for \(\alpha=\det X\).

If \(\ell\) is an odd prime dividing n exactly once, \(\ell\nmid m\),
and \(-1\) is in the subgroup generated by \(\ell\) modulo m, each
prime above \(\ell\) in \(\mathbb Q(\zeta_m)\) is fixed by conjugation.
This follows from the cyclotomic decomposition group generated by
Frobenius \(\ell\), with conjugation corresponding to \(-1\).
The valuation at any such prime gives \(2v(\alpha)=k\), so k is even.
We use \(\ell=599\) for the original matrix and \(\ell=5\) when a
smaller Hadamard matrix of order 40 or 80 occurs.

Apply §1 and this parity test to every prime \(3\le q\le2396\),
and every \(0\le f\le\lfloor2396/q\rfloor\) with \(2396-f=qt\),
\(t>0\). The only survivors at \(q\ge29\) are the seven in the table
and \((q,f,t)=(479,1,5)\), eliminated by Davis. There are no larger
primes: an odd-order subgroup embeds in the row permutation group
(the kernel of the unsigned projection is a 2-group).

In every surviving row \(q\nmid t\). An element of order \(q^2\)
would have a q-th power whose number of q-cycles is divisible by q.
A subgroup \(C_q^2\) would have all nonidentity elements fixing f,
so its number of orbits is \(f+(n-f)/q^2=f+t/q\) by Burnside.
Both possibilities are contradictory. Every q-group of order at
least \(q^2\) contains a subgroup of order \(q^2\), of one of these
two types, proving the first-power restriction.

## 3. The four missing sign rows

We need a small equivariant refinement of a classical completion
fact. By Hall's Hadamard completion theorem (M. Hall Jr.,
*Integral matrices A for which \(AA^{\mathsf T}=mI\)*,
*Number Theory and Algebra*, Academic Press, 1977, pp. 119–134;
see also [Verheiden's extension](https://doi.org/10.1016/0097-3165(78)90019-5)),
a partial real Hadamard matrix with t columns and \(t-4\) sign
rows can be completed by four more sign rows.

There are at most two possible unordered sets of the four
additional **projective** rows (a sign row and its negative
are identified). To see this, fix one completion with bottom
rows \(V\in\{\pm1\}^{4\times t}\). Negate individual columns of V
for this analysis so that their first coordinate is positive.
Represent the column patterns by \((1,x,y,z)\), \(x,y,z\in\{\pm1\}\).
The normalized pattern frequencies have vanishing degree-one
and degree-two moments by \(VV^{\mathsf T}=tI\). Hence they are
\((1+\theta xyz)/8\) for some \(-1\le\theta\le1\).

If \(|\theta|<1\) all eight patterns occur. A sign vector in
the four-dimensional orthogonal complement is \(w^{\mathsf T}V\);
\(|w^{\mathsf T}(1,x,y,z)|^2=1\) at all eight patterns implies
\(w_iw_j=0\) for every \(i\ne j\) by comparing the six distinct
degree-one and degree-two coefficients. Thus the only projective
rows are the original four. If \(|\theta|=1\), the four
occurring column patterns are orthogonal. A sign vector in the
complement can assign an arbitrary sign to each of those
patterns. Inner products correspond to equally weighted
inner products on these four signs, since all occur equally
often. The eight projective sign rows of length four split
into two parity classes of size four; distinct rows are
orthogonal exactly within a parity class. Hence precisely two
projective completions occur in this case.

An odd-order action on the t columns preserving the span of
the known rows acts on this set of at most two completions,
so fixes each completion. On the complement it is therefore
represented by a signed permutation of four rows. For an
order-r action with r an odd prime, this adds at most one
r-cycle when \(r=3\), and no r-cycle for \(r\ge5\). Odd signed
cycles can be untwisted as in §1. In particular if the action
on the t columns is a nontrivial permutation of prime order r,
one gets an order-r automorphism of the completed matrix.

## 4. Odd primes in a centralizer

Let distinct odd prime elements of orders q and r commute, with
\(q\ge29\). Their product has order qr; work with the simultaneous
ordinary action. Write \(f_r\) for the number of fixed labels
for the order-r element, s for the number fixed by both, and z
for the number of length-qr cycles of the product. Necessarily
\[
0\le s\le\min(f,f_r),\qquad
s\equiv f_r\bmod q,\quad s\equiv f\bmod r,\qquad
z=\frac{2396-f-f_r+s}{qr}\in\mathbb Z_{\ge0}.
\tag{2}
\]
Indeed the cycle lengths are \(1,q,r,qr\), and summing their
contributions gives (2). Apply §2 to z for m=qr when the prime
599 is coprime to qr.

On the f q-fixed rows, the second action has
\(a=(f-s)/r\) cycles of length r. It has z such cycles on the
t column-orbit labels of the first action. The B block is an
intertwiner between these two permutation representations.
Because \(BB^{\mathsf T}=tI\), its transpose embeds the first
module into the second. For \(f=0\) this is the zero-space
embedding. Thus in the orthogonal complement of dimension
\(t-f\) the multiplicity of every nontrivial r-th root is
\(b=z-a\), requiring \(b\ge0\) and \((r-1)b\le t-f\).

For defect \(t-f=4\), §3 further gives \(b\le1\) if \(r=3\)
and \(b=0\) for \(r\ge5\). If \(z>0\), apply the tests of
§1 and §2 to the completed Hadamard matrix of order t with
\(t-rz\) fixed labels and z r-cycles. When \(t=4,f=0\), the
completion is any 4-square Hadamard; the §3 argument still
applies. The remaining candidate r sets are exactly the table's
centralizer column. These are exact arithmetic filters, not
constructions of a matrix or even of a consistent orbit block.

For \(q=149,r=3\), the only remaining tuple is
\((f_r,s,z,b)=(596,0,4,0)\). Thus every order-three centralizer
element acts without fixed points on the twelve q-fixed row
labels. Any 3-subgroup of the centralizer therefore acts
freely there: a nontrivial stabilizer would contain an
order-three element. Its order divides twelve and is at most
three. For \(q=199,599\) there are no other odd primes in
the centralizer.

## 5. Odd affine actions in normalizers

The conjugation image of N embeds in \(\mathbb F_q^\times\).
In the table this can add no new odd prime for \(q=31,37\).
For q=599 we use the existing stronger result cited above.
We exclude the potential additional odd image factors for
\(q=29,59,149,199\) below, except a single factor 3 at q=199.

Suppose h normalizes \(\langle g\rangle\), has odd prime-power
order, and its image is multiplication by a nonidentity
\(u\in\mathbb F_q^\times\). The subgroup generated by h and g
has odd order, so untwist both together. On each q-orbit,
h maps its coordinates \(x\) to \(ux+c\) in the target q-orbit.
On the g-fixed positions, h is a permutation. For a q-orbit
label fixed by h, its affine map has exactly one fixed actual
position. On q-orbit labels and fixed labels the equivariance
of B is unchanged from §4, since B is constant inside each
moving column orbit. For every case below the fixed block A is
invertible and intertwines the two actions on the q-fixed labels,
so those two actions have identical cycle types. The same argument
with \(H^{\mathsf T}\) gives the corresponding complement constraints
on the other side.

In the normalized q-orbit-constant bases the full H block is
\(\begin{pmatrix} A&\sqrt q B\\\sqrt q D&E\end{pmatrix}\), where
D is a \(t\times f\) sign matrix and E is an integer matrix of
sums of sign functions on q-cycles. Every E row has
\[
\sum_{j=1}^t E_{ij}^2=n-qf.
\tag{3}
\]
If h fixes all q-orbit labels on each side and u has odd
order r, each of the \(t^2\) block sequences is invariant under
an affine map with multiplier u and a single fixed point.
The signs on nonfixed positions contribute a multiple of r
whose quotient is even, since \((q-1)/r\) is even. In particular,
\(E_{ij}\equiv\pm1\bmod 2r\).

* \(q=29,r=7\). Let a be the number of 7-cycles of h on the 76
  q-fixed labels. The defect-four representation forces exactly
  a such cycles on the 80 moving labels, on either side. If
  \(a>0\), the completed matrix of order 80 has \(80-7a\)
  fixed positions. This is at least four, at most \(80/7\),
  and congruent to 3 modulo 7, hence is 10. By the short even
  fixed-block test (\(10<14\)), this is impossible. Thus h
  fixes all labels. Each \(|E_{ij}|\) is then 1 or 13 under
  the row budget 192 and congruence modulo 14. The baseline is
  80 and even one 13 would add 168, contradiction.
* \(q=59,r=29\). By the defect bound the number a of 29-cycles
  on the 36 fixed labels equals the number on the 40 moving
  labels. Then h fixes \(76-58a\) actual positions, and the
  order-29 row of the table forces \(a=0\). Congruence modulo
  58 and row budget 272 leave only entries of absolute value
  one, which cannot attain the required budget.
* \(q=149,r=37\). Both the 12 fixed and the 16 moving labels
  are fixed by an order-37 action. The congruence modulo 74
  and budget 608 likewise allow only absolute value one.
* \(q=199,r=11\). The eight fixed labels cannot move in
  11-cycles. Neither can the 12 moving labels, by the defect
  bound. Congruence modulo 22 and row budget 804 allow
  \(\{1,21,23\}\). Relative to baseline 12, the two allowed
  increments are 440 and 528, which cannot total 792:
  dividing by 88 would require \(5a+6b=9\).
* \(q=199\), image order a nontrivial power of 3. The
  centralizer contains no 3, so if the normalizer has 3-part
  at least 9, its 3-Sylow injects into the cyclic image and
  contains an order-nine element h mapping to order nine.
  Consider either order three or order nine, with image of
  the same order. On the eight fixed labels its order
  divides three. If order nine and a length-nine cycle
  occurs on the 12 moving labels, \(h^3\) has three 3-cycles
  there but none on the fixed labels, impossible by §3.
  So both label actions have order dividing three. Let a
  and z count their 3-cycles on the fixed and moving labels
  respectively, with \(0\le a\le2\), \(a\le z\le a+1\).
  If \(z>0\), the completed order-12 matrix has \(12-3z\)
  fixed labels. The bound \(12-3z\le12/3\) forces
  \(z=3,\ a=2\). Then h fixes \(20-3(a+z)=5\) actual
  positions; these same counts hold on columns by similarity.
  Its fixed Gram has off-diagonals divisible by 3, so the
  odd Gram test for f=5 in §1 gives a contradiction. Thus
  \(a=z=0\). Now for order nine, the congruence modulo 18
  and row budget 804 allow \(\{1,17,19\}\). Relative to
  baseline 12, the increments are 288 and 360, which cannot
  total 792 because \(4a'+5b'=11\) has no nonnegative
  integer solution. Order nine is excluded. An order-three
  h, if present, consequently fixes \(8+12=20\) actual
  positions and acts as described in the theorem.

In each case excluding an image factor r, a hypothetical r factor
would yield an order-r element mapping nontrivially as used above:
r is absent from that centralizer's prime list. The exponents
claimed for q=149 and q=199 now follow from the centralizer bound
and the cyclic image.

The exact arithmetic tables and the orbit-row budgets can be
reproduced without external packages:
~~~sh
python3 verify_factor_hadamard2396_large_prime_actions.py
~~~
The code rejects all other cases using the displayed necessary
tests and imports the stated order-479 exclusion; it does not
perform, or claim to perform, a search for Hadamard matrices.
