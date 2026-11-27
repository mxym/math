# An exact construction and certificate

A quantum Latin square (QLS) of order \(n\) is an \(n\)-by-\(n\) array of
unit vectors in \(\mathbb C^n\) whose rows and columns are orthonormal
bases. The cardinality counts vectors up to multiplication by a global
phase, equivalently counts the complex rays they span.

## 1. The two-value Hadamard matrix

Use \(\mathbb F_{23}=\mathbb Z/23\mathbb Z\) to index every coordinate,
row, and column by 0 through 22. Let \(D\) be its set of nonzero squares,
let \(d=\mathbf 1_D\), and set
\[
 D=\{1,2,3,4,6,8,9,12,13,16,18\},\qquad
 \xi=\frac{-11+i\sqrt{23}}{12},\qquad H_{ka}=\xi^{d(k-a)} .
\]
We have \(|\xi|=1\). For every nonzero \(u\), there are exactly 5 field
elements \(x\) with \(d(x)=d(x-u)=1\). For a direct proof, let \(\chi\)
be the quadratic character extended by \(\chi(0)=0\). The map
\(x\mapsto x/(x-u)\) is a bijection from \(\mathbb F_{23}\setminus\{u\}\)
to \(\mathbb F_{23}\setminus\{1\}\). On its domain,
\(\chi(x)\chi(x-u)=\chi(x/(x-u))\), since \((x-u)^2\) is a nonzero square.
The term at \(x=u\) is zero, so \(\sum_x\chi(x)\chi(x-u)=-1\).
Now write \(2d(x)=1+\chi(x)-\mathbf 1_{x=0}\). Expanding the product at
\(x,x-u\), using \(u\ne0\), gives
\[
 4\sum_x d(x)d(x-u)
 =23-1-(1+\chi(-u))-(1+\chi(u))=20,
\]
because \(-1\) is not a square. Each translated set has 11 points, so the
difference of two distinct columns of the exponent matrix has 6 entries
of each sign and 11 zeros. For distinct columns the Hermitian inner
product in \(H\) is
\(11+6\xi+6\overline{\xi}=0\); each column has squared norm 23.
Thus \(H^*H=23I\). This is a two-value Paley/Björck circulant construction.

## 2. The quantum Latin square

Define the permutation by listing its values in increasing input order:
\[
 \sigma=(22,6,13,2,9,5,16,10,1,20,14,4,18,3,19,21,12,17,8,7,11,15,0).
\]
Set \(K_{kb}=H_{\sigma(k),b}\). It has unimodular entries and \(K^*K=23I\).
Take
\[
 v_{ab}(k)=\frac{1}{\sqrt{23}}\,
       \xi^{d(k-a)+d(\sigma(k)-b)}
          =\frac{1}{\sqrt{23}}H_{ka}K_{kb}.
\]
For fixed \(a\), coordinatewise multiplication by \(H[:,a]\) is unitary
and the columns of \(K/\sqrt{23}\) form an orthonormal basis. This proves
the row condition; exchanging \(H\) and \(K\) proves the column condition.
These observations are the mixed Schur-product construction.

## 3. How to count rays without numerical tolerances

Let \(E_{ab}(k)=d(k-a)+d(\sigma(k)-b)\). The sum of every \(E_{ab}\)
over \(k\) is 22. Suppose \(v_{ab}=\lambda v_{ce}\); then
\(\xi^{E_{ab}(k)-E_{ce}(k)}=\lambda\) at every coordinate.
The phase \(\xi\) is not a root of unity: if it were, \(\xi+\xi^{-1}\)
would be an algebraic integer; this is the rational noninteger
\(-11/6\). Hence \(E_{ab}-E_{ce}\) is a constant integer vector. Its sum
is zero, so that constant is zero. Conversely, equal exponent vectors
give equal vectors, and therefore equal rays.

For \(a\ne c\), put \(r_{ac}(k)=d(k-a)-d(k-c)\). Two distinct cells
\((a,b),(c,e)\) cannot lie in the same row or column if their rays
agree, since such cells are orthogonal. With \(a\ne c\) and \(b\ne e\),
the preceding equivalence is exactly
\[
 [v_{ab}]=[v_{ce}]\quad\Longleftrightarrow\quad
 r_{ac}(k)=r_{eb}(\sigma(k))\quad\text{for every }k .
\]
Equivalently, the directed column ratio \(H[:,a]/H[:,c]\) and the
directed column ratio \(K[:,e]/K[:,b]\) are equal coordinatewise.

## 4. Exact finite certificate

Here every exhaustive loop runs over all stated indices. For any
coordinate order \(Q=(Q_0,\ldots,Q_{22})\), define the integer column
mask \(C_Q(a)=\sum_{k:\,Q_k-a\in D}2^k\). The two masks encoding the
values \(+1\) and \(-1\) of a signed column difference are
\[
 M_Q(a,c)=\big(C_Q(a)\mathbin{\&}\neg C_Q(c),
                 C_Q(c)\mathbin{\&}\neg C_Q(a)\big).
\]
The complement is harmless because each term is intersected with a
23-bit mask. The pair determines the signed vector, since unmarked
coordinates have value 0. The finite certificate consists of the
following procedure and its exact result:

~~~text
for Q in { identity order, values of sigma }:
    calculate C_Q(a) for every a in 0,...,22 by modular membership in D
    make the map from M_Q(a,c) to (a,c) for all 23*22 ordered pairs a != c
    check the map has no repeated keys
intersect the two key sets; look up the labels from both maps

common key (hex masks)     identity label     sigma label
(051142, 0a44a0)           (0,1)              (0,1)
(0a44a0, 051142)           (1,0)              (1,0)
~~~

The two intersection entries represent the two ordered orientations of
one unordered cell pair: \(\{(0,1),(1,0)\}\). Since every pair of
distinct same-row or same-column cells has unequal rays, and all other
pairs would produce one of the tested ordered-ratio matches, there are
no further coincidences. Thus the 529 cells comprise 527 singleton rays
and one double ray, for a total of 528.

The first verifier implements this exact mask certificate. The second
independently constructs all vectors without their common
\(1/\sqrt{23}\) factor, working in \(\mathbb Q(i\sqrt{23})\). It
checks each of the 46 Gram matrices and compares all unordered cell
pairs after multiplying each unnormalized vector by the conjugate of
its unit-modulus first coordinate. For that independent comparison, two
dephased vectors are equal if and only if the original vectors define the
same ray, by direct cancellation of the first coordinate.
