# A rank-only test fails for HKWW Open Problem 4

We give a simple \(2\)-\((16,6,8)\) design of binary rank \(8\)
satisfying the parameters prescribed by Hyun–Kwon–Wang–Wu with
\(m=6,r=2\), but without the triple symmetric difference property.
Thus rank \(m+2\) cannot replace the rank-plus-Reed–Muller condition
at positive plateau order. We also give a simple exact substitute
for that condition: after checking the rank, use one linear system
and one binary sumset test on the columns of any generator matrix.
Both statements are proved without computation.

## 1. The source and its parameters

Jong Yoon Hyun, Jieun Kwon, Jiaxin Wang and Yansheng Wu,
[*Designs, linear codes, plateaued functions, and their
interconnections*](https://arxiv.org/abs/2605.24355v1), May 2026,
[Theorem 3 (p. 9) and Open Problem 4 (p. 10)](https://arxiv.org/pdf/2605.24355v1#page=9).
Write \(d=m-r\) and \(v=2^d\); the (integral) nontrivial parameters
have \(d\) even and \(d\ge4\). The parameters in Theorem 3 are
\[
 k=v/2-\sqrt v/2,\qquad
 \lambda=2^r(v/4-\sqrt v/2).
 \tag{1}
\]
A design is *simple* when its blocks are distinct. Its code
\(C_{\mathcal D}\) is the binary code of length \(b\) spanned by the
point rows of the incidence matrix, with coordinates indexed by
the blocks. For (1), the block count is
\(b=\lambda v(v-1)/[k(k-1)]=2^rv=2^m\).
If \(d=2\), then \(k=1\) and a simple design has at most four
blocks; for \(r\ge1\) its rank cannot be \(m+2\). We work in the
nontrivial regime.

For these parameters, Theorem 3 identifies the triple symmetric
difference property (TSDP) and the associated plateaued addition
designs with condition (iii): the binary rank is \(m+2\) and
\(C_{\mathcal D}\) contains a coordinate-relabelled
\(\mathrm{RM}(1,m)\). At \(r=0\) the authors recall the known
rank-only criterion. Open Problem 4 asks for a simplification
at positive \(r\). Our example disproves the same rank-only
simplification; the sumset criterion below applies for every \(r\)
in (1).

## 2. An elementary two-test replacement for the subcode condition

Let \(C\) be any binary length-\(2^m\), dimension-\(m+2\) code
with distinct columns \(X\subset\mathbb F_2^{m+2}\) in a full-rank
generator matrix. In particular, columns are distinct in
\(C_{\mathcal D}\): the full incidence columns are different by
simplicity, so they remain different on a basis of point rows.
Then
\[
 \begin{split}
 C\text{ contains a relabelled }\mathrm{RM}(1,m)
 \quad\Longleftrightarrow\quad
 &\mathbf1\in C\ \text{ and }\
 |X+X|<2^{m+1}.
 \end{split} \tag{2}
\]
Membership of \(\mathbf1\) is one linear system in the generator
rows. The sumset is computed by taking XORs of column pairs,
or from the support of the Boolean-group convolution of the column
indicator with itself, using ordinary integer coefficients.
Changing the generator basis carries \(X\) and \(X+X\) through
an invertible linear map, and relabelling block coordinates just
permutes the columns. Thus neither changes the test.

To prove sufficiency, \(\mathbf1\in C\) gives a linear functional
\(\ell\) with \(\ell(x)=1\) for every \(x\in X\).
Thus \(X+X\subset\ker\ell\), a space of size \(2^{m+1}\).
The strict inequality gives \(w\in\ker\ell\setminus(X+X)\).
It is nonzero since \(0\in X+X\). Each coset of \(\langle w\rangle\)
in \(H=\{x:\ell(x)=1\}\) contains at most one column, or else the
sum of two columns in that coset is \(w\). Both the number of these
cosets and the number of columns equal \(2^m\), so there is exactly
one column in each coset. Choose \(m\) more linear functionals
along with \(\ell\) giving coordinates on
\(\mathbb F_2^{m+2}/\langle w\rangle\). They give all binary \(m\)-tuples
exactly once on \(X\), and their evaluations together with
\(\ell=1\) generate the required Reed–Muller subcode.

For necessity, use a generator basis with the first \(m+1\) rows
the constant and \(m\) linear rows of the relabelled
\(\mathrm{RM}(1,m)\), and extend by one row. The columns then
have form \((1,t,F(t))\) with exactly one per \(t\in\mathbb F_2^m\).
Their sumset misses \((0,0,1)\), a vector in the kernel of the first
coordinate. This proves (2).

## 3. A family of designs with additive block labels

For any bent quadratic \(Q\) on \(V=\mathbb F_2^d\), make the
\(v\) blocks with incidence functions
\[
 Q(z)+a\cdot z+Q^*(a),\qquad a\in V,
 \tag{3}
\]
where \(W_Q(a)=\sqrt v\,(-1)^{Q^*(a)}\).
These form the standard addition design of \(Q\). In particular
each block size is \(k=(v-\sqrt v)/2\), by the sign choice.
For a fixed point the sign sum over all \(a\) equals \(\sqrt v\)
by Walsh inversion. For two distinct points the sum of the
products of their signs is zero by character orthogonality.
Expanding the product of two block indicators gives a constant
pair count \(v/4-\sqrt v/2\). All blocks from (3) are distinct
because a change in \(a\) makes a nonconstant affine difference.

The binary span of the incidence vectors (as functions of the
points) is \(\mathrm{RM}(1,d)+\langle Q\rangle\).
Indeed the differences with the \(a=0\) block have affine
coefficient vectors \((a,Q^*(a)+Q^*(0))\). They span all
\(d+1\) affine coefficients: a linear relation annihilating
those vectors either annihilates every \(a\) with no constant
coefficient, or makes \(Q^*\) affine. The former relation
must be zero, and the latter is impossible because \(Q^*\)
is bent (directly from the Walsh inversion formula).
The \(a=0\) block itself adds \(Q\) modulo affine functions.

Now choose a set \(\mathcal L\) of \(2^r\) distinct bent homogeneous
quadratics. They have disjoint block lists, since quadratics in
different families have different top degree-two parts.
Take the union of the block lists (3) on the same \(v\) points.
It is a simple design with parameters (1), and its binary rank is
\[
 d+1+\dim\langle\mathcal L\rangle ,
 \tag{4}
\]
using the span just proved and the equality of row and column rank.
Its TSDP holds exactly when \(\mathcal L\) is an affine subspace
of the vector space of homogeneous quadratic forms. Indeed the
top quadratic part of an XOR of three block vectors is the sum
of the three labels. If the sum label is present, (3) has a block
with the same linear part as that XOR; the constant is either
right already or is obtained by taking its complement. If the
sum label is not present, neither a block nor its complement
can have that quadratic part. A nonempty set of labels is
closed under triple sums exactly when a translate of the set is
closed under pairwise sums, equivalently when it is affine.
Any failure of triple closure uses three distinct labels, so
causes failure even when testing three distinct blocks only.

## 4. Explicit counterexample and unbounded families

On \(V=\mathbb F_2^2\times\mathbb F_2^2\), write
\(x=(x_1,x_2)\), \(y=(y_1,y_2)\), and take
\[
\begin{array}{ll}
 Q_1=x_1y_1+x_2y_2,&
 Q_2=x_1y_2+x_2(y_1+y_2),\\
 Q_{12}=Q_1+Q_2,&
 Q_3=x_1y_2+x_2y_1 .
\end{array}
\]
All four are bent: each has form \(x^{\mathsf T}My\) with \(M\)
invertible, so partial Walsh summation over \(x\) has exactly one
surviving \(y\) and gives magnitude \(2^2\).
Their label span has dimension three (specifically \(Q_3\) is
outside \(\langle Q_1,Q_2\rangle\)).
Thus \(d=4,r=2,m=6\) gives \(64\) distinct blocks with
\((v,k,\lambda)=(16,6,8)\) and rank \(4+1+3=8\).
The three \(a=0\) blocks of \(Q_1,Q_2,Q_{12}\) XOR to the empty
set: their signs at zero are positive, so their incidence vectors
are those three quadratic forms themselves. Neither the empty set
nor its complement is a block. Also an all-one point-code word
would be a linear functional evaluating to 1 on every block column,
which contradicts the sum of these three columns being zero.
In particular rank \(m+2\) does not
imply the TSDP or condition (iii). No claim of minimality in \(m\)
or of a rank-only failure at \(r=1\) is needed here.

For unbounded families, fix any \(r\ge2\) and
\(n\ge r+1\), set \(d=2n\) and take \(V=\mathbb F_{2^n}^2\) in any
binary coordinate basis. With the binary coordinate pairing use
\(Q_c(x,y)=x\cdot(cy)\). Nonzero \(c\) give bent homogeneous
quadratics, and \(c\mapsto Q_c\) is an injective binary linear
map. Choose an \(r\)-space \(R\subset\mathbb F_{2^n}\), \(c_0\notin R\)
and \(w\in R\setminus\{0\}\). Use the labels \(Q_c\) for
\[
       c\in L=\big((c_0+R)\setminus\{c_0\}\big)\cup\{w\}.
\]
There are \(2^r\) nonzero labels. The pairwise differences of
the retained coset elements span \(R\): each nonzero \(t\in R\)
is a sum of two nonzero distinct vectors \(a,a+t\in R\), since
there is \(a\in R\setminus\{0,t\}\). With any element of
\(c_0+R\) these span \(R+\langle c_0\rangle\), dimension \(r+1\).
Three retained coset elements \(c_0+a,c_0+b,c_0+a+b\) for
independent \(a,b\in R\) sum to \(c_0\), not a label.
Consequently (4) gives rank \(m+2\) and the TSDP still fails.
This shows the rank-only simplification fails in an infinite
parameter range, not just a single small design.

## 5. Attribution and reproducibility

The classical addition-design construction (3) and the
rank-plus-subcode condition are those in HKWW (their §IV-A
and Theorem 3), not claimed to be new. Construction of a binary
code by evaluating linear functionals on generator columns is
standard, e.g. [Carlet, §4.2.1](https://www.math.univ-paris13.fr/~carlet/book-fcts-Bool-vect-crypt-codes.pdf).
The statements here are an explicit obstruction to the suggested
rank-only replacement, its infinite family, and the concrete
basis-invariant replacement test (2) for the specific subcode
condition. Searches through 27 November 2026 for the exact arXiv
number, authors, Open Problem 4, binary rank and TSDP, the
\(2\)-\((16,6,8)\) design parameters, and Reed–Muller inclusion
did not locate a same-scope answer. This is not an absolute
priority claim.

Two independent finite checks (Python 3.10+, standard library):
```sh
python3 verify_design.py
python3 verify_sumset.py
```
