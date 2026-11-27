# Length-four codes with coherent secants

## 1. Source definitions and statement

Let \(C\subseteq\mathcal A^4\), with alphabet size \(q\). Distances
are Hamming distances, and \(k=\log_q|C|\) need not be integral.
A pair of values at distinct positions is **compatible** when some
codeword realizes both. The conflict graph of a word has an edge
between positions holding an incompatible pair. A code is
conflict-checkable when membership can be decided from this graph.
Equivalently, every full assignment with no conflict belongs to the
code: all legal words have the empty conflict graph. Local-to-global
consistency at minimum distance \(d\) means that every compatible
partial assignment on any set of at least \(4-d+1\) positions extends
to a codeword. We prove:

**Theorem.** For every real \(\varepsilon>0\), for arbitrarily large
\(q\) there exists a conflict-checkable, local-to-global consistent
\((4,k,2)_q\) code with \(k>2\) and \(k\ge3-\varepsilon\).

The comparison-based upper bound in ePrint 2023/627 Theorem 1.8 is
\((4-2+2)/2=2\). At length four, distance two is non-endpoint:
\(1<2<4-1\). The theorem therefore supplies a positive witness for
the conjecture on p. 11 beyond its already established
\(d=n-1\) case.

## 2. Gram-level code and its actual pair projections

Fix integers \(L,T\ge1\) and let \(H=\lceil\sqrt L\,T\rceil\).
Select a Gram triple \(G=(g_{11},g_{12},g_{22})\) realized by some
\(A,B\in[-T,T]^L\cap\mathbb Z^L\). Define the **whole** integer Gram level
\[
 \mathcal F_G=\{(A,B)\in(\mathbb Z^L)^2:
       A\cdot A=g_{11},\ A\cdot B=g_{12},\ B\cdot B=g_{22}\}.
\]
Each coordinate of both vectors is at most \(H\) in absolute value.
Importantly, the level is not restricted further to the original
box used to choose it. This ensures closure under integral
reconstruction below.

Choose a prime \(P>36H\). Take \(\mathcal A=\mathbb F_P^L\) and the four
positions \(0,1,2,3\). The code is the set of words
\[
 c_i=Z+iA+i^2B\pmod P\quad(i=0,1,2,3),\qquad
          Z\in\mathbb F_P^L,\quad (A,B)\in\mathcal F_G. \tag{1}
\]
For \(i<j\) define the integer difference
\[
 D_{ij}(A,B)=(j-i)A+(j^2-i^2)B=(j-i)\big(A+(i+j)B\big).
\]
Every coordinate has magnitude at most \(12H\), since
\(j-i\le3\) and \(j^2-i^2\le9\). A pair \(y_i,y_j\) is compatible
if and only if the residue \(y_j-y_i\) is the reduction of
\(D_{ij}(A,B)\) for some \((A,B)\in\mathcal F_G\). The forward
direction is immediate from (1). Conversely, choose the free
offset to realize \(y_i\); the difference then realizes \(y_j\).
Thus this criterion uses the actual projections of the code,
not hypothetical edges from a larger set.

For any compatible assignment, choose for each pair an integer
lift \(D_{ij}\) of this form; it is unique as an integer vector, since
the difference of any two candidate lifts is at most \(24H<P\)
coordinatewise. Write \(S_{ij}=D_{ij}/(j-i)\in\mathbb Z^L\).
For each compatible triple \(i<j<k\), the identity
\[
 D_{ij}+D_{jk}=D_{ik} \tag{2}
\]
holds over the integers: it holds modulo \(P\) by differencing
the labels; the possible residual has magnitude at most
\(36H<P\) in every coordinate.

## 3. Every triangle extends

Fix a compatible triple \(i<j<k\). Put \(r_1=j-i\),
\(r_2=k-j\), \(r_3=k-i\). Equation (2) says
\[
 r_1S_{ij}+r_2S_{jk}=r_3S_{ik}.
\]
Since no triple of \(0,1,2,3\) has both gaps divisible by a
common prime, \(\gcd(r_2,r_3)=1\). Indeed, the positive consecutive
gap pairs from the four triples are \((1,1),(1,2),(2,1),(1,1)\).
It follows from
\(r_2(S_{jk}-S_{ij})=r_3(S_{ik}-S_{ij})\)
that \(r_3\) divides every component of \(S_{jk}-S_{ij}\).

Define
\[
 B_*=(S_{jk}-S_{ij})/r_3,\qquad A_*=S_{ij}-(i+j)B_*.
\]
These are integer vectors. To see that they belong to the
correct Gram level, take any reference \((A_0,B_0)\in\mathcal F_G\).
Set \(S^0_{uv}=A_0+(u+v)B_0\), \(D^0_{uv}=(v-u)S^0_{uv}\). The three
squared lengths \(\|D_{ij}\|^2,\|D_{jk}\|^2,\|D_{ik}\|^2\) are
determined by \(G\) and the indices, so equal their reference
values. By (2) and polarization, the inner product
\(D_{ij}\cdot D_{jk}\) is also the reference value. Dividing by
nonzero gaps gives equality of the two-by-two Gram matrices of
\((S_{ij},S_{jk})\) and \((S^0_{ij},S^0_{jk})\).
The displayed linear transformation applied to the reference
pair returns exactly \((A_0,B_0)\). Equality of Gram matrices
is preserved under this transformation, proving
\((A_*,B_*)\in\mathcal F_G\).

The quadratic with coefficients \((A_*,B_*)\) has integer
secants \(S_{ij},S_{jk}\), hence differences \(D_{ij},D_{jk}\).
Choose its free offset to match \(y_i\). Its word then agrees
with all three labels. The extension is unique: degree at most
two interpolation at three distinct field inputs is unique in
each vector component because \(P>3\).

## 4. Every full clique is a word

Let all six pairs of a full assignment be compatible. From
each triangle \((0,j,k)\), equation (2) gives
\(D_{jk}=D_{0k}-D_{0j}\). Each \(D_{uv}\) has the same length as
\(D^0_{uv}\) for the single reference pair used above, regardless
of which witnesses produced these differences. Polarization
therefore proves that the full three-by-three Gram matrix of
\(D_{01},D_{02},D_{03}\) equals the reference one. Since
\(S_{0j}=D_{0j}/j\), the same applies to \(S_{01},S_{02},S_{03}\).
The reference secants \(A_0+jB_0\) satisfy
\(S^0_{01}-2S^0_{02}+S^0_{03}=0\), so the squared norm of the
corresponding actual combination, computed from the equal Gram
matrices, is zero. Positive definiteness of the real Euclidean
norm gives the vector equality
\[
 S_{01}-2S_{02}+S_{03}=0.
\]
By §3, the triangle on \(0,1,2\) extends to a word in (1).
The lifted secants of this word from 0 to 1 and 2 equal the
actual secants by uniqueness of the bounded difference lifts in
§2. Its secant to 3 must be \(2S_{02}-S_{01}=S_{03}\); choosing the
same offset thus realizes \(y_3\) as well. Every empty conflict
graph is therefore a word of \(C\). All assignments on three or
four positions have now been treated, proving both structural
properties.

## 5. Count, distance, and quantifiers

For each fixed \(L,T\), choose \(G\) maximizing the number of pairs
in the box \(([-T,T]^L\cap\mathbb Z^L)^2\) with that Gram triple.
There are \((2T+1)^{2L}\) pairs. Each diagonal Gram entry is between
0 and \(LT^2\), and the off-diagonal is between \(-LT^2\) and
\(LT^2\). Thus there are at most
\[
 (LT^2+1)^2(2LT^2+1)\le12L^3T^6
\]
levels, and the **whole** level chosen in §2 has size at least
\[
 |\mathcal F_G|\ge \frac{(2T+1)^{2L}}{12L^3T^6}.
\]
All of its coefficient pairs have coordinates in \([-H,H]\),
even those outside the original box, by the chosen squared norms.
These bounds determine \(H\) before choosing \(P\). By Bertrand's
postulate use a prime \(36H<P<72H\); hence \(P=\Theta_L(T)\) for
fixed \(L\) and growing \(T\). The map from \(\mathcal F_G\) to
the two coefficient vectors modulo \(P\) is injective since
\(2H<P\). Evaluation is injective on degree-at-most-two vector
polynomials after reduction (any three positions suffice), so
\(q=P^L\) and \(|C|=q|\mathcal F_G|\) exactly. Moreover any two
distinct words agree on at most two positions, hence \(d\ge2\).

Given \(\varepsilon>0\), choose
\(\eta=\min(\varepsilon,1/2)\) and fix an integer \(L>6/\eta\).
The estimate above and \(P\le72(\sqrt L+1)T\) yield
\[
 \frac{|C|}{q^{3-\eta}}
   \ \ge\ c_{L,\eta}T^{\eta L-6},
 \qquad c_{L,\eta}>0 .
\]
This tends to infinity with \(T\). Consequently for all large
enough \(T\) the code satisfies \(|C|\ge q^{3-\eta}>q^2\).
Since a projection to a specified pair of coordinates has only
\(q^2\) possible values, there must be distinct words agreeing
on both those coordinates. This proves the minimum distance is
exactly two, not merely at least two, and the dimension bound
follows. As \(T\to\infty\) the guaranteed alphabet sizes are
unbounded. No finite regression below is used to prove this
asymptotic statement.
