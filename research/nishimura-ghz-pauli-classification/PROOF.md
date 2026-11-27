# A projection-and-translation proof for exact single-GHZ Pauli PSQM

Write \(\mathbb F_2\) additively and use algebraic normal forms
(ANFs, i.e. multilinear polynomials on the Boolean cube). A
coordinate \(i\) is **essential** when a flip of it changes the
function at some input. Its coordinate derivative is
\(D_i f(x)=f(x+e_i)+f(x)\).

**Theorem.** For every odd \(k\ge3\) and every Boolean function
essential in all \(k\) coordinates, the protocol in Section 1
exists with perfect correctness and perfect privacy if and only if
\(\deg f\le2\) and its quadratic graph has an isolated vertex
or every graph degree is even. For such a function the minimum
shared seed entropy and support size are \(\dim W\) bits and
\(2^{\dim W}\), respectively, with \(W\) defined in Section 3.
At \(k=3\) the same feasibility criterion holds also for
nonessential functions, making a full classification of all 256.

## 1. Model and the affine label rule

There are \(k\) players, each with one bit \(x_i\). The players
share a fixed state \( (|0^k\rangle+|1^k\rangle)/\sqrt2\) and an
input-independent classical value \(R\) with arbitrary finite
support, not revealed to the referee. At fixed \(R=r\) each player
applies one of \(I,X,Z,XZ\), up to a scalar phase, as a function
of \(x_i\); it sends that same qubit, with no auxiliary message.
The referee may use any binary decoding POVM on the joint message.
Perfect correctness means its output equals \(f(x)\) with
probability one for every \(x\). Perfect privacy means the
averaged joint message density operator is the same for inputs
with the same \(f\)-value. For \(k=3\) these are exactly
Nishimura Sections 2.2 and 4.4. We use the direct odd-\(k\)
generalization of that restricted protocol model.

Let a player's operator be \(X^{p_i(x_i)}Z^{z_i(x_i)}\),
with \(p_i,z_i\in\mathbb F_2\) at each fixed seed. These are
affine functions of one bit. In computational notation the
resulting vector, up to phase, is
\[
 \frac{|0,q\rangle+(-1)^w|1,q+\mathbf1\rangle}{\sqrt2},
 \qquad q=(p_1+p_j)_{j=2}^k,\quad w=\sum_i z_i.                \tag{1}
\]
Indeed the two basis vectors before putting the first bit at
zero are \(p(x)\) and \(p(x)+\mathbf1\), and the latter has
the sign \((-1)^{\sum_i z_i}\). Exchanging their order changes
only the global phase. Distinct \(q\)'s have disjoint
computational supports, and for equal \(q\) the two signs are
orthogonal. Thus the \(2^k\) vectors form the GHZ basis;
(1) agrees with Lemma 4.1 of the source for \(k=3\).

In the \(q\)-space \(\mathbb F_2^{k-1}\), put
\(v_1=\mathbf1\) and \(v_j=e_{j-1}\) for \(j=2,\ldots,k\).
Every deterministic branch has
\[
 q_r(x)=t_r+\sum_{i=1}^k a_{r,i}v_i x_i,\qquad
 w_r(x)=b_r+\sum_{i=1}^k c_{r,i}x_i.                          \tag{2}
\]
Conversely every such map is realizable by the \(k\) local
Pauli choices: put the offset for \(p_1\) at zero, assign the
coordinates of \(t_r\) as offsets of \(p_2,\ldots,p_k\),
and assign the phase constant \(b_r\) to \(z_1\).
The only nontrivial linear relation among the \(v_i\)'s is
\(\sum_i v_i=0\), since \(v_2,\ldots,v_k\) are a basis and
their sum equals \(v_1\).

For each \(x\), the average state is diagonal in the GHZ
basis with entries the distribution of \((q_R(x),w_R(x))\).
Perfect privacy gives two class distributions \(D_0,D_1\) for
nonconstant \(f\). Perfect correctness implies their supports
are disjoint even for an arbitrary referee POVM: each basis
label of positive weight for one output must have that output
with probability one, because this probability is averaged
from numbers in \([0,1]\). A label of positive weight for both
would require contradictory output probabilities. Conversely
disjoint class supports suffice by a GHZ-basis measurement.
This is the support logic behind Equations (4.4)–(4.8) of the
source; no LP feasibility result is needed here.

## 2. The odd-party projection lemma

Suppose \(k\ge3\) is odd and every input variable of \(f\) is
essential. For each projected character \(s\in\mathbb F_2^{k-1}\),
consider its average at input \(x\):
\[
 m_s(x)=\mathbb E_R(-1)^{s\cdot q_R(x)}.
\]
For every \(s\), some \(i\) satisfies \(s\cdot v_i=0\).
In fact \(\sum_i(s\cdot v_i)=0\) in \(\mathbb F_2\)
but an all-ones list of odd length would sum to one.
Equation (2) shows that **every** branch in this particular
character, hence its average, ignores that same \(x_i\).
Since \(i\) is essential there exist two inputs differing
only in \(x_i\) with opposite \(f\)-values.
Perfect privacy says \(m_s(x)\) is constant in each output
class, so these two inputs prove equality of the two class
values of \(m_s\). The pair may depend on \(s\).
This argument is not an assumption about the full-degree
Fourier coefficient of \((-1)^f\).

All the character expectations agree, so by the
finite-group Fourier inversion the two projected \(q\) laws
coincide; call the common law \(\mu\). Explicitly, the
point mass at \(t\) is \(2^{-(k-1)}\sum_s(-1)^{s\cdot t}
m_s(x)\), by pairwise orthogonality of characters.
For each \(q\in\operatorname{supp}\mu\), both classes have
positive mass over that \(q\). There are only two labels
\((q,0),(q,1)\) over it; disjointness of the **joint** supports
therefore implies exactly one belongs to each class.
Let \(G(q)\) be the phase of the class-zero label. For every
positive-probability branch \(r\) and every \(x\), correctness
now forces
\[
                    f(x)=w_r(x)+G(q_r(x)).                 \tag{3}
\]
There is one common function \(G\) on the projected support,
not a different decoder for different seeds or output classes.

## 3. Necessity for essential odd-party functions

Let \(N=\{i:D_i f\text{ is nonconstant}\}\). If \(i\in N\),
then \(a_{r,i}=1\) in every positive-probability branch:
otherwise \(q_r\) would ignore \(x_i\) and (3) would imply
\(D_i f=c_{r,i}\), a constant. Write \(x_N\) for the vector
of these coordinates and fix the other coordinates at zero.
Set
\[
 L_N x_N=\sum_{i\in N}v_i x_i,\qquad W=\operatorname{im}L_N.
\]
Then \(q_r(x_N,0)=t_r+L_Nx_N\) in every branch,
and at zero the law of \(t_R\) is \(\mu\). Since the law
of \(q_R(x_N,0)\) is \(\mu\) at all \(x_N\), \(\mu\) is
invariant under translation by the whole subspace \(W\).
In particular pick \(t_0\) in its support; every point
of \(t_0+W\) occurs as the offset of at least one
positive-probability branch.

Fix one such branch at \(t_0\) and, for every \(h\in W\),
one at \(t_0+h\). Comparing (3) at the same input
\((x_N,0)\) for the two branches gives
\[
 G(t_0+h+L_Nx_N)+G(t_0+L_Nx_N)
              =w_{r_h}(x_N,0)+w_{r_0}(x_N,0).               \tag{4}
\]
The right side is affine in \(x_N\).
A linear right inverse from \(W\) to the \(x_N\)-space
exists since \(L_N\) is onto \(W\); applying it shows
that the left side, as a function of \(L_Nx_N\), is
affine on \(W\). Thus all first derivatives of
\(G\) on the affine space \(t_0+W\) are affine.
In coordinates on \(W\), differentiating an ANF in a
basis direction removes precisely that variable from
the monomials containing it. Two distinct such monomials
cannot collapse to the same monomial. Hence any monomial of
degree at least three would leave a quadratic-or-higher
term in a coordinate derivative. This proves
\(G|_{t_0+W}\) has degree at most two, including zero- and
one-dimensional \(W\).

By (3) restricted to one branch at \(t_0\), \(f(x_N,0)\)
also has degree at most two. For every \(i\notin N\),
\(D_i f\) is a constant \(\gamma_i\). Changing those
coordinates one by one gives
\(f(x)=f(x_N,0)+\sum_{i\notin N}\gamma_i x_i\).
Thus \(f\) has degree at most two on the whole cube.
Its quadratic graph has one vertex per player and an edge
\(\{i,j\}\) for each ANF term \(x_ix_j\).
Now \(N\) is exactly the set of non-isolated vertices.
If \(N\ne[k]\), the graph has an isolated vertex.
If \(N=[k]\), all \(a_{r,i}\)'s are one, so
\(q_r(x+\mathbf1)=q_r(x)\). By (3), \(D_{\mathbf1} f\)
is constant, as it equals the corresponding derivative of
the affine \(w_r\).
For a quadratic, this derivative has coefficient
\(\sum_{j\ne i} [x_ix_j]f\) at \(x_i\):
each edge contributes \(x_i+x_j+1\) under the flip.
All degrees of the graph must therefore be even.

## 4. Unified sufficiency and exact seed size

Suppose the ANF is the sum of a quadratic \(Q(x)\) with
only degree-two terms and an affine \(J(x)\), and the graph
has an isolated vertex or all degrees even.
Let \(N\) be the non-isolated vertices, \(W=\operatorname{im}L_N\).
If \(N\) is proper, the only relation among the \(v_i\)'s
shows that \(L_N\) is injective, so
\(G(L_Nx_N)=Q(x_N)\) defines a quadratic \(G\) on \(W\),
by linear substitution. If \(N=[k]\), the kernel of \(L_N\)
is \(\{0,\mathbf1\}\).
Even graph degrees imply \(D_{\mathbf1}Q=Q(\mathbf1)\)
is constant. Select a linear \(K\) with
\(K(\mathbf1)=Q(\mathbf1)\) (use \(K(x)=Q(\mathbf1)x_1\)).
Then \(Q+K\) factors through \(L_N\), giving
\(G(L_N x)=Q(x)+K(x)\). This \(G\) is quadratic, for
example by choosing a linear section of \(L_N\) in its
definition. In this case replace \(J\) by \(J+K\).
In both cases we obtain
\[
 f(x)=G(y)+J'(x),\qquad y=L_Nx_N,
\]
with \(G\) quadratic on \(W\) and \(J'\) affine.

Take \(t\) uniform on \(W\) as all the shared randomness,
and use local Pauli choices implementing
\[
             q_t(x)=t+y,\qquad
             w_t(x)=J'(x)+G(y)+G(t+y).                    \tag{5}
\]
For fixed \(t\) the last two terms are the first derivative
of a quadratic in direction \(t\), hence affine in \(y\)
and in \(x\). Thus (2) implements the prescribed \(q,w\).
The referee decodes \(w_t(x)+G(q_t(x))\).
Since \(q_t(x)\) is uniform over \(W\) for every input and
\(w_t(x)=f(x)+G(q_t(x))\), the joint distribution depends
only on \(f(x)\), proving perfect correctness and privacy.
When \(Q=0\), \(W=\{0\}\), so no shared random bits are
required. This construction does not require that all
variables be essential.

For a feasible all-essential odd-party function the amount
of shared randomness in (5) is minimal. Indeed in any
protocol Section 3 proved that \(t_R\) is uniform within
each positive-mass \(W\)-coset. Therefore the support of
\(R\) is at least \(2^{\dim W}\). Its Shannon entropy
(in bits) obeys
\[
 H(R)\ge H(t_R)=H(t_R+W)+\dim W\ge \dim W.
\]
The first inequality is because the offset is a deterministic
function of the seed. The construction has support exactly
\(2^{\dim W}\) and entropy exactly \(\dim W\).
Here \(\dim W=|N|\) if \(N\) is proper, and \(k-1\)
otherwise. This optimality claim is only for the
all-essential odd-party theorem.

## 5. Exact specialization to three parties

If a three-bit function is not essential in every
coordinate, it depends on at most two variables and so
has degree at most two with an isolated vertex (possibly
a constant graph). It is feasible by (5).
For the essential cases the preceding necessity and sufficiency
apply at \(k=3\). There is also a short direct check
for essential functions: extend \(G\) arbitrarily over unused
\(q\)'s in \(\mathbb F_2^2\) and write \(\theta\) for the
coefficient of its quadratic term. For any positive branch,
its two \(q\) coordinates are
\(t_1+a_1x_1+a_2x_2\) and \(t_2+a_1x_1+a_3x_3\).
Equation (3) therefore permits no cubic term and gives the
quadratic edge vector
\(\theta(a_1a_2,a_1a_3,a_2a_3)\), never of weight two.
Equivalently, a two-edge graph has no isolated vertex and
its two leaf vertices are odd. The allowable edge sets are
empty, a single edge, or the triangle. There are 16 possible
affine parts for each edge set.
Hence precisely \(5\cdot16=80\) functions are feasible,
exactly the positive family of Nishimura's Theorem 4.5.
The 128 cubic ANFs and the 48 degree-two ANFs with exactly
two edges are rigorously excluded, closing the classification
left numerical in Remark 4.7 and Section 7.
EXACT1 and EXACT2 have truth-table weight three and therefore
a nonzero cubic coefficient (the sum of all eight truth values);
the two-edge examples are excluded even with arbitrary
affine additions. No impossibility is asserted for other
shared states, general local unitaries, auxiliary systems
and arbitrary local CPTP maps, or more transmitted qubits.
