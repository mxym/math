# An unbiased qutrit MIC with less maximal randomness than every qutrit SIC

We answer negatively the question in §7 of Curran,
arXiv:2605.18291v1, whether SICs in higher dimension share
the minimizing property proved in dimension two. The
criterion throughout is the maximum, over input states,
of the intrinsic conditional min-entropy for a fixed
unbiased minimal informationally complete measurement
(MIC). We show:
\[
 \begin{array}{ll}
 \text{every qutrit SIC:}& H^{\mathrm{max}}_{\min}=\log_2 6,\\[1mm]
 \text{one explicit non-SIC unbiased qutrit MIC:}&
 H^{\mathrm{max}}_{\min}\le
 \log_2 6-\log_2(1+2\epsilon/3)<\log_2 6,
 \qquad \epsilon=1/100000 .
 \end{array}                                                \tag{1}
\]
This is a comparison of the stated intrinsic-randomness
criterion, not a statement about tomographic optimality,
any projective-simulability threshold, or experimental
security.

## 1. Reduction to a pure-state overlap functional

Let \(v_1,\ldots,v_9\) be unit vectors in \(\mathbb C^3\)
forming an unbiased rank-one MIC
\(M_j=|v_j\rangle\langle v_j|/3\). Define
\[
 m(V)=\min_{\|\psi\|=1}\;\max_j
                        |\langle v_j,\psi\rangle|^2.
\]
A pure input has guessing probability
\(\max_j |\langle v_j,\psi\rangle|^2/3\). Indeed any
positive-state decomposition of its rank-one density
operator is supported on the same ray. For a mixed
state take any pure-state decomposition and, in each
branch, guess the most probable outcome for that branch.
This is admissible in Curran's Eq. (2): collect branches
that make the same guess into one positive component of
the decomposition. The resulting success probability is
at least \(m(V)/3\). Thus minimizing guessing probability
over *all* states gives exactly \(m(V)/3\), and maximizing
the intrinsic min-entropy gives \(-\log_2[m(V)/3]\).
The minimum for pure states exists by compactness.

## 2. A one-parameter family of unbiased MICs

Let \(\omega=e^{2\pi \mathrm i/3}\) and \(t=1+\omega
=e^{\pi\mathrm i/3}\); \(|t|=1\) and \(t^3=-1\). For a
parameter \(p\) with \(0<p<1\), write \(s=\sqrt p\) and
\(a=\sqrt{1-p}\). The nine vectors, grouped into triples
indexed by \(j=0,1,2\), are
\[
 A_j=(0,s,-t\omega^j a),\qquad
 B_j=(-\omega^j a,0,s),\qquad
 C_j=(s,-\omega^j a,0).                                     \tag{2}
\]
This is a Weyl--Heisenberg orbit in a convenient gauge,
not a new general orbit recipe. Indeed let
\(\nu=e^{\mathrm i\pi/9}\), so \(\nu^3=t\).
The standard phase-and-cyclic-shift orbit of
\((0,s,-\nu a)\) gives the same three groups with \(\nu\)
in place of each relative phase prefactor \(t,1,1\).
Conjugating by \(\mathrm{diag}(1,\nu^{-1},\nu)\) and
removing a phase from each vector gives (2). The
minimax comparison concerns this particular parameter
and measurement, not a novelty claim about the orbit.

They are unit vectors. Averaging their projectors over \(j\)
within each triple removes the off-diagonal entries.
The three average diagonals are
\((0,p,1-p),(1-p,0,p),(p,1-p,0)\), whose sum is
\((1,1,1)\). Thus the nine \(M_j=|v_j\rangle\langle v_j|/3\)
sum to \(I\) and have equal trace \(1/3\).

For each triple, Fourier combinations of its three
projectors recover both corresponding oriented
off-diagonal matrix units, up to nonzero constants,
and its average diagonal. This follows from the three
different characters \(1,\omega^j,\omega^{-j}\),
and from \(s a\ne0\). The three pairs of oriented units
are disjoint and cover every off-diagonal position.
The matrix of the three diagonal rows has determinant
\(p^3+(1-p)^3>0\). Hence the nine projectors span the
full complex matrix space, and the Hermitian effects are
linearly independent over the reals. They constitute a
MIC and are extremal: if an effect is written as a
strict mixture of positive effects, those effects must
have the same rank-one support, and normalization plus
linear independence forbids any nontrivial reweighting.

If \(p=1/2\), two distinct vectors from the same triple
have absolute squared inner product
\(|1+\omega|^2/4=1/4\), and between triples the only
shared coordinate gives the same value \(1/4\).
Thus this is a SIC. For \(p\ne1/2\), two vectors from
different triples instead have squared overlap
\(p(1-p)<1/4\), so the measurement is not a SIC.

## 3. The qutrit SIC reference value

For *any* qutrit SIC, put \(P_j=|v_j\rangle\langle v_j|\)
and \(x_j=\langle\psi,P_j\psi\rangle\) on pure input.
We use the identities
\[
        \sum_j x_j=3,\qquad \sum_j x_j^2=3/2.              \tag{3}
\]
The first is normalization. For the second, the linear
map \(L(X)=\sum_j\operatorname{Tr}(P_jX)P_j\) takes each
\(P_\ell\) to \((3/4)(P_\ell+I)\) by the SIC overlaps
and \(\sum_jP_j=3I\). The nine \(P_j\) span (their
Hilbert--Schmidt Gram matrix is \((3/4)I+(1/4)J\)),
so \(L(X)=(3/4)(X+\operatorname{Tr}(X)I)\) for all \(X\).
Taking \(X=|\psi\rangle\langle\psi|\) yields (3).
In particular \(\max_j x_j\ge (\sum_jx_j^2)/\sum_jx_j=1/2\).

Hughston and Salamon's all-qutrit-SIC classification
(Theorem 5.5 in arXiv:1410.5862v2) says that every such SIC
is unitarily congruent to a member of the midpoint family.
We do not assert a single unitary orbit. We use only its
consequence that there is a triple of vectors in one complex
two-dimensional subspace. A unit vector
orthogonal to that subspace gives at least three zero
values among the nine \(x_j\). By Cauchy--Schwarz, with
the two sums in (3), the other six must all be \(1/2\):
fewer than six positive values cannot give sum 3 and
square sum \(3/2\), and equality holds with six. Thus
\(m(V)=1/2\) for every qutrit SIC. For the specific
reference SIC in (2) this upper bound also follows
directly by taking any coordinate basis vector.
The three-zero and six-equal Born probabilities of this type
are known; see the references to Szymusiak and Stacey.
The classification is not used for the local estimates
on our own reference SIC below.

## 4. A quantitative perturbation

In (2) take \(p=1/2+\epsilon\) with \(\epsilon=1/100000\).
Set \(\delta=1/10000\). We show that for every unit
\(\psi\in\mathbb C^3\),
\[
      \max_j|\langle v_j(p),\psi\rangle|^2
                       \ge 1/2+\epsilon/3 .                \tag{4}
\]

### 4.1 Away from the three coordinate rays

For this part let \(x_j\) refer to the **reference** SIC
\(p=1/2\) in (2). Suppose \(\max x_j\le1/2+\delta\).
Then by (3)
\[
          \sum_j x_j(1/2+\delta-x_j)=3\delta .
\]
All summands are nonnegative. If \(x_j\le1/4\),
then \(x_j\le12\delta\); if \(x_j>1/4\), then
\(1/2+\delta-x_j\le12\delta\), so
\(x_j\ge1/2-11\delta\). There are at most six of the
latter, since \(7(1/2-11\delta)>3\). Choose three
of the small-overlap vectors.

For any three vectors of the reference SIC not all in
the same triple of (2), their \(3\times3\) matrix of
rows has determinant of absolute value at least
\(1/(2\sqrt2)\). To verify the bound, drop all three
normalizing factors \(1/\sqrt2\):
- Two vectors in the same triple span the corresponding
  coordinate plane. Their two-dimensional minor has
  magnitude \(|\omega^i-\omega^j|=\sqrt3\).
  The third vector has a coordinate of modulus one
  outside that plane, so the full determinant has
  the same magnitude.
- One vector from each triple has determinant
  \(1-t\omega^{i+j+k}\), up to an overall sign from row
  ordering. The three possible phases \(t\omega^m\)
  have principal arguments \(\pi/3,\pi,-\pi/3\);
  the three absolute values of \(1-t\omega^m\) are
  \(1,2,1\).

For normalized rows the Frobenius norm is \(\sqrt3\),
so the product of the two largest singular values is at
most 3. The smallest singular value is therefore at
least \(1/(6\sqrt2)\), also for the conjugated row matrix
that evaluates inner products. The sum of the three
squared overlaps for a unit vector is at least \(1/72\).
But those three small values total at most
\(36\delta=36/10000<1/72\). They must all come from the
same triple. Their average maps to half the squared
weight outside the corresponding coordinate ray, because
that triple's average projector is one half the projection
onto the corresponding coordinate plane. Thus for some
coordinate \(i\)
\[
          1-|\psi_i|^2\le24\delta<1/100 .
\]
Consequently, if for *every* coordinate \(i\) the value
\(u_i=\sqrt{1-|\psi_i|^2}\) is at least \(1/10\),
then the reference maximum exceeds \(1/2+\delta\).

At each fixed \(j\), changing \(p=1/2\) to
\(1/2+\epsilon\) changes a projector by a \(2\times2\)
Hermitian matrix with diagonal entries
\(\pm\epsilon\) (on its supported coordinates) and
off-diagonal entries of modulus
\(1/2-\sqrt{1/4-\epsilon^2}\).
The latter is at most \(2\epsilon^2\) by rationalization.
The operator norm of the whole change is at most
\(\epsilon+2\epsilon^2\le2\epsilon\). Hence in the above
region the perturbed maximum exceeds
\[
                   1/2+\delta-2\epsilon
                         > 1/2+\epsilon/3 .
\]

### 4.2 Near a coordinate ray

Suppose \(u=\sqrt{1-|\psi_i|^2}\le1/10\) for some \(i\).
There is one triple in (2) with squared coefficient
\(p\) on coordinate \(i\), in which the largest overlap
is at least the triple's average \(p(1-u^2)\).
If \(u^2\le\epsilon\), this gives
\[
       p(1-u^2)\ge p(1-\epsilon)
                    =1/2+(1-p)\epsilon>1/2+\epsilon/3 .
\]
Otherwise \(u\ge\sqrt\epsilon>0\), and one of the other
coordinates, say \(j\), has \(|\psi_j|\ge u/\sqrt2\).
Use the triple in (2) supported on coordinates \(i,j\).
Its coefficient on coordinate \(i\) has square at least
\(1/2-\epsilon\). Among the three equally spaced
relative phases one has interference at least half the
full positive interference amplitude. Accordingly its
largest overlap is at least
\[
 (1/2-\epsilon)(1-u^2)
             +\sqrt{p(1-p)}\,\sqrt{1-u^2}\,\frac u{\sqrt2}.
\]
The coefficient of \(u\) in the second term exceeds
\(1/4\): use \(p(1-p)> (49/100)^2\),
\(\sqrt{1-u^2}\ge99/100\), and \(1/\sqrt2>7/10\).
The lower bound is therefore at least
\[
 1/2-\epsilon-u^2/2+u/4
       \ge 1/2+u/4-3u^2/2
       \ge 1/2+u/10
       > 1/2+\epsilon/3 .
\]
Here \(\epsilon\le u^2\), \(u\le1/10\), and
\(\sqrt{\epsilon}/10>\epsilon/3\), the last following
from \(\epsilon<9/100\). This treats every possible
phase and handles the coordinate rays themselves via
the first case.

The two regions prove (4). With §1 and the reference
value from §3 this gives (1), including every mixed
input permitted by the stated intrinsic randomness
model.
