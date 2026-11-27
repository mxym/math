# A three-collision converse and sharp affine-conditioned error

## 1. Model and summary

Let \(F\) randomly select a hash \(f:\mathcal X\to[M]\), independently
of a finite source \((X,Y)\). The seed is public. Write
\[
 \Delta_F(X|Y;M)
 =\tfrac12\mathbb E_f\sum_{y,z}
       |P(f(X)=z,Y=y)-P(Y=y)/M|.
\]
For a fixed seed this is total variation, and the average is
equivalently total variation with the seed included in both states.
Suppress trivial \(Y\) in \(\Delta_F(X;M)\). Finite labeled seed
ensembles are allowed; several seeds can select the same function.
For classical--quantum side information use the trace-distance
definition with the same independent seed.

Following Regula--Cheng arXiv:2611.33270v1, a \(j^*\)-universal family
has probability exactly \(M^{1-i}\) that any \(i\) distinct inputs
all hash to the same bin, for every \(2\le i\le j\).
Without the star their condition is an upper bound. A strongly
\(j\)-universal family has uniformly independent outputs on every
set of at most \(j\) distinct inputs, and is \(j^*\)-universal.
We use \(M\ge2\) throughout.

**Theorem 1 (one-shot).** For any classical source law \(w_x\) with
\(C_j=\sum_xw_x^j\), every \(3^*\)-universal family satisfies
\[
 \Delta_F(X;M)\ \ge\
 (1-M^{-1})\frac{C_2^2}{2M^{-1}C_2+(1-2M^{-1})C_3}.        \tag{1}
\]
In particular, for \(X\) uniform on \(N\) points,
\[
 \Delta_F(X;M)\ \ge\ \ell_M(N):=\frac{M-1}{2N+M-2}.        \tag{2}
\]
If the source is conditionally uniform on \(N_Y\) points, the
corresponding bound is \(\mathbb E_Y\ell_M(N_Y)\).

**Theorem 2 (affine-conditioned case).** Let \(X\in\mathbb F_2^d\)
and, for each \(Y=y\) with nonzero probability, let \(X|y\) be uniform
on an affine space of dimension \(K(y)\). There is no disjointness or
common-direction assumption. For \(M=2^m\) with \(m\ge1\), write
\(\Delta_3^*=\inf_F\Delta_F\) over \(3^*\)-universal families and
\(\Delta_{\rm aff}\) for the full random affine family
\(f(x)=A x+b\) with independent uniform binary entries. Then
\[
 \frac14\mathbb E\min(1,2^{m-K})
 \ \le\ \mathbb E\,\ell_M(2^K)
 \ \le\ \Delta_3^*
 \ \le\ \Delta_{\rm aff}
 \ \le\ \mathbb E\min\!\left(1,\frac{M-1}{2\cdot2^K}\right)
 \ \le\ \mathbb E\min(1,2^{m-K}).                           \tag{3}
\]
In particular \(\Delta_{\rm aff}\le4\Delta_3^*\) for the
seed-averaged classical side-information error at every finite
\(d,m\) and every such \((X,Y)\), with no bound on the number
of possible affine supports. The affine family is strongly
\(3\)-universal. It has an exact
finite rank sum below. If \(X\) is uniform on a single affine space
of size \(N\), the leading constant of both \(\Delta_3^*\) and
\(\Delta_{\rm aff}\) is \((M-1)/(2N)\) as \(M/N\to0\), in the
sense that division by this expression tends to one.

## 2. A one-sided third-moment argument

Set \(p=1/M\). Draw a uniformly random output bin \(U\) independently
of the seed. For \(I_x=1_{\{f(x)=U\}}\), the exact collision
equalities give
\[
 \mathbb E\prod_{i=1}^s I_{x_i}=p^s,\qquad 1\le s\le 3
\]
for distinct inputs. The \(s=1\) formula requires only the independent
uniform bin. These identities, or inclusion-exclusion, give the first
three joint moments of independent Bernoulli variables, regardless
of the marginal law of \(f(x)\) itself.

Put \(Z=\sum_x w_x(I_x-p)\) and \(a=\mathbb E Z_+=\mathbb E Z_-\), where
\(Z_+=\max(Z,0)\) and \(Z_-=\max(-Z,0)\). In particular
\(\Delta_F=M a\), since for each \(f\) total variation is the sum of
its output deviations of positive sign over all bins. Terms with
distinct variables and terms with a centered singleton cancel when
expanding the second and third moments, so
\[
 v=\mathbb E Z^2=p(1-p)C_2,\qquad
 w=\mathbb E Z^3=p(1-p)(1-2p)C_3 .
\]
In particular \(v>0,w\ge0\). Since \(Z_-\le p\), we have
\(\mathbb E Z_-^2\le p a\) and \(\mathbb E Z_-^3\le p^2a\).
Cauchy--Schwarz on \(\mathbb E Z_+^2=\mathbb E\sqrt{Z_+Z_+^3}\)
therefore yields
\[
             v\le p a+\sqrt{a(w+p^2a)}.
\]
If \(p a\ge v\) then \(a\ge v/p\ge v^2/(2pv+w)\).
Otherwise square the inequality \(v-pa\le\sqrt{a(w+p^2a)}\);
cancelling \(p^2a^2\) again gives \(a\ge v^2/(2pv+w)\).
Insert the moments and divide by \(p\) to get (1); flat weights give
(2). This proof also covers \(N=1,2\), when some of the distinct-input
conditions are vacuous.

Under an independent public seed, the conditional distance is the
average over \(P_Y\) of the same expression for the law \(X|Y=y\).
Collision equalities of a family on the full domain remain true for
every restriction to a support. Averaging (2) proves the conditional
claim; no map has been selected after observing \(Y\).

For later comparison, under \(2^*\)-universality only, \(v\) is
still \(p(1-p)C_2\). The two bounds \(Z_+\le1-p,\ Z_-\le p\) give
\(v\le (1-p)a+pa=a\), hence
\[
                    \Delta_F(X;M)\ge(1-p)C_2.               \tag{4}
\]
For \(N=2^d\) and \(M=2^m\le N\), uniform \(X\) attains (4) via the
field-affine hash \(\pi_m(a x+b)\), after identifying the input
with \(\mathbb F_{2^d}\). Here \(a,b\) are uniform independent and
\(\pi_m\) is a surjective binary-linear projection. Distinct two
evals \(a x+b, a x'+b\) are independent uniform, by invertibility
of their two-by-two field system. For \(a\ne0\) a uniform input
stays uniform after the projection; for \(a=0\) the conditional
output is constant. Thus \(\Delta=(1-p)/N\) exactly.
This family and error formula already appear in Cheng et al.,
arXiv:2611.34468v1 §V-E; (4) is the elementary matching lower bound
over the entire exact two-collision class. Dropping the star allows
zero distance for the balanced subfamily \(a\ne0\), also in that
source. For \(m\ge2\) and \(d\ge m\), the field-affine ensemble is
not \(3^*\): the exactly attained two-collision value is strictly
below (2) since \(2N+M-2<MN\) whenever \(M>2,N>1\).

## 3. Affine hash and rank computation

A uniform binary \(m\times d\) matrix \(A\), followed by an independent
uniform offset \(b\in\mathbb F_2^m\), is strongly 3-wise independent:
for any at most three distinct points the augmented vectors
\((x_i,1)\) are linearly independent. A relation of odd weight is
excluded by the final coordinate and a nonzero relation of even
weight at most three would identify two of the points. Each row of
\((A,b)\) therefore contributes an independent uniform tuple of
bits. With four inputs \(0,e_1,e_2,e_1+e_2\) when \(d\ge2\), the
four-collision probability is \(M^{-2}\), not \(M^{-3}\).

On a fixed affine subspace \(x_0+V\) of dimension \(k\), the random
restriction \(A|_V\) is a uniform \(m\times k\) binary matrix in
any basis. Each row is uniform independently because \(V\) has a
basis, and evaluating all its basis vectors is a surjective map
on the ambient dual row space. The output law of a conditional
uniform input for each fixed seed is uniform on an affine
subspace of size \(2^j\), \(j=\operatorname{rank}(A|_V)\). Thus its
distance from uniform on \(M\) points is \(1-2^{j-m}\).
An exact formula, valid including \(k=0\) or \(k<m\), is
\[
 B_{m,k}=2^{-mk}\sum_{j=0}^{\min(m,k)}
 (1-2^{j-m})
 \frac{\prod_{i=0}^{j-1}(2^m-2^i)(2^k-2^i)}
 {\prod_{i=0}^{j-1}(2^j-2^i)}.                              \tag{5}
\]
Use empty products for \(j=0\). To count rank \(j\), choose an
ordered independent \(j\)-tuple in the image, divide by the
number of bases of a \(j\)-space to count image subspaces, and
multiply by the number of surjections from the input to a fixed
\(j\)-space, the row rank count in the second product.

For an especially short bound, let \(J=|\ker((A|_V)^T)|=2^{m-j}\)
be the number of left-kernel vectors of the matrix \(A|_V\). Each particular nonzero binary row relation has
probability \(1/N\) of holding, \(N=2^k\). Each pair of distinct
nonzero row relations is independent over \(\mathbb F_2\), so
\[
 \mathbb E(J-1)=\frac{M-1}{N},\qquad
 \mathbb E (J-1)(J-2)=\frac{(M-1)(M-2)}{N^2}.
\]
As \(J\) is a power of two,
\[
 0\le \frac{J-1}{2}-(1-J^{-1})
       =\frac{(J-1)(J-2)}{2J}
       \le\frac{(J-1)(J-2)}8 .
\]
The expression vanishes for \(J=1,2\), and for \(J\ge4\) the last
bound is immediate. It follows that
\[
 \frac{M-1}{2N}-\frac{(M-1)(M-2)}{8N^2}
 \le B_{m,k}
 \le\min\!\left(1,\frac{M-1}{2N}\right).                     \tag{6}
\]
In (3), the first inequality follows from
\(\ell_M(N)\ge\frac14\min(1,M/N)\) for any \(M\ge2,N\ge1\):
if \(N\le M\) use \(4(M-1)\ge2N+M-2\);
if \(N\ge M\) the inequality reduces to
\((M-2)(2N-M)\ge0\).
Using (5) or (6) conditionally and averaging gives (3). Formula
(2), with
\(\ell_M(N)/[(M-1)/(2N)]=2N/(2N+M-2)\), and (6) give the common
leading constant. No independence between \(K\) and the direction
of \(V\) is required. With an independent seed, the same uniform
matrix ensemble works even when the conditioning sets overlap.

If Eve's quantum side information is produced from \(Y\) by any
channel \(Y\to E\), including one preparing noncommuting density
matrices, the same affine-family upper bounds continue to apply by
trace-distance contractivity. The converse is asserted with the
classical \(Y\) itself, not after information has been discarded;
a generic quantum ensemble need not admit this affine-conditioning
model.

### Exact binary-output check for any flat support size

For \(M=2\) and an arbitrary flat \(N\)-point support, the exact
infimum over \(3^*\) is \(1/(2N)\) when \(N\) is even, and
\(1/(N+1)\) when \(N\) is odd. Let \(S\) be the sum of \(N\) hash
output signs. Even without a uniform marginal sign, \(2^*\)
gives \(\mathbb E S^2=N\), and the error is
\(\mathbb E|S|/(2N)\). Set \(a=N\bmod2\). For \(a\le |S|\le N\),
\[
                     |S|\ge\frac{S^2+aN}{N+a}.
\]
This gives the stated lower bound. To attain it, choose an
exchangeable sign vector on the \(N\) inputs with \(|S|\) supported
on \(\{a,N\}\) and \(\mathbb E S^2=N\) (the \(N=1\) case is
constant in absolute value). Choose the overall sign symmetrically.
Each single and triple distinct sign product has mean zero by
sign-flip symmetry, each distinct pair has mean zero by
exchangeability and the second moment, so the signs are strongly
3-wise independent. Add independent uniform output signs for any
inputs outside the chosen support. No analogous equality is claimed
for every \(M>2\).

## 4. Exact i.i.d. error exponents and the universality question

Suppose one copy of \(X\in\mathbb F_2^d\) satisfies the
affine-conditioning hypothesis with finite classical \(Y\).
On \(n\) i.i.d. copies the conditional affine dimension \(K_n\)
is the sum of \(n\) i.i.d. copies of \(K\). Let the binary output
length \(m_n\ge1\) have \(m_n/n\to R\ge0\), in bits per copy.
Equation (3) shows that the infimum over all \(3^*\) families
and the explicit affine family have the same exact reliability
exponent:
\[
\begin{split}
 E_{3^*}(R)
 &= \lim_{n\to\infty}-n^{-1}\log_2\Delta_3^*
  = \min_\nu\left(D_2(\nu\Vert P_K)+[\mathbb E_\nu K-R]_+\right)\\
 &= \max_{0\le\theta\le1}
     \left(-\theta R-\log_2 \mathbb E\,2^{-\theta K}\right).
                                                        \tag{7}
\end{split}
\]
Here \(\nu\) ranges over the probability simplex on the support
of \(P_K\) and \(D_2\) is classical relative entropy in bits,
not a Rényi-order-2 divergence. For the first variational formula,
\(\min(1,2^{m_n-K_n})=2^{-n[K_n/n-m_n/n]_+}\).
The standard multinomial type count bounds the probability of a
type \(\nu\) of \(K\) between
\((n+1)^{-|\operatorname{supp}P_K|}2^{-nD_2(\nu\Vert P_K)}\)
and \(2^{-nD_2(\nu\Vert P_K)}\). The number of types is polynomial
in \(n\) and rational types approximate the whole simplex. This
proves the limit using (3).
For the second formula, set \(P_\theta(k)=P_K(k)2^{-\theta k}/
\mathbb E\,2^{-\theta K}\). For all \(\nu\),
\[
 D_2(\nu\Vert P_K)+\theta(\mathbb E_\nu K-R)
 = D_2(\nu\Vert P_\theta)-\theta R-\log_2\mathbb E2^{-\theta K}.
\]
The rightmost objective of (7) is concave in \(\theta\), with
derivative \(\mathbb E_{P_\theta}K-R\).
At an interior maximizer the tilted mean equals \(R\); at a
maximizer \(\theta=0\) it is at most \(R\), and at \(\theta=1\) it is
at least \(R\). Using that \(P_\theta\) as \(\nu\) gives equality
in replacing the positive part by its linear minorant, proving (7).

For comparison, the \(4^*\) exponent from Regula--Cheng is the
same maximum with \(0\le\theta\le1/2\). Indeed for classical
\(Y\) the sandwiched optimized conditional entropy is the Arimoto
quantity, with
\[
 \theta H_{\alpha}^{\uparrow}(X|Y)
   =-\log_2\sum_y P_Y(y)
       \left(\sum_x P_{X|y}(x)^\alpha\right)^{1/\alpha}
   =-\log_2\mathbb E2^{-\theta K},
 \quad \theta=(\alpha-1)/\alpha .
\]
The first equality follows directly by optimizing the classical
reference probability for \(Y\) by Hölder's inequality (or
Lagrange multipliers). Dephasing the reference on classical \(Y\)
cannot increase the sandwiched divergence, so a classical reference
suffices. The second equality uses flatness. For example,
take uniform binary input and independently reveal the bit
with probability \(1-\eta\), recording an erasure otherwise.
Then \(K=1\) with probability \(\eta\), \(0\) otherwise.
Equation (7) gives the maximum of
\(-\theta R-\log_2(1-\eta+\eta 2^{-\theta})\).
For \(0<\eta<1\) this strictly exceeds the \(4^*\) value whenever
\(0<R<\eta/(\sqrt2(1-\eta)+\eta)\): the derivative at
\(\theta=1/2\) is positive. The erasure expression itself is known
as the complementary erasure-channel random coding exponent
(see SOURCES.md). Here the same value is optimal over *all*
\(3^*\)-universal ensembles; it is not an unrestricted or expurgated
optimum. Another covered example is an independent random
binary linear observation of each uniform source block, with
both the observation matrix and its value recorded in \(Y\).
Conditional dimension is the number of columns minus matrix rank.

For trivial side information and one equiprobable bit per copy,
the exact optimal exponents at \(0<R<1\) are
\[
       E_{2^*}=1,\qquad E_{3^*}=1-R,\qquad E_{4^*}=(1-R)/2 .
\]
The first follows from (4) and the field-affine equality example,
the second from (7) with \(K=1\), the third from Regula--Cheng's
formula. The separation also disproves a constant-factor one-shot
converse of their form under strong three-wise independence. On
a flat \(N\)-point law with no side information, their quadratic
test value \(\pi^{\mathrm{half}}_{M/4}\) (the half-quadratic test, with
constraint \(\sum_x t_x^2\le M/4,\ 0\le t_x\le1\)) is
\(\min(1,\sqrt{M/(4N)})\), by Cauchy--Schwarz and a constant
weight on the support. Equation (6) is at most \((M-1)/(2N)\);
its ratio to the test tends to zero for \(M/N\to0\).

Thus order four is necessary **if one asks which exact collision
order alone suffices** for the Regula--Cheng ensemble-wide
converse. Even strongly \(3\)-universal families can give smaller
error. This does not decide the weakest possible assumptions
on other features such as tails, approximate fourth moments,
or structure of the seed ensemble. It gives no converse for
general quantum side information or for \(3\)-universal families
stated only with inequalities. The last qualification is necessary:
for a uniform source of size \(N\) divisible by \(M\), draw uniformly
from the balanced maps with fibers of size \(N/M\). They give zero
error and are \(j\)-universal in the inequality sense for every \(j\):
the \(i\)-collision probability is \(M(N/M)_i/(N)_i\le M^{1-i}\)
for \(i\le N\), where \((u)_i\) is a falling factorial. If
\(i\le N/M\), this follows by factoring out the first term and
bounding each ratio \((N/M-h)/(N-h)\) by \(1/M\); otherwise
the probability is zero.
