# All-rate trace-distance exponent for phase-covariant sources

All logarithms below have base two. Let \(q\) be a fixed prime
power, \(k\ge 1\), and \(G=\mathbb F_q^k\). Fix a nontrivial
additive character \(\chi:\mathbb F_q\to\mathbb C\). For each
classical flag \(y\) in a finite alphabet, specify a probability
distribution \(\lambda_y\) on \(G\). The classical label
\(X\) is uniform on \(G\) and independent of \(Y\sim p\);
given \(x,y\), the side information contains the orthogonal flag
\(y\) and the pure state
\[
 |\psi_{x,y}\rangle
   = \sum_{t\in G}\sqrt{\lambda_y(t)}\,\chi(x\cdot t)|t\rangle.
\]
Define the joint distribution \(P(y,t)=p(y)\lambda_y(t)\); \(T\)
under \(P\) is a classical phase label, not a measurement of the
honest label. Assume \(H_P(T|Y)>0\) unless stated otherwise.

At blocklength \(n\), the public seed independently samples
\(A:\mathbb F_q^{kn}\to\mathbb F_q^{r_n}\), uniformly among
full-row-rank matrices, with \(1\le r_n\le kn\). A translation
of the output, including an independent public random offset,
does not change the error. Extract \(Z=AX^n\). The error is the
expected trace distance from uniform \(Z\) times the true side
marginal, with the hash choice public. If
\[
 R=\lim_n \frac{r_n\log q}{n},\qquad c=k\log q-R,
\]
then
\[
 \lim_{n\to\infty}-\frac1n\log
   \mathbb E_A T(\rho^{A}_{ZE^n},\,U_Z\otimes\rho_{E^n})
 = \min_{Q\ll P}\{D(Q\|P)+(c-H_Q(T|Y))_+\}.                 \tag{1}
\]
This is the exponent of the **ensemble average**, not the
best code or the typical seed. The same exponent holds when
all matrix entries are sampled independently and uniformly
without conditioning on the rank. No independence of
distinct bins is assumed.

For a single flag this is the exponent of the additive
noise law \(\lambda\). In the binary case it gives the
complete exponent for any nondegenerate pair of equal-prior
pure side states: a global phase makes the overlap real
nonnegative, and their normalized sum and difference give an
orthogonal basis with spectral probabilities
\(\lambda_\pm=(1\pm|\langle\psi_0|\psi_1\rangle|)/2\).
Identical rays are the deterministic edge case discussed below.

## 1. A fixed matrix and its phase blocks

At fixed \(y^n\), abbreviate the product phase probabilities
by \(P_w=\prod_i\lambda_{y_i}(w_i)\), \(w\in V=\mathbb F_q^N\),
\(N=kn\). Averaging the phase states over uniform \(X^n\)
gives the diagonal state with entries \(P_w\). Conditional on
any particular \(AX^n=z\), the uniform input is a translate
of \(\ker A\). The average of the character
\(\chi(x\cdot(w-w'))\) on that translate vanishes unless
\(w-w'\in(\ker A)^\perp=\operatorname{row} A\), and otherwise
is a phase of modulus one. Indeed, if the field-linear
functional on \(\ker A\) given by \(w-w'\) is nonzero, it
maps onto \(\mathbb F_q\), over which \(\chi\) sums to zero.
The remaining phases are removed by diagonal unitary
conjugation determined by a representative of the translate.

Thus for each \(z\) the deviation from the true marginal
has unitarily equivalent blocks indexed by cosets \(B\) of
\(\operatorname{row} A\):
\[
 M_B=|v_B\rangle\langle v_B|-\mathrm{diag}(P_w:w\in B),
       \qquad v_B(w)=\sqrt{P_w}.
\]
The error at fixed flag is \(\frac12\sum_B\|M_B\|_1\).
In particular the offset in the extracted key is immaterial.
On \(v_B^\perp\) the quadratic form is nonpositive, so there
is at most one positive eigenvalue; \(M_B\) is traceless.
If the positive eigenvalue is \(\gamma\), the negative
eigenvalues' absolute values sum to \(\gamma\). Hence
\(\gamma^2\le\|M_B\|_2^2\le2\gamma^2\); if the block has no
positive eigenvalue it is zero. Entrywise,
\(\|M_B\|_2^2=\sum_{w\ne w'\in B}P_wP_{w'}\).
In particular, writing \(S_B\) for this ordered-pair sum,
\[
 \frac1{\sqrt2}\sum_B\sqrt{S_B}
       \le T(\rho^A_{ZE|y^n},U_Z\otimes\rho_{E|y^n})
       \le \sum_B\sqrt{S_B}.                               \tag{2}
\]
This compares exact trace distance to an ordinary count of
pairs, not to the square root of an average decoding error.

## 2. Finite occupancy bounds

Take any probability mass \(P_w\) on \(V\), not necessarily
a product. Partition its positive support into any disjoint
classes \(T_j\) on each of which \(P_w\) is a fixed value \(v_j\).
Let \(N_j=|T_j|\), \(m=q^{N-r}\), and
\[
 a_j=N_j/m,\qquad
 \Psi_j=v_jN_j\min(1,a_j).
\]
For the average trace distance the finite bounds are
\[
 \frac{1-1/q}{2\sqrt2(q+1)}
       \max\Big\{\max_{j:N_j\ge2}\Psi_j,\ \max_{i\ne j}\sqrt{\Psi_i\Psi_j}\Big\}
 \le \mathbb E_A T
 \le \left(\sum_j\sqrt{\Psi_j}\right)^2 .                   \tag{3}
\]
Each lower maximum over an empty index set is zero.

View the \(m\) cosets as bins of an independently labelled
affine quotient \(f(w)=Bw+a\), where \(B\) is uniform full
rank \(N-r\) by \(N\) and \(a\) uniform. Its kernel is uniform
among \(r\)-dimensional subspaces, as is the row space of
uniform \(A\). Relabelling leaves sums over bins unchanged.
For distinct \(u,v\), the probability their difference
belongs to the kernel (their outputs collide) is
\[
 p_2=\frac{q^r-1}{q^N-1},
 \qquad (1-1/q)/m\le p_2\le1/m .
\]
The joint event that they are both in a given bin has
probability \(p_2/m\). Given this event, affine combinations
of \(u,v\) lie in that bin. For \(w\) off their field-affine
line, the two directions are field-linearly independent, so
the conditional probability of a further hit is
\((q^r-q)/(q^N-q)\le1/m\); off-line points can exist only if
\(N\ge2\). This follows by symmetry: conditional on one
nonzero direction entering the kernel, every vector outside
its span has the same chance, and \(q^r-q\) such vectors
are in the kernel. The uniform offset makes the additional
bin-label conditioning independent of the kernel.

Fix a bin and let \(U_j\) count its elements from \(T_j\).
For \(i\ne j\) there are four upper bounds on
\(\mathbb E\sqrt{U_iU_j}\):
\[
 a_i a_j,\quad a_i\sqrt{a_j},\quad \sqrt{a_i}a_j,\quad
 \sqrt{a_i a_j}.
\]
For the first use \(\sqrt{uv}\le uv\) on nonnegative integer
counts and the pair inclusion probability. For the second use
\(\sqrt{U_iU_j}\le U_i\sqrt{U_j}\), expand the first factor by
points, and condition on the given point entering the bin.
The expected other-class count is \(N_jp_2\le a_j\).
Then Jensen gives the second bound; symmetry gives the third.
The fourth follows from Cauchy-Schwarz and
\(\mathbb E U_j=a_j\). Taking the minimum of all four
gives \(\min(a_i,\sqrt{a_i})\min(a_j,\sqrt{a_j})\).
For a single class the corresponding ordered pair count is
\(U_j(U_j-1)\), so
\(\mathbb E\sqrt{U_j(U_j-1)}\le\min(a_j,a_j^2)\)
by comparison with \(U_j\) and with \(U_j(U_j-1)\).
Multiplication by \(m\sqrt{v_iv_j}\) (or by \(mv_j\) for
the same class) gives at most \(\sqrt{\Psi_i\Psi_j}\).
Apply \(\sqrt{\sum b_l}\le\sum\sqrt{b_l}\) on all ordered
class pairs in \(S_B\), then sum over bins, proving the upper
bound in (3).

For the lower bound, use only one class \(T_j\) with \(N_j\ge2\).
On \(U_j\ge2\),
\(\sqrt{U_j(U_j-1)}\ge U_j(U_j-1)/U_j\).
Expand the numerator as the sum of ordered point-pair
indicators. For each particular pair entering the bin,
\(\mathbb E[U_j\mid \text{pair in bin}]\le q+a_j\):
at most \(q\) points are on the pair's affine line, and all
remaining points have conditional inclusion at most \(1/m\).
Jensen applied to \(x\mapsto1/x\) gives
\[
 \mathbb E \sum_B \sqrt{U_j(B)(U_j(B)-1)}
 \ \ge\ \frac{N_j(N_j-1)p_2}{q+a_j}.
\]
Since \(N_j(N_j-1)\ge N_j^2/2\) and
\(a_j/(q+a_j)\ge \min(1,a_j)/(q+1)\), the lower
bound in (2) gives the same-class part of the lower bound.

For two different classes, expand
\(\sqrt{U_iU_j}=U_iU_j/\sqrt{U_iU_j}\) on \(U_iU_j>0\)
over pairs. Given any such pair in the bin, the two
conditional means are at most \(q+a_i,q+a_j\) by the same
line count. The function \((x,y)\mapsto1/\sqrt{xy}\) is
convex for \(x,y>0\), since it is the exponential of
\(-(\ln x+\ln y)/2\). Jensen gives
\[
 \mathbb E\sum_B\sqrt{U_i(B)U_j(B)}
 \ \ge\ \frac{N_iN_jp_2}{\sqrt{(q+a_i)(q+a_j)}} .
\]
Use \(q+a\le(q+1)\max(1,a)\), \(p_2\ge(1-1/q)/m\),
and multiply by \(\sqrt{v_iv_j}\). After (2) this gives
the cross-class part of (3), even with twice the displayed
lower constant. This deals in particular with two or
more positive singleton classes at short blocklength.
With only one positive phase word all the blocks vanish.

## 3. Conditional types and the exact exponent

For fixed \(y^n\), partition phase words into their
conditional types, or equivalently by the whole joint type
\(\widehat Q_{YT}\) with fixed flag marginal. The number of
conditional types is polynomial in \(n\), uniformly in
\(y^n\). Each class size is between
\(2^{nH_{\widehat Q}(T|Y)}\) times an inverse polynomial
and that value; its phase probability mass is between
\(2^{-nD(\widehat Q_{T|Y}\|\lambda\mid\widehat Q_Y)}\)
times an inverse polynomial and that value. These estimates
are the multinomial type-size bounds on each nonempty flag
block, multiplied over flags. Types outside the support of
\(P\) contribute zero. Thus its \(\Psi\) in (3) has cost
\[
 D(\widehat Q_{T|Y}\|\lambda\mid\widehat Q_Y)
             +(c_n-H_{\widehat Q}(T|Y))_+,\qquad
 c_n=(kn-r_n)\log q/n,
\]
with uniform polynomial factors. Indeed the \(\min(1,N_j/m)\)
factor has this second cost, and multiplying its argument
by any \(a\le1\) changes the result by at most \(a^{-1}\).

Trace distance averages exactly over the orthogonal \(Y^n\)
sectors. Flag type probability costs
\(D(\widehat Q_Y\|p)\) up to polynomial factors. The
conditional average depends only on the flag type,
because a block-coordinate permutation simultaneously
permutes phase words and preserves the uniform matrix law.
Combine costs by the relative entropy chain rule. In the
upper bound use
\((\sum_j\sqrt{\Psi_j})^2\le K_n^2\max_j\Psi_j\),
where \(K_n\) is the number of types. Summing polynomially
many flag types gives the lower bound on the exponent in (1).
For the matching bound choose any \(Q\ll P\) with positive
conditional entropy, approximate it by joint types with the
same support for sufficiently large \(n\), and apply their
term in the lower bound of (3). The conditional class then
has size at least two. Any minimizer \(Q\) on the boundary,
including deterministic conditional types, can be approached
by mixtures with \(P\), which have positive conditional
entropy because \(H_P(T|Y)>0\). Continuity on the supported
simplex and \(c_n\to c\) prove equality.

In the full-matrix ensemble, conditional on full rank we
recover the ensemble already treated. Rank-defect probability
is at most \(q^{r_n-kn}\), by a union bound over nonzero
dependencies among the rows. If \(c>0\), the exponent in
(1) is strictly less than \(c\) by testing \(Q=P\), so
the defective contribution is negligible for the exponent
since trace distance is at most one. If \(c=0\), the
exponent is zero by (1) and the probability of full rank
is bounded below by \(\prod_{j\ge1}(1-q^{-j})>0\).
These arguments also cover \(R=0\) with a nonempty output
at every sufficiently large \(n\).

If every positive-probability flag has a deterministic
phase label, the quantum rays are independent of \(X\).
The full-rank error is identically zero; in the unrestricted
ensemble the error at rank \(s\) is \(1-q^{s-r_n}\).
The full-rank probability
\(\prod_{i=0}^{r_n-1}(1-q^{i-kn})\) and the union bound give
exponent \(c\) for the latter average when \(r_n\ge1\).
This case is separate from (1). A singleton output
(\(r_n=0\)) always has zero error.

## 4. Gallager form and the published binary equation

With \(S_y(\theta)=\sum_t\lambda_y(t)^{1/(1+\theta)}\),
the right side of (1) equals
\[
 \max_{0\le\theta\le1}
 \left\{\theta c-\log\sum_y p(y)\,S_y(\theta)^{1+\theta}\right\}.
                                                               \tag{4}
\]
Indeed \((c-H)_+=\max_{\theta\in[0,1]}\theta(c-H)\).
The expression \(D(Q\|P)+\theta(c-H_Q(T|Y))\) is convex
in \(Q\) (conditional entropy is concave), affine in
\(\theta\), and continuous on the compact supported
simplex and interval. Thus min and max can be interchanged
by the convex minimax theorem. For fixed \(\theta\), first
minimize over each \(Q_{T|Y=y}\): it is proportional to
\(\lambda_y(t)^{1/(1+\theta)}\), with value
\(-(1+\theta)\log S_y(\theta)\) in its conditional part,
by subtracting a nonnegative divergence. The minimization
over \(Q_Y\) then similarly gives
\(-\log\sum_y p(y)S_y(\theta)^{1+\theta}\).
This is Gallager's random-coding function at rate \(R\)
for the classical additive channel with uniform input and
receiver-known flag: its transition probability is
\(W(z,y|x)=p(y)\lambda_y(z-x)\) and the finite input
alphabet has size \(q^k\). The inner sum in
Gallager's expression is \(p(y)^{1/(1+\theta)}S_y(\theta)/q^k\),
constant in \(z\); summing its \((1+\theta)\)-powers over
\(z,y\) gives the stated form. Here (4) is proved for average quantum
true-marginal trace-distance error, not obtained by a
fidelity comparison.

For \(q=2,k=1\) and one flag with law \(\lambda=(1-p,p)\),
(4) is
\[
 \max_{0\le\theta\le1}\theta[1-R-H_{1/(1+\theta)}(\lambda)].
\]
Hayashi's arXiv:1202.0322v6 Appendix E, Lemma 39
(rendered Eq. (151), PDF Eq. (150)) uses these same binary
phase states and, for \(R>0\), the same asymptotic
uniform random quotient sequence, with unhalved trace norm \(d'_1\). That constant factor does not change
the exponent. Substituting \(\theta=s/(1-s)\) in the v6
displayed formula gives **one half** of (4), not (4).
For nondeterministic \(\lambda\), (4) is strictly positive
at every \(R<1-H(\lambda)\) since its derivative at zero
is \(1-R-H(\lambda)>0\). Thus the two expressions differ
on \(0<R<1-H(\lambda)\). At \(R=0\) the displayed
variational expressions are still related algebraically,
but Hayashi's literal codimension \(\lfloor nR\rfloor\)
is then zero, so its key is a singleton and the error is
zero. Our finite zero-rate exponent concerns a nonempty
key sequence (\(r_n\ge1\) eventually), not that sequence.
This comparison only concerns the specified preprint and
ensemble. It neither treats the subsequent bound for a
different quantity as the same equality, nor evaluates
the unverified journal text, other sources, or all families.
