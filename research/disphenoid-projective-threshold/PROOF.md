# Exact two-qubit projective simulation in a diagonal correlation class

## 1. Measurement and state model

There are four outcome labels on each side. A local POVM is
projective-simulable (PS) when it is an independent private mixture of
projective measurements on the same qubit followed by classical
outcome processing. The only shared resource is an arbitrary density
operator on two qubits. Equivalently the observed distribution must be
\(\operatorname{Tr}[\rho(M_a\otimes N_b)]\) for two PS POVMs.
One may not use an additional common classical random draw to correlate
the local simulator choices. This is the model of
Rout–Horodecki–Bhattacharya (RHB), arXiv:2611.33559v1.

Let \(s_a\), \(0\le a<4\), be the four sign vectors of even minus
parity:
\[
 s_0=(1,1,1),\quad s_1=(1,-1,-1),\quad
 s_2=(-1,1,-1),\quad s_3=(-1,-1,1).
\]
Then \(\sum_a s_a=0\) and \(\sum_a s_as_a^T=4I_3\).
For a real triple \(c=(c_1,c_2,c_3)\), consider
\[
 P(c)_{ab}=\frac{1+\sum_i c_i s_{a,i}s_{b,i}}{16}.       \tag{1}
\]
If it is a probability matrix, its marginals are \(1/4\), and its
sign-vector cross-covariance is exactly \(\operatorname{diag}c\).
Nonnegativity is equivalent to \(1+\sum_i c_i s_{a,i}\ge0\)
for the four labels, since the sign vectors are closed under
coordinatewise products.

**Theorem.** Write \(r_i=\sqrt{|c_i|}\), and sort these three
numbers in decreasing order just for evaluating \(g\). Define
\[
 g(r)=
 \begin{cases}
 \sqrt{r_1^2+(r_2+r_3)^2},& r_1\ge r_2+r_3,\\
 (r_1+r_2+r_3)/\sqrt2,&r_1\le r_2+r_3 .
 \end{cases}                                                \tag{2}
\]
The branches agree at their common boundary.
Equation (1) has a two-qubit, two-PS realization if and only if
\(g(r)\le1\). The result includes all signs, all zero coordinates,
and \(c=0\). In the sufficiency direction it already implies that
(1) is a probability matrix.

## 2. Necessary bound: optimize the covariance encoding

For a common encoding \(x_a\) of the outcome labels as real vectors,
let \(D=\max_{a,b}\|x_a-x_b\|_2\) and let \(\Gamma\) denote the encoded
cross-covariance. The RHB Proposition IV.1 uses
\(\chi(\Gamma)=\sum_i\sqrt{\sigma_i(\Gamma)}\), where \(\sigma_i\)
are singular values, and proves \(\chi(\Gamma)\le D/2\) for every
two-PS realization. Here is a brief self-contained proof.

Writing the vector-valued operator
\(\sum_a x_a M_a\) by its Pauli coefficients gives an identity
coefficient vector and a response matrix \(R_A\) whose columns
multiply \(\sigma_1,\sigma_2,\sigma_3\).
In a single projective branch with unit Bloch axis \(u\), let
\(x_+,x_-\) be the average encoded labels after post-processing the
two projective outcomes. The response is
\((x_+-x_-)u^T/2\), whose nuclear norm is at most \(D/2\), since
\(x_\pm\) are convex combinations of labels. A deterministic
constant-output branch has response zero. Convexity gives
\(\|R_A\|_*\le D/2\), and the same for \(R_B\).
Centering cancels the identity coefficients, giving
\(\Gamma=R_A K R_B^T\), where
\[
 K_{ij}=\operatorname{Tr}(\rho\,\sigma_i\otimes\sigma_j)
       -\operatorname{Tr}(\rho\,\sigma_i\otimes I)
        \operatorname{Tr}(\rho\,I\otimes\sigma_j).
\]
For unit vectors \(u,v\), the centered observables
\(u\cdot\sigma\otimes I\) and \(I\otimes v\cdot\sigma\)
have variances at most 1. Cauchy–Schwarz in the state gives
\(|u^T K v|\le1\), so \(K\) is an operator-norm contraction.

For completeness, for any compatible matrices \(F,G\) of rank at
most three, \(\sum_i\sqrt{\sigma_i(FG)}
\le\sqrt{\|F\|_*\|G\|_*}\); the same argument works in arbitrary
finite rank. Exterior powers give the partial-product bounds
\(\prod_{i=1}^j\sigma_i(FG)\le\prod_{i=1}^j\sigma_i(F)\sigma_i(G)\)
for singular values in decreasing order. In general these bounds
are the submultiplicative operator norm on exterior powers, with
zero singular values padded if needed. If decreasing nonnegative
sequences \(a_i,b_i\) have such partial-product inequalities, then
for every real \(t\),
\(\sum_i(\ln a_i-t)_+\le\sum_i(\ln b_i-t)_+\), taking the maximum
of log partial sums minus \(jt\), with zero terms omitted.
Integrating against \(e^{t/2}/4\) gives
\(\sum_i\sqrt{a_i}\le\sum_i\sqrt{b_i}\).
Finally apply scalar Cauchy–Schwarz. The singular values of
\(R_AK\) are bounded termwise by those of \(R_A\) by the
rank-approximation characterization. This proves
\(\chi(R_AKR_B^T)\le\sqrt{\|R_A\|_*\|R_B\|_*}\le D/2\).

Now use \(x_a=(w_1s_{a,1},w_2s_{a,2},w_3s_{a,3})\) with \(w_i\ge0\).
Any two distinct even-parity sign vectors differ in exactly two
coordinates, and every pair of coordinate positions occurs. Thus
\[
 \frac{D}{2}=\max_{i<j}\sqrt{w_i^2+w_j^2},\qquad
 \Gamma=\operatorname{diag}(w_i^2c_i),\qquad
 \chi(\Gamma)=\sum_i w_i r_i.
\]
So a PS realization requires
\[
 \sum_i w_i r_i\le1
   \quad\text{for all }w_i\ge0\text{ with }\max_{i<j}(w_i^2+w_j^2)\le1.
                                                               \tag{3}
\]
Sort the \(w_i\) to match the decreasing \(r_i\), by rearrangement.
The constraint becomes \(w_1^2+w_2^2\le1\), \(w_1\ge w_2\ge w_3\).
One can take \(w_3=w_2\) and reach the arc \(w_1^2+w_2^2=1\).
Writing \(w_1=\cos\theta,w_2=\sin\theta\) for
\(0\le\theta\le\pi/4\), the quantity to maximize is
\(r_1\cos\theta+(r_2+r_3)\sin\theta\).
Its maximizer is the unconstrained weight proportional to
\((r_1,r_2+r_3)\) if \(r_1\ge r_2+r_3\) and the endpoint
\(\theta=\pi/4\) otherwise. This proves (2) and the theorem's
necessary direction. For \(r=0\), the maximum is zero.
For \(r_i>0\) the sorted maximizing weight is unique.

## 3. Sufficient bound: implement the extremal pieces

For any unit vector \(u\in\mathbb R^3\) with nonzero entries
restricted to two chosen coordinates \(i,j\) (one may vanish), define
the four-effect POVM
\[
 M_a(u)=\frac14\big(I+(\operatorname{diag}(u)s_a)\cdot\sigma\big).
                                                               \tag{4}
\]
Let \(k\) be the omitted coordinate. The two pairs of labels with
common \(s_{a,k}\) are disjoint, and the two vectors
\(\operatorname{diag}(u)s_a\) within each pair are opposites.
Privately select one of the two pairs with probability \(1/2\).
Perform the qubit PVM with the axis of the first label and report
the first label for plus and the other for minus. This induces
(4), with exactly the factor \(1/4\). The construction works
also when entries of \(u\) are negative. \(M(0)\) ignores the quantum
system and outputs a private uniform label, and is PS.

For \(r\ge0\), \(g(r)>0\), the following explicit mixtures of those
unit, at-most-two-support atoms give \(r/g(r)\). Use the sorted
physical coordinate labels in the formulas and undo the sorting at
the end.

- If \(r_1\ge r_2+r_3>0\), the atoms are
  \[
  u^{12}=\frac{(r_1,r_2+r_3,0)}{g}, \qquad
  u^{13}=\frac{(r_1,0,r_2+r_3)}{g},
  \]
  with probabilities \(r_2/(r_2+r_3)\) and \(r_3/(r_2+r_3)\).
  If \(r_2+r_3=0\), the single atom \((1,0,0)\) suffices.
- If \(r_1\le r_2+r_3\), put \(S=r_1+r_2+r_3\) and use
  \(u^{ij}=(e_i+e_j)/\sqrt2\) with probability
  \((r_i+r_j-r_k)/S\), where \(k\) is the omitted index.
  These are nonnegative by the triangle inequalities and sum to one;
  the \(i\)th coordinate of their mean is \(\sqrt2\,r_i/S=r_i/g\).

Thus if \(g(r)\le1\), mixing the boundary POVM with \(M(0)\)
using respective weights \(g(r)\) and \(1-g(r)\) produces \(M(r)\).
If \(r=0\), use \(M(0)\) directly. Reflecting individual coordinates
of all atoms shows that \(M(\varepsilon\odot r)\) is PS for any
axis sign pattern \(\varepsilon_i\in\{-1,1\}\).

On an ideal singlet take Alice's \(M(r)\) and Bob's
\(M(\varepsilon\odot r)\), with \(\varepsilon_i=-\operatorname{sgn}c_i\)
when \(c_i\ne0\), arbitrary when \(c_i=0\).
The singlet has zero Bloch marginals and
\(\langle\sigma_i\otimes\sigma_j\rangle=-\delta_{ij}\).
The Born formula is therefore precisely (1).
Both measurements are PS with independent local branch choices;
they need no common choice of the atom or of the pair. This proves
sufficiency including the equality points.

## 4. All unbiased extremal four-outcome measurements and white noise

Let \(M_a=(I+n_a\cdot\sigma)/4\) be any unbiased rank-one
four-effect qubit POVM, with \(\|n_a\|=1\).
Unbiased here means equal effect trace and hence uniform outcomes
on the maximally mixed state. Each genuine four-outcome extremal
qubit POVM has rank-one nonzero effects: if a full-rank effect and
another nonzero effect existed, a sufficiently small positive or
negative perturbation proportional to the other effect could be
transferred between them. Rank-one effects are extremal exactly
when linearly independent: any positive decomposition of an
effect stays in its one-dimensional support, and a nontrivial
real relation permits a small rescaling in both directions.
This is the standard criterion also cited in RHB.

The POVM condition gives \(\sum_a n_a=0\).
Set \(v_i=(n_0+n_i)/2\) for \(i=1,2,3\). These three vectors
are mutually orthogonal: for distinct \(i,j,k\in\{1,2,3\}\),
\(\|n_0+n_i+n_j\|^2=\|n_k\|^2=1\), which gives
\(1+n_0\cdot n_i+n_0\cdot n_j+n_i\cdot n_j=0=4v_i\cdot v_j\).
Also \(n_a=\sum_i s_{a,i}v_i\). Thus \(r_i=\|v_i\|\),
\(\sum_i r_i^2=1\); the rank-one effects are linearly independent
exactly when all \(r_i>0\), by the invertible sign-character matrix.
Using axes \(v_i/r_i\) gives the RHB Equation (35) family,
\(r_i^2=q_i\), up to a choice of labeling and orthonormal frame.
No physical improper rotation is needed: projective axes can be
chosen directly in the given frame, and singlet dot products do
not depend on its orientation.

Using the same measurement on both sides of a noisy singlet
\(\rho_v=v|\Psi^-\rangle\langle\Psi^-|+(1-v)I/4\)
gives (1) with \(c_i=-v r_i^2\). Homogeneity in (2) yields
\[
 v_{\rm crit}=g(r)^{-2},\qquad \eta_{\rm crit}=1-v_{\rm crit}.
                                                               \tag{5}
\]
Both PS reproductions exist at and below the critical visibility;
above it the witness excludes any two-PS realization on any
two-qubit state. For any fixed local trace-preserving depolarization
\(M_a^{(t)}=(I+t\,n_a\cdot\sigma)/4\), the exact **single**-POVM
PS threshold is also \(t_{\rm PM}=1/g(r)\): the explicit atoms
prove sufficiency, and any local PS realization at larger \(t\)
on both sides of a singlet would violate (3). Thus the RHB
upper simulation bound (36) is exact on this class.

For the highlighted \((q_1,q_2,q_3)=(1/2,1/4,1/4)\),
\(g(r)^2=(3+2\sqrt2)/4\),
\(v_{\rm crit}=12-8\sqrt2\), and
\(\eta_{\rm crit}=8\sqrt2-11>1/4\).
For the isotropic tetrahedral SIC, \(g(r)^2=3/2\) and
\(\eta_{\rm crit}=1/3\), the known value. If a coordinate is zero,
\(g(r)^2=1\) and the local measurement is PS even without noise.
The two formulas also agree when \(r_1=r_2+r_3\).

For all positive nonisotropic triples, the exact tolerance is
strictly greater than the original diameter certificate \(q_{\min}\).
Indeed that certificate is (3) tested only at the weight
\(w=r/\sqrt{r_1^2+r_2^2}\), and this is never a maximizer unless
all three coordinates agree: in the dominant case the optimizing
weight has \(w_2=w_3\) proportional to \(r_2+r_3\), not to
\(r_2,r_3>0\); in the other case all weights agree.
Moreover the SIC uniquely maximizes \(\eta_{\rm crit}\) on this
family. In the balanced branch,
\(g(r)^2=(\sum r_i)^2/2\le3/2\) with equality only at the SIC.
In the dominant branch,
\(1\ge(r_2+r_3)^2+r_2^2+r_3^2\ge6r_2r_3\), so
\(g(r)^2=1+2r_2r_3\le4/3\).

The theorem is also exact for this measurement family on any
state with zero Bloch marginals and a diagonal correlation tensor
in its measurement frame. With tensor diagonal \(t_i\), substitute
\(c_i=r_i^2t_i\). This covers aligned Bell-diagonal noise, not
arbitrary misalignment or states with biased marginals. Nor does
it claim the general thresholds for biased three- or four-outcome
extremal POVMs posed in RHB Section V.

## 5. Exact threshold for a realization with at least one PS measurement

The preceding theorem decides whether the observations **require at
least one non-PS measurement**. It is a different question whether
they require both measurements to be non-PS. The same diagonal class
also has an exact answer to the second question.

Let \(d_i=|c_i|\), ordered \(d_1\ge d_2\ge d_3\), and write
\(A=d_1^{2/3}\), \(B=d_2^{2/3}+d_3^{2/3}\). Set
\[
  J(d)=\begin{cases}
  d_1+B^{3/2},&A\ge B,\\
  (A+B)^{3/2}/\sqrt2,&A\le B.
  \end{cases}                                                 \tag{6}
\]
Then \(P(c)\) is realizable on a two-qubit state with at least one
PS local measurement and the other local measurement arbitrary
**if and only if \(J(d)\le1\)**. Both branches agree at equality.
The statement is equivalent to allowing Alice to be the PS party,
because \(P(c)\) is symmetric. This does not assume which party
is PS in the observed experiment.

For necessity, use independent mathematical encodings
\((w_i s_{a,i})_i\) and \((z_i s_{b,i})_i\) on the two sides,
with \(w,z\ge0\). The PS side has response nuclear norm at most
\(U(w):=\max_{i<j}\sqrt{w_i^2+w_j^2}\), as in Section 2.
For the arbitrary qubit POVM on the other side, write its effects
\(\mu_b(I+n_b\cdot\sigma)\), \(\sum_b\mu_b=1\), \(\|n_b\|\le1\).
Its response is a sum of rank-one matrices
\(\sum_b\mu_b(z\odot s_b)n_b^T\), and has nuclear norm at
most \(\|z\|_2\). The very same covariance factorization and
contraction bound therefore give
\[
 \sum_i\sqrt{d_i w_i z_i}\le\sqrt{U(w)\|z\|_2}.
\]
For fixed \(w\) with \(U(w)\le1\), maximizing the left side over
\(\|z\|_2\le1\) is ordinary conjugate \(4/3,4\) Hölder
optimization in \(\sqrt{z_i}\). The maximum equals
\(F(w)^{3/4}\), where \(F(w)=\sum_i d_i^{2/3} w_i^{2/3}\).
Thus \(\max_{w\ge0,U(w)\le1}F(w)\le1\). Sorting the weights
and taking \(w_3=w_2\) and \(w_1^2+w_2^2=1\) reduces
this to maximizing
\[
 A x^{1/3}+B(1-x)^{1/3},\qquad \tfrac12\le x=w_1^2\le1 .
\]
The unrestricted critical point is
\(x=A^{3/2}/(A^{3/2}+B^{3/2})\), with endpoints understood when
one coefficient is zero. This point is feasible exactly when
\(A\ge B\); otherwise the maximum is at \(x=1/2\).
It follows that \(J(d)=(\max F)^{3/2}\), proving necessity.

For sufficiency when all \(d_i>0\), take an explicit maximizing
\(w\) just found, with all \(w_i>0\), and let \(F=F(w)\).
Set
\[
   a_i=\frac{d_i^{2/3}w_i^{-1/3}}{F},\qquad
   b_i=\frac{d_i}{a_i}.
\]
For every \(u\ge0\) with \(U(u)\le1\), the right derivative of
\(F((1-t)w+tu)\) at \(t=0\) is nonpositive by maximality.
As this derivative is \((2/3)F\,a\cdot(u-w)\), we have
\(a\cdot u\le a\cdot w=1\). The dual formula (3) therefore
gives \(g(a)=1\), so \(M(a)\) is PS by the explicit mixture
above. The vector \(b\) satisfies
\[
 \|b\|_2^2=F^2\sum_i d_i^{2/3} w_i^{2/3}=F^3=J(d)^2.
\]
Thus, if \(J(d)\le1\), \(M(\varepsilon\odot b)\) is an ordinary
qubit POVM by (4) (its effects are positive and sum to the identity).
Use these two measurements on a singlet with
\(\varepsilon_i=-\operatorname{sgn}c_i\) as before. Their
measured diagonal entries are \(c_i\).
If at most two \(d_i\) are nonzero, (6) gives \(J(d)=\sum_i d_i\),
and taking \(a=b=(\sqrt{d_i})_i\) produces two PS measurements
under the same condition, including \(d=0\).

For white noise in Section 4, \(d_i=v r_i^2\), so the one-PS critical
visibility is \(v_{\rm one}=1/J((r_i^2)_i)\), while
\(v_{\rm both}=1/g(r)^2\) is the two-PS threshold.
For all \(r_i>0\), \(v_{\rm both}<v_{\rm one}<1\).
Indeed \(g(x)>\|x\|_2\) holds for every all-positive \(x\):
\(x/g(x)\) is a convex mixture of at least two distinct unit
two-support atoms, and the Euclidean norm is strictly convex on
distinct unit vectors. At the two-PS boundary put \(a=b=r/g(r)\);
the first vector has \(g(a)=1\) while the second has Euclidean
norm strictly less than one. Increasing the second by a sufficiently
small positive scalar factor therefore increases visibility with
a one-PS realization. Finally \(v_{\rm one}<1\), since a one-PS
realization at \(v=1\) would by the above exact factorization
give \(1=\sum_i a_i b_i\le\|a\|_2\|b\|_2<1\).
The isotropic SIC example has \(v_{\rm one}=\sqrt{2/3}\)
and \(v_{\rm both}=2/3\). In particular the two thresholds are
not interchangeable, even for the regular tetrahedron.
