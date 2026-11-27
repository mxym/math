# Gaussian smoothing on the two-prime cyclotomic flow torus

**Scope.** This is a distribution theorem about a spherical Gaussian
reduced modulo one Euclidean lattice. It computes its exact total
variation from Haar and its pointwise flatness across the transition.
There are no learning samples, secrets, encryption protocols, or
cryptanalytic procedures in the model. All widths here are in explicitly
unscaled Euclidean units.

For integers \(p,q\ge2\), let \(E\) be the real space of \(p\times q\)
matrices whose row and column sums vanish, and let \(L=E\cap\mathbb Z^{p\times q}\).
Thus \(L=A_{p-1}\otimes A_{q-1}\), the integral flow lattice of
\(K_{p,q}\) with ordinary Euclidean edge lengths. Let \(\mathcal P_t\)
be the centered spherical Gaussian on \(E\), reduced modulo \(L^*\),
with real-coordinate covariance \(t/(2\pi^2)\) times the identity.
Here \(t=\pi s^2\) for the Gaussian width \(s\) of
\(e^{-\pi\|\cdot\|^2/s^2}\); thus its torus Fourier coefficients are
\(e^{-t\|a\|^2}\) for \(a\in L\). Write \(U\) for probability Haar.
The pointwise deviation is
\[
    \left\|d\mathcal P_t/dU-1\right\|_\infty
       =\Theta_L(t)-1,\qquad \Theta_L(t)=\sum_{a\in L}e^{-t\|a\|^2},
\]
by positivity of the Fourier coefficients.

For **distinct prime** \(p,q\), the canonical codifferent of
\(\mathbb Q(\zeta_{pq})\) is isometric to \(L/\sqrt{pq}\).
Consequently the canonical ring of integers is \( \sqrt{pq}\,L^*\).
Multiply the width \(s\) in this note by \(\sqrt{pq}\) to express
the same result on the canonical integer-ring torus. To verify the
identifications, in a prime conductor \(p\) the trace Gram matrix
of the power basis has diagonal \(p-1\) and off-diagonal \(-1\),
so that the ring lattice is \(\sqrt p\,A_{p-1}^*\) and its dual
\(A_{p-1}/\sqrt p\). For coprime \(p,q\), embeddings and the integral
powerful basis factor by the Chinese remainder theorem, so the
canonical Gram matrix is the tensor of the two prime Gram matrices.
This is the standard cyclotomic tensor identification of the
[LPR Toolkit, Proposition 2.13 and (2.6)–(2.7)](https://web.eecs.umich.edu/~cpeikert/pubs/toolkit.pdf).

## 1. Statements

If \(p,q\to\infty\), with no condition on their ratio:

* If \(y=pq e^{-2t}\) tends to \(y_0\in[0,1)\), then
  \[
       \Theta_L(t)\longrightarrow \frac{e^{-y_0}}{1-y_0}.
       \tag{1}
  \]
  If \(y\to y_0\in[1,\infty]\), then \(\Theta_L(t)\to\infty\).
* If \(x=\sqrt{pq}\,e^{-2t}\) tends to \(x_0\in[0,1)\), then
  \[
  d_{\rm TV}(\mathcal P_t,U)
    \longrightarrow 2\Phi\!\left(\frac{\sqrt{-\log(1-x_0^2)-x_0^2}}2\right)-1 .
    \tag{2}
  \]
  If \(x\to x_0\in[1,\infty]\), then \(d_{\rm TV}\to1\).
  Here \(\Phi\) is the standard normal distribution function.

In particular, (1) gives the smoothing width to additive \(o(1)\)
in \(t\): at any fixed \(\epsilon>0\), let \(y_\epsilon\in(0,1)\)
be the unique solution \(e^{-y_\epsilon}/(1-y_\epsilon)=1+\epsilon\).
Then the squared width is
\((\log(pq)-\log y_\epsilon)/(2\pi)+o(1)\) in the above units.
The TV transition lies instead at \(t=\log(pq)/4+O(1)\).
These are not first-shell estimates: every fixed simple even
cycle length remains visible.

If **\(p\) is fixed** and \(q\to\infty\), there is a different
finite-dimensional phase average. For \(u\in\mathbb T^p\), write
\(F_p(u)=|\sum_{i=1}^p e^{2\pi i u_i}|^2-p\).
Then when \(q e^{-2t}\to y_0<\infty\),
\[
           \Theta_L(t)\ \longrightarrow\
                \int_{\mathbb T^p} e^{y_0 F_p(u)}\,du ;
    \tag{3}
\]
it diverges if \(q e^{-2t}\to\infty\).
Let \(Z_{ij}\) for \(1\le i<j\le p\) be independent standard proper
complex Gaussians, meaning real and imaginary variances \(1/2\).
For \(\sqrt q\,e^{-2t}\to\tau<\infty\), the TV limit is
\[
 \begin{split}
  &1-\mathbb E\min\{\mathcal H_{\tau,p}(Z),1\},\\
  &\mathcal H_{\tau,p}(Z)
     =\int_{\mathbb T^p}
        \exp\!\left(2\tau\,\operatorname{Re}
             \sum_{i<j} e^{2\pi i(u_i-u_j)} Z_{ij}
                          -\binom p2\tau^2\right)\,du .
 \end{split} \tag{4}
\]
The limit is 1 if \(\sqrt q\,e^{-2t}\to\infty\).
The \(p=2\) phase average is the single common-angle form, but (4)
includes the dependent phases for every fixed \(p\).
Throughout, integration on a unit torus uses probability Haar.

For context, bipartite cycle statistics and likelihood expansions
are used in different Gaussian matrix experiments by
[Banerjee–Ma](https://arxiv.org/abs/1804.00567). Our Fourier coefficients
are instead the Gaussian mass of all **integer** balanced flows.
The proof combines a full flow-sum bound with a cycle joint CLT over
unit-circle phases and does not assume a bounded aspect ratio.
The torus problem and the sharp constants below are not consequences
of matrix eigenvalue CLTs.

## 2. Pointwise limit by decomposing integral flows

Orient \(K_{p,q}\) from the first side to the second as a reference.
Each signed integral \(a\in L\) is a circulation; orient an edge by
the sign of \(a_e\) and give it multiplicity \(|a_e|\).
Flow conservation gives a decomposition into directed simple cycles
with no cancellation on any occupied edge: follow directed edges
until a vertex repeats, remove the resulting simple cycle, and
iterate on the remaining balanced multigraph. A two-edge cycle
is impossible because both signs cannot occur on the same edge.
The number of directed simple cycles of length \(2\ell\), including
both orientations, is
\[
      M_\ell=\frac{(p)_\ell(q)_\ell}{\ell}\qquad
              (2\le\ell\le\min(p,q)).
 \tag{5}
\]
This counts ordered alternating visits starting on the first side
and divides by the \(\ell\) choices of starting vertex.
In particular \(M_2=2\binom p2\binom q2\).

Since \(\|a\|^2\ge\|a\|_1\), at least one cycle multiset represents
each \(a\) with activity \(e^{-t\|a\|_1}\) at least as large as
the desired weight. Therefore
\[
 \Theta_L(t)\le
        \prod_{\text{directed simple }c}(1-e^{-t|c|})^{-1}.
 \tag{6}
\]
A single multiset has a unique flow sum, so choosing one admissible
decomposition per flow does not overcount in this upper bound.
If \(y\to y_0<1\), the logarithm of (6) tends to
\(\sum_{\ell\ge2}y_0^\ell/\ell=-\log(1-y_0)-y_0\):
the first-order terms converge by (5) and a uniform geometric
majorant, and the remainder is bounded by a constant times
\(\max_c e^{-t|c|}\) times their bounded sum, tending to zero.

For a matching lower bound restrict to collections of vertex-disjoint
directed simple cycles, keeping at most a fixed number of cycles
and a fixed maximum length. A collection gives a distinct flow
because its support components determine its cycles, and its
energy \(\|a\|^2\) is the sum of its lengths. For any fixed length
multiplicities \(m_\ell\), as both sides grow the count of such
collections is asymptotic to \(\prod_\ell M_\ell^{m_\ell}/m_\ell!\):
successively selecting cycles excludes an \(O(1/p+1/q)\) fraction
at each step, by vertex symmetry. Their limiting total weight
is \(\prod_\ell(y_0^\ell/\ell)^{m_\ell}/m_\ell!\).
Increasing the finite cutoffs proves (1). If \(y\to y_0\ge1\)
or \(y\to\infty\), even just individual directed cycles of fixed
bounded lengths give a lower bound tending to the corresponding
partial series, which can be made arbitrarily large.

## 3. Gaussian cycle limits on the quotient torus

Let \(\Pi\) be orthogonal projection from the ambient matrix space
to \(E\). Its image \(\Pi\mathbb Z^{p\times q}\) is a discrete lattice
because \(E\) is rational, and its dual in \(E\) is \(L\) by testing
integer coordinate vectors. Thus it is \(L^*\).
The map \(\mathbb T^{pq}\to E/L^*\) induced by \(\Pi\) sends
ambient Haar to \(U\). It sends an ambient spherical Gaussian
with the same covariance (first reduced modulo \(\mathbb Z^{pq}\))
to \(\mathcal P_t\), since the orthogonal projection of a spherical
Gaussian onto \(E\) remains spherical there. All circuit characters
are invariant by this quotient; they lie in \(L\).

Use complex phases \(W_e=e^{2\pi i Y_e}\) for the independent
ambient coordinates. Under \(U\) these are iid Haar circle phases.
Under the Gaussian pushforward they are independent with
\(\mathbb E W_e^k=e^{-tk^2}\) for integer \(k\).
For a directed simple cycle \(c\) let
\(\chi_c(W)=\prod_{e\in c}W_e^{\pm1}\), with signs from its orientation.
Define the real variable
\[
   S_\ell=(pq)^{-\ell/2}
           \sum_{\substack{\text{directed simple } c\\ |c|=2\ell}}
                               \chi_c(W)
\]
(the reverse orientation contributes the conjugate).
If \(x=\sqrt{pq}\,e^{-2t}\to x_0<\infty\) and both sides grow, then
for any fixed finite set of lengths the \(S_\ell\) converge jointly
to independent real Gaussian variables of variance \(1/\ell\),
with means \(0\) under Haar and \(x_0^\ell/\ell\) under \(\mathcal P_t\).

Here is a joint moment proof. First replace the phases by independent
centered variables \(V_e\), allowing conjugates in place of negative
exponents; suppose \(|V_e|\le2\), \(\mathbb E|V_e|^2\to1\),
\(\mathbb E V_e^2\to0\), and the same law for all edges at each
dimension. Consider a product of cycle sums with lengths
\(2\ell_1,\ldots,2\ell_d\), and put \(B=\sum_i\ell_i\).
A nonvanishing term must use each distinct edge at least twice.
The union has at most \(B\) edges, and degree at least 2 at every
vertex. In either side it has at most \(B/2\) vertices.
For each of the finitely many unlabeled union patterns, after
dividing by \((pq)^{B/2}\) its contribution is bounded
by a constant times \(p^{v_p-B/2}q^{v_q-B/2}\). It vanishes unless
both exponents are zero. Equality requires exactly \(B\) edges
of multiplicity two and degree two at every vertex, hence disjoint
cycle components, each traversed by two of the original cycles.
Equal orientations give vanishing moments by the assumption
\(\mathbb E V_e^2\to0\). Opposite orientations pair by (5) with
variance \(1/\ell\). These are precisely the Wick pairings.
Moment determinacy of the Gaussian limits gives the claim in
the centered case, including joint convergence. In Haar take
\(V_e=W_e\).

For the Gaussian case take \(V_e=W_e-a\) with \(a=e^{-t}\);
then \(\mathbb E|V_e|^2=1-a^2\) and
\(\mathbb E V_e^2=a^4-a^2\). Expand each cycle product.
The term with no centered edges gives the deterministic shift
\(M_\ell a^{2\ell}/(pq)^{\ell/2}\to x_0^\ell/\ell\).
All intermediate terms vanish in \(L^2\) at every fixed length.
Indeed a nonempty proper subset of a simple cycle is a union of
paths. If it has \(j\) centered edges and \(v_p,v_q\) incident
vertices, a term in its second moment must have the **same**
centered edge support in both factors or a centered variable
occurs only once. There are \(O(p^{v_p}q^{v_q})\) placements and
at most \(O(p^{\ell-v_p}q^{\ell-v_q})\) completions of each
factor. The weight is \(a^{2(2\ell-j)}\) in the second moment.
After normalization, using \(a^2=O((pq)^{-1/2})\), the bound
is \(O(p^{j/2-v_p}q^{j/2-v_q})=o(1)\):
each side's incident vertex count is at least \(j/2\)
by maximum degree two, and at least one inequality is strict
because the support contains a path. Only finitely many
patterns occur. This completes the Gaussian cycle limit.

## 4. Saturation of the likelihood second moment

On \(E/L^*\) write \(D_t=d\mathcal P_t/dU\). Parseval and (1) give
for \(0<x_0<1\)
\[
      \mathbb E_U D_t^2=\Theta_L(2t)\longrightarrow
      e^{V},\qquad V=\sum_{\ell\ge2}\frac{x_0^{2\ell}}{\ell}
                        =-\log(1-x_0^2)-x_0^2 .
 \tag{7}
\]
For fixed \(K\ge2\) let \(Z_K=\sum_{\ell=2}^K x_0^\ell S_\ell\)
and \(V_K=\sum_{\ell=2}^K x_0^{2\ell}/\ell\).
The two cycle limits give \(Z_K\Rightarrow N(0,V_K)\) under \(U\)
and \(Z_K\Rightarrow N(V_K,V_K)\) under \(\mathcal P_t\).
Let \(g(z)=e^{z-V_K/2}\) and \(g_A=\min(A,g)\).
Testing with the bounded \(g_A\) in both laws and using (7),
\[
 \lim \mathbb E_U(D_t-g_A(Z_K))^2
  = e^{V}-e^{V_K}
       +\mathbb E_{N(0,V_K)}(g-g_A)^2 .
\]
First \(A\to\infty\) and then \(K\to\infty\) make this zero.
Thus the half-\(L^1\) norm of \(D_t-1\) tends to the TV of
the shifted normal experiment with variance \(V\), namely (2).
This argument uses limiting likelihood overlap, not a test lower
bound alone. If \(x_0=0\), (1)–(7) give \(\mathbb E_U D_t^2\to1\).
If \(x_0\ge1\), add Gaussian variance so that any prescribed
\(x'<1\) becomes the new value of \(x\). TV contracts under this
convolution, so the original limiting lower bound is at least
the right side of (2) evaluated at \(x'\). Let \(x'\uparrow1\)
to get the limit one.

## 5. A fixed number of rows

For fixed \(p\), view a flow as \(q\) columns \(z_j\in A_{p-1}\)
with \(\sum_j z_j=0\). The coefficient extraction by Haar is
\[
 \Theta_L(t)=\int_{\mathbb T^p}
     \left(\sum_{z\in A_{p-1}} a^{\|z\|^2}e^{2\pi i z\cdot u}\right)^q du,
       \qquad a=e^{-t}.
\]
The inner function is \(1+a^2 F_p(u)+O_p(a^4)\) uniformly:
the norm-2 vectors are \(e_i-e_j\), and the remaining nonzero
squared norms are at least 4. Absolute convergence bounds the
uniform tail at order \(a^4\). This proves (3) for finite \(y_0\).
As \(y_0\to\infty\) the limit in (3) diverges because \(F_p>0\)
on an open set around zero, so monotonicity also covers that endpoint.

For TV, the kernel of the projection
\(\mathbb T^{pq}\to E/L^*\) is the image of the row and column phases
\(Y_{ij}\mapsto Y_{ij}+u_i+v_j\): this is exactly the image of
\(E^\perp\) modulo integers. The Gaussian density on the quotient
lifts to the average over these phases of the ambient wrapped
Gaussian product; under ambient Haar this lift gives the same
TV to Haar. After integration of the independent \(v_j\), the
likelihood is an integral over \(u\) of a product of \(q\) factors.
For \(Y_{\cdot j}\) the ambient Haar column, its factor is
\[
       1+a^2 F_p(Y_{\cdot j}+u)+R_j(u).
\]
The remainder \(R_j\) has the nonzero balanced Fourier modes
of squared norm at least 4, with absolute coefficient sum
\(O_p(a^4)\). For every such mode the sum of its characters over
the \(q\) independent columns has expected absolute value at most
\(\sqrt q\) by its second moment. Hence
\(\mathbb E\sup_u|\sum_jR_j(u)|=O_p(\sqrt q\,a^4)=o(1)\) in
the finite-\(\tau\) window. Also
\(q^{-1}\sum_jF_p(Y_{\cdot j}+u)^2\to p(p-1)\) uniformly
in probability: flat Haar averages annihilate every nonconstant
term of this finite trigonometric polynomial, and its constant term
is the number \(p(p-1)\) of roots by character orthogonality.
Expanding the product logarithm, the uniform cubic error is
\(O_p(q a^6)=o(1)\). Its linear part is
\[
     2\sqrt q\,a^2\operatorname{Re}
          \sum_{i<j} e^{2\pi i(u_i-u_j)}
           \left(q^{-1/2}\sum_{h=1}^q
             e^{2\pi i(Y_{ih}-Y_{jh})}\right).
\]
By the multivariate CLT and character orthogonality, the variables in
parentheses converge jointly to the independent \(Z_{ij}\) in (4).
The quadratic term of the log is \(-\binom p2\tau^2+o_{\mathbb P}(1)\).
Uniformity of the error and the continuous mapping theorem give
\(\mathcal H_{\tau,p}(Z)\) as the law of the limiting likelihood
under Haar. The overlap formula \(1-\mathbb E\min(D_t,1)\) now
proves (4) because the integrand is bounded. For fixed \(Z\),
\(\mathcal H_{\tau,p}(Z)\to0\) as \(\tau\to\infty\), since its log
is at most \(2\tau\sum_{i<j}|Z_{ij}|-\binom p2\tau^2\).
As before convolution monotonicity proves the endpoint with
diverging actual \(\sqrt q\,a^2\).

**Replay.** Run `node verify-bipartite-flow-smoothing.js` for
exact small-flow and oriented-cycle identities, and deterministic
checks of the Fourier and finite-phase normalizations. It is
a mathematical replay on synthetic examples, not a numerical
premise of the limits.
