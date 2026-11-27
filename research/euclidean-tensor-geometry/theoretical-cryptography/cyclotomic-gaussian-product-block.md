# Exact Gaussian comparison for a block of cyclotomic product coefficients

**Scope.** This is a positive statistical approximation and a matching limit
for two independent continuous Gaussian ring elements, with no hidden signal
or public samples. It addresses a joint-distribution question suggested by
the deterministic norm expansion in [Lyubashevsky–Peikert–Regev, Toolkit
§2.5.2](https://web.eecs.umich.edu/~cpeikert/pubs/toolkit.pdf) and by its
analysis of noise under multiplication. Neither a statement about actual
errors after any protocol operation, nor a change to a Ring-LWE reduction
or a new computational procedure, is implied. In particular, continuous
independent inputs and the consecutive coefficient block are hypotheses.

Let \(d\to\infty\) through powers of two, \(m=d/2\), and consider the real
algebra \(\mathbb R[Y]/(Y^d+1)\) with the coefficient basis. Let \(A_0,B_0\)
be independent ring elements whose \(d\) coefficients are independent
\(N(0,1)\) variables. Put \(C=A_0B_0/\sqrt d\) using the ring product;
write \(P_{d,k}\) for the law of its first \(k\) coefficients, \(Q_k=N(0,I_k)\).
For every sequence \(1\le k\le d\) with
\[
       k/d^{2/3}\ \longrightarrow\ \gamma\in[0,\infty],
\]
one has
\[
 \boxed{\quad
 d_{\rm TV}(P_{d,k},Q_k)
 \ \longrightarrow\
 2\Phi\!\left(\frac{\gamma^{3/2}}{2\sqrt3}\right)-1 .
 \quad}
 \tag{1}
\]
Here \(\Phi\) is the standard normal distribution function and the right
side is 1 at \(\gamma=\infty\). Each coefficient always has variance one;
the critical law is genuinely joint. Canonical and coefficient metrics
are proportional for these rings. Thus using spherical Gaussians in the
canonical metric instead only requires rescaling the product to variance one.

## 1. Conditional Toeplitz covariance

For finite \(\gamma\) eventually \(k\le m\); use that assumption until the
last paragraph. Set \(\theta_j=(2j+1)\pi/(2m)\), \(0\le j<m\).
Evaluation at \(e^{i\theta_j}\), divided by \(\sqrt m\), and separated
into real and imaginary parts, is an orthogonal real transform on the
coefficient space. For example, evaluation at all \(d\) roots divided
by \(\sqrt d\) is unitary, and the evaluations pair by conjugation.
The normalization \(1/\sqrt d\) in the product therefore makes its
transformed slot the product of two independent standard complex pairs
(each with real-coordinate variances 1) divided by \(\sqrt2\).
Conditional on the first factor, the slots are independent two-coordinate
normal variables, each with covariance \(W_j I_2\) where the \(W_j\)
are independent exponential variables of mean one. The inverse transform
restricted to the observed coordinates gives
\[
 X\mid A\ \sim N(0,I_k+A),\quad
 A=\sum_{j=0}^{m-1}\delta_j P_j,\quad
 \delta_j=W_j-1,\quad
 (P_j)_{i\ell}=\frac1m\cos((i-\ell)\theta_j)
 \quad(0\le i,\ell<k).
 \tag{2}
\]
In particular \(P_j\succeq0\), \(\operatorname{tr}P_j=w=k/m\),
\(\sum_jP_j=I_k\), and \(P_j^2\preceq wP_j\).
Put \(A_{i\ell}=a_{|i-\ell|}\). Dependence across observed coefficients appears in their shared random
diagonals. Exact cosine
orthogonality for \(0\le h,\ell<k\le m\) gives
\[
 a_\ell=\frac1m\sum_j\delta_j\cos(\ell\theta_j),\qquad
 \mathbb E a_h a_\ell = 1_{\{h=\ell\}}v_\ell,\quad
 v_0=1/m,\quad v_\ell=1/(2m)\quad(\ell>0).
 \tag{3}
\]
To verify orthogonality, the sum of \(\cos(s\theta_j)\) is zero for every
nonzero integer \(s\) with \(|s|<2m\): odd \(s\) cancel under
\(\theta_j\mapsto\pi-\theta_j\); for even \(s\) use the geometric sum.
Expand \(\cos(h\theta_j)\cos(\ell\theta_j)\) as the half sum of the cosines
at \(h-\ell\) and \(h+\ell\).

Here are two estimates used below. For any fixed \(p>0\), when
\(k=O(m^{2/3})\),
\[
 \mathbb E\|A\|_{\rm op}^{p}
   \le C_p(w\log(2m))^{p/2},\qquad
 \Pr(\|A\|_{\rm op}>\eta)=o(1),\quad
 \eta=C_0\sqrt{w\log(2m)}
 \tag{4}
\]
for sufficiently large absolute \(C_0\), and
\[
 \mathbb E\|A\|_F^2 \le k^2/m,\qquad
 \operatorname{Var}(\|A\|_F^2)\le Ck^3/m^2 .
 \tag{5}
\]
For (4), the Toeplitz quadratic form is bounded by the supremum of
the trigonometric symbol \(g(t)=a_0+2\sum_{\ell=1}^{k-1}a_\ell\cos(\ell t)\),
by integration against the squared modulus of the input polynomial.
At each fixed \(t\), \(g(t)=\sum_j c_j(t)\delta_j\), with
\(\max|c_j|\le2w\) and \(\sum c_j^2\le2w\) by (3). The exact centered
exponential moment formula \(\log\mathbb E e^{x\delta}=-x-\log(1-x)
\le Cx^2\) for \(|x|\le1/2\) yields the two-sided tail
\(2\exp[-c\min(u^2/w,u/w)]\).
Each Fourier coefficient of \(g\) is at most \(\|g\|_\infty\) in
modulus, so \(\|g'\|_\infty\le k(k-1)\|g\|_\infty\). A grid of \(O(k^2)\)
points bounds \(\|g\|_\infty\) by twice the grid maximum. A union bound
and integration of the tail at this grid give (4). Explicitly, if
\(u=t\eta\), \(t\ge1\), then eventually \(\eta<1\) and the tail
exponent is at least \(c t\eta^2/w\). The union factor \(O(k^2)\) is
absorbed by taking \(C_0\) large, since \(w\log(2m)\to0\).

For (5), set \(b_0=k,\ b_\ell=2(k-\ell)\) for \(1\le \ell<k\);
then \(\|A\|_F^2=\sum_\ell b_\ell a_\ell^2\) and its expectation is
\(k(k+1)/(2m)\). We use the following elementary rule several times:
if the components of \(\delta\) are independent, centered, variance one,
and have bounded fourth moments, then
\(\operatorname{Var}(\delta^\mathsf T M\delta)\le C\|M\|_F^2\)
for real symmetric \(M\). Expansion proves it because centered
diagonal terms are independent and unmatched factors at distinct
indices have zero expectation. If \(a=V\delta\), then
\(VV^\mathsf T=\operatorname{diag}(v_\ell)\) by (3); in particular
\(\|V^\mathsf T H V\|_F^2\le m^{-2}\|H\|_F^2\) for symmetric \(H\).
Use \(H=\operatorname{diag}(b_\ell)\) for (5).

## 2. Truncated second moment of the overlap

All limits in this section allow \(k=O(m^{2/3})\). Take the event
\[
 \mathcal E(A)=\{\|A\|_{\rm op}\le\eta,\ \|A\|_F^2\le Rk^2/m\}.
\]
In the positive critical regime \(k^{3}/m^2\to c\in(0,\infty)\) use
a sufficiently large fixed \(R\), for which (5) gives
\(\Pr(\mathcal E)\to1\) because \(k\to\infty\). In the subcritical
regime choose \(R\to\infty\) slowly with \(R k^{3}/m^2\to0\);
Markov's inequality suffices in (5). Write \(\widetilde P\) for the law
conditioned on \(\mathcal E(A)\). Its distance from \(P_{d,k}\) is at most
\(\Pr(\mathcal E^c)\). If \(B\) is an independent copy of \(A\),
completed Gaussian integration gives
\[
 \mathbb E_{Q_k}\left(\frac{d\widetilde P}{dQ_k}\right)^2
    =\mathbb E\big[D(A,B)\mid \mathcal E(A),\mathcal E(B)\big],
 \qquad D(A,B)=\det(I-AB)^{-1/2}.
 \tag{6}
\]
Indeed the integrated Gaussian precision is
\((I+A)^{-1}+(I+B)^{-1}-I\), which becomes \(I-AB\) on
left multiplication by \(I+A\) and right multiplication by \(I+B\).
It is positive definite under the truncation for large \(m\).
No finiteness assertion for the **untruncated** second moment is needed.
On this event the log-determinant power series is valid with the
following real trace expansion:
\[
 \log D=\tfrac12\operatorname{tr}AB+
         \tfrac14\operatorname{tr}(ABAB)+
         O(\eta^2\|AB\|_F^2).
 \tag{7}
\]
For \(\ell\ge2\),
\(|\operatorname{tr}(AB)^\ell|\le\|AB\|_F^2\|AB\|_{\rm op}^{\ell-2}\),
by the trace-norm bound on a product of two Frobenius factors.
Also
\[
 \mathbb E\|AB\|_F^2=\operatorname{tr}((\mathbb EA^2)^2)
       \le kw^2=k^3/m^2,\qquad
 \mathbb EA^2=\sum_jP_j^2\preceq wI .
\]

**Uniform integrability.** An exponentially small bad-event tail is
needed here; convergence in probability of the remainder alone would
not prove (6)'s limit. We give details. Fix constants \(l\in\mathbb R\)
and \(c>0\); for fixed \(A\) on its good event set
\(f=\exp(l\operatorname{tr}AB+c\|AB\|_F^2)\).
For an independent \(k\times k\) matrix \(H\) of standard normal
entries use Gaussian integration to write
\[
 f=\mathbb E_H e^{\sum_j\delta'_j\,\xi_j(H)},\qquad
 \xi_j=l\operatorname{tr}(AP_j)+\sqrt{2c}\langle H,AP_j\rangle_F ,
\]
where \(B=\sum_j\delta'_jP_j\). Split the \(H\) integral where
\(\max_j|\xi_j|\le1/2\) and its complement. On its good part, drop
\(1_{\mathcal E(B)}\), integrate the independent exponentials, and
bound that expectation by \(\exp(C\sum_j\xi_j^2)\). The deterministic
squared terms sum to at most \(Cw\|A\|_F^2\).
For the Gaussian vector
\((\langle H,AP_j\rangle_F)_j\) the covariance has trace at most
\(w\|A\|_F^2\) from \(P_j^2\preceq wP_j\), and operator norm at most
\(w\|A\|_{\rm op}^2\). For the latter bound, for each deterministic \(H\)
apply
\[
 \sum_j|\operatorname{tr}(P_j M)|^2\le w\|M\|_F^2,
 \qquad M=H^\mathsf T A.
\]
This inequality follows from Frobenius Cauchy–Schwarz against
\(P_j^{1/2}\) and \(M P_j^{1/2}\), followed by \(\sum_jP_j=I_k\).
The Gaussian quadratic exponential, integrated over all \(H\), is
therefore at most \(\exp(C'w\|A\|_F^2)\): diagonalize its covariance
and use \(-\log(1-x)\le2x\) at small \(x\). This gives a uniform
bound on the good part since \(w\|A\|_F^2\le Rk^3/m^2=O(1)\).

On the bad part, keep \(B\) fixed on its good event and complete the
square in \(H\). It costs the outside factor \(f\) and replaces
\(H\) by \(H+\sqrt{2c}\,AB\) in the bad indicator. The means of the
shifted \(\xi_j\) are bounded in modulus by
\(C(w\eta+w\eta^3)=o(1)\), because
\(|\langle AB,AP_j\rangle|\le w\|B\|_{\rm op}\|A\|_{\rm op}^2\).
Each variance is \(O(w^2\eta^2)\), since \(\|P_j\|_F\le w\).
A Gaussian tail and union bound give \(2m\exp[-c'/(w^2\eta^2)]\).
The outside factor is at most \(\exp(Ck\eta^2)\). Their product is
\(o(1)\) uniformly: \(k\eta^2=O(m^{1/3}\log(2m))\) while
\((w^2\eta^2)^{-1}\gtrsim m/\log(2m)\).
We have proved
\[
 \mathbb E[1_{\mathcal E(B)} f\mid A]
        \le \exp(C'Rk^3/m^2)+o(1)
        \quad\text{on }\mathcal E(A).
 \tag{8}
\]
In particular any fixed power of \(D\) has bounded conditional
expectation by (7) and (8), hence \(D\) is uniformly integrable there.

## 3. The two overlap terms

Define the additive rectangles and their number by
\[
 \mathcal R_k=\{(i,j,h,\ell):0\le i<j<h<\ell<k,\ i+\ell=j+h\},
 \qquad N=|\mathcal R_k| .
\]
Their gaps are \(u,v,u\) with \(u,v\ge1\). Hence
\(N=\sum_{2u+v<k}(k-2u-v)= k^3/12+O(k^2)\) by summing first in \(v\)
and then the squares in \(u\). Write \(V_k=N/m^2\).

Let \(T_1=\operatorname{tr}AB\). Conditional on \(A\) this is
\(\sum_j\delta'_j\,\operatorname{tr}(AP_j)\), with variance
\(\sum_\ell b_\ell^2v_\ell a_\ell^2\) by (3), using the weights
\(b_\ell\) from (5). The mean of that conditional variance is
\[
 \sum_\ell b_\ell^2v_\ell^2
        = k^2/m^2+\sum_{j=1}^{k-1}j^2/m^2=4V_k+O(k^2/m^2).
\]
Its variance is \(O(k^5/m^4)=o(1)\) by the quadratic-form rule in §1.
The maximum coefficient \(|\operatorname{tr}(AP_j)|\le w\|A\|_{\rm op}\)
vanishes in probability. Expand the centered exponential
characteristic function conditionally, with third-order error
bounded at fixed frequency by a constant times the maximum coefficient
times the sum of squares. This yields \(T_1\Rightarrow N(0,4V)\)
if \(V_k\to V>0\). If \(V_k\to0\), its unconditional second moment
already gives \(T_1\to0\) in probability.

For \(T_2=\operatorname{tr}(ABAB)\), expand four entries as
\(\sum_{i,j,h,\ell} A_{ij}B_{jh}A_{h\ell}B_{\ell i}\).
By (3), nonzero expectations require
\(|i-j|=|h-\ell|\) and \(|j-h|=|\ell-i|\). For distinct indices these
are equivalent to \(i+h=j+\ell\): on the closed path all matching
steps must be opposite (both matching signs equal and positive would
force a repeated vertex; a lone positive sign would force a zero
step). Thus there are \(8N\) ordered distinct cases, each of weight
\(1/(4m^2)\). Repeated-index cases number \(O(k^2)\): adjacent
repetition forces its opposite, and an opposite repetition forces
the other pair equal or one vertex determined by the other two.
It follows that
\(\mathbb E T_2=2V_k+O(k^2/m^2)\).

In fact \(\operatorname{Var}(T_2)=o(1)\). For one exponential variable
\(W\), \(\operatorname{Var}h(W)\le4\mathbb E|h'(W)|^2\):
subtract \(h(0)\), write \(h(x)-h(0)=\int_0^x h'(s)ds\),
use weighted Cauchy–Schwarz with weights \(e^{s/2},e^{-s/2}\), and
integrate against \(e^{-x}\,dx\). Indeed swapping the resulting integrals
gives exactly the constant 4. The same inequality holds after shifting
by one, and tensorizes for independent variables by conditional variance.
Here the gradient components are \(2\operatorname{tr}(P_j B A B)\)
and \(2\operatorname{tr}(P_j A B A)\), respectively. The trace inequality
from §2 shows
\[
 \operatorname{Var}(T_2)
 \le Cw\,\mathbb E(\|BAB\|_F^2+\|ABA\|_F^2)
 \le Cw\,\mathbb E\|A\|_F^2\,\mathbb E\|B\|_{\rm op}^4
 =O(k^5\log^2(2m)/m^4)=o(1),
\]
absorbing the identical term by symmetry. The remainder in (7) tends
to zero in probability. These conclusions persist after conditioning
because the joint good event has probability \(1-o(1)\).
Consequently (6)–(8) give
\[
 \mathbb E_{Q_k}\left(\frac{d\widetilde P}{dQ_k}\right)^2\longrightarrow
       \mathbb E e^{Z/2+V/2}= e^V,\qquad Z\sim N(0,4V),
 \tag{9}
\]
with the same formula \(e^0=1\) in the subcritical regime.
In particular (1) holds for \(\gamma=0\) by the second-moment
bound on TV.

## 4. The critical likelihood is accounted for by quartic rectangles

Assume \(V\in(0,\infty)\) and let
\(F(x)=\sum_{(i,j,h,\ell)\in\mathcal R_k}x_i x_j x_h x_\ell\).
Under \(Q_k\), \(F\) is a fourth Gaussian chaos with mean zero
and variance \(N\), by independence and distinct index sets.
More precisely write \(S\) for its symmetric order-four tensor
(value \(1/4!\) on permutations of a rectangle and zero otherwise),
so \(\|S\|_F^2=N/4!\). Fixing \(r=1,2,3\) indices leaves at most
\(O(k^{3-r})\) compatible ordered tuples in the other \(4-r\)
positions: pick all but one new index, then one of a bounded set of
rectangle signs fixes the last. The flattening of \(S\) into \(r\)
and \(4-r\) modes thus has squared operator norm at most
\(O(k^{3-r}k^{r-1})=O(k^2)\) by its row and column sums.
Each squared contraction norm of the normalized kernel is bounded
by \(O(k^2\|S\|_F^2/N^2)=O(1/k)\). The
[Nualart–Peccati contraction criterion](https://arxiv.org/abs/math/0503598)
for fixed-order Gaussian chaos gives \(F/\sqrt N\Rightarrow N(0,1)\).

Under \(P_{d,k}\) write \(X=(I+A)^{1/2}G\), with \(G\sim Q_k\)
independently. Decompose \(F(X)\) by Gaussian Wick degrees 4, 2, 0
conditional on \(A\), or equivalently expand the generating function
\(\exp(t^\mathsf TX-t^\mathsf T(I+A)t/2)\). The fourth kernel is
\(((I+A)^{1/2})^{\otimes4} S\); its difference from \(S\) is
\(o_{\mathbb P}(\sqrt N)\) in Frobenius norm by (4).
On the operator-norm good event the isometry of degree-four
Gaussian chaos therefore makes the difference in the random degree-four
terms \(o_{\mathbb P}(\sqrt N)\). For degree 2, the kernel before the
ordinary square-root covariance factors is \(6(S\mathbin{\lrcorner} A)\):
the contraction with \(I_k\) vanishes because all indices are distinct.
Each entry of the contracted tensor is a weighted sum of \(O(k)\)
entries \(a_h\) (at most \(O(k)\) completions with two indices fixed).
Each of those entries has fourth-moment norm \(O(m^{-1/2})\),
by expansion in the independent centered exponentials.
Minkowski followed by summing over \(k^2\) choices gives
\[
 \big(\mathbb E\|S\mathbin{\lrcorner} A\|_F^4\big)^{1/2}=O(k^4/m).
\]
The degree-two isometry, Cauchy–Schwarz, and the bounded fourth moment of
\(\|I+A\|_{\rm op}\) from (4) make the variance \(O(k^4/m)=o(N)\).

The degree-zero part is the exact conditional mean
\[
 M(A)=\sum_{2u+v<k} (k-2u-v)
             (a_u^2+a_{u+v}^2+a_{2u+v}a_v).
 \tag{10}
\]
These are the three Wick pairings of gaps \(u,v,u\). By (3),
\(\mathbb E M=N/m\). To bound its variance, write it as a quadratic
form in \(a_1,\ldots,a_{k-1}\). Its diagonal entries are \(O(k^2)\)
(at most \(O(k)\) summands of weight \(O(k)\) at a fixed index),
and the off-diagonal entries are \(O(k)\) (the positions
\(2u+v,v\) determine \(u,v\)). Its squared Frobenius norm is
\(O(k^5)\), giving \(\operatorname{Var}M=O(k^5/m^2)=o(N)\)
by the same quadratic variance rule. We obtain the shifted limit
\[
      F(X)/\sqrt N\Rightarrow N(\sqrt V,1)
 \tag{11}
\]
also under \(\widetilde P\), since conditioning changes TV by \(o(1)\).

This one-dimensional limit gives the full TV, not just a lower bound.
Set \(L_k=d\widetilde P/dQ_k\), \(Z_k=F/\sqrt N\),
\(g(z)=\exp(\sqrt V\,z-V/2)\), and \(g_D=\min(g,D)\).
By bounded continuous testing in the two laws, (9), (11), and the
null CLT,
\[
 \lim \mathbb E_{Q_k}(L_k-g_D(Z_k))^2
       = e^V+\mathbb E_{\rm null}g_D^2-2\mathbb E_{\rm shift}g_D
       =\mathbb E_{\rm null}(g-g_D)^2 ,
\]
where the last expectations are for the two limiting one-dimensional
normal laws. This tends to zero as \(D\to\infty\). Consequently
\(\tfrac12\mathbb E_{Q_k}|L_k-1|\) tends to the variation distance of
\(N(0,1)\) and \(N(\sqrt V,1)\), namely \(2\Phi(\sqrt V/2)-1\).
Since \(V=N/m^2\to\gamma^3/3\), and the conditioning is \(o(1)\)
in TV, this proves (1) at every finite positive \(\gamma\).
For \(\gamma=\infty\), project down to
\(k_0=\lfloor\gamma_0 d^{2/3}\rfloor\) for any fixed \(\gamma_0>0\);
it eventually lies within the observed block. The finite critical
profile is a lower bound by data processing, and tends to one as
\(\gamma_0\to\infty\).

**Replay.** Run `node verify-cyclotomic-gaussian-product-block.js`.
It uses exact rectangle/counting identities and numerical checks of
Fourier normalization, covariances, Wick conditional means, and Gaussian
overlap in generated small dimensions. It does not simulate an
encryption scheme or stand in for the asymptotic proof.
