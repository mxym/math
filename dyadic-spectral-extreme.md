# Extremal Gaussian-padding width in dyadic module embeddings

Let \(d\ge 4\) run through powers of two, and write \(R_d=\mathbb Z[Y]/(Y^d+1)\). Fix positive integers \(m,r\), and let \(F_d\) be an \(m\)-by-\(r\) matrix over \(R_d\). Its coefficients are independent copies of a centered integer Gaussian \(Z_d\), with masses proportional to \(\exp(-a_d z^2)\), where \(a_d>0\) may vary arbitrarily. Let \(v_d=\mathbb E Z_d^2\) be its actual coefficient variance. Give the source and target their canonical Euclidean metrics, counting both embeddings of a complex place in the squared norm. Write \(\mathcal M_d\) for the Euclidean operator norm of multiplication by \(F_d\) on the canonical spaces. Set
\[
 N=d/2,\qquad L=\log N,\qquad
 b_d=L+(m+r-2)\log L-\log(\Gamma(m)\Gamma(r)).
\]

**Theorem.**
1. If \(d\min(1,v_d)/L^2\to\infty\), then
\[
  \Pr\!\left(\frac{\mathcal M_d^2}{d v_d}-b_d\le x\right)\longrightarrow
          \exp(-e^{-x})\qquad(x\in\mathbb R).                              \tag{1}
\]
2. If \(d v_d/L^2\to c\in(0,\infty)\), define a random \(m\)-by-\(r\) matrix \(G\) of independent standard real Gaussians. For a real matrix \(g\), define
\[
 \begin{split}
 \Psi_c(g)&=\mathbb E_{U,V}\exp\left(
    \frac1{\sqrt c}\sum_{a,b}g_{ab}w_{ab}
          -\frac1{4c}\sum_{a,b}w_{ab}^2\right),\\
 &\hspace{10mm}w_{ab}=|U_a|^2|V_b|^2 ,
 \end{split}                                                              \tag{2}
\]
where \(U,V\) are independent uniform unit vectors in \(\mathbb C^m,\mathbb C^r\). Then
\[
 \Pr\!\left(\frac{\mathcal M_d^2}{d v_d}-b_d\le x\right)\longrightarrow
              \mathbb E_G \exp(-e^{-x}\Psi_c(G)).                         \tag{3}
\]
Equivalently this is the law of an independent standard Gumbel plus \(\log\Psi_c(G)\). In the scalar case it is a standard Gumbel plus an independent \(N(-1/(4c),1/c)\) variable. The mixing factor is nonconstant for every \(m,r\): adding the same \(t\) to each entry of \(g\) multiplies it by \(e^{t/\sqrt c}\); the corresponding normal direction in \(G\) is independent of its orthogonal complement. Thus (3) is not a deterministic shift of (1).

**Scope and prior results.** The complex-place block decomposition is the one relevant to the positive Gaussian completion in [Lin, Wang, Zhuang et al., *Hardness of Entropic Module-LWE*, §3.1, Lemma 11 and Theorem 3](https://pure.tudelft.nl/ws/portalfiles/portal/186654080/1-s2.0-S0304397524001683-main.pdf). For a fixed multiplication map \(T\), independent centered real Gaussian input of covariance \(\sigma^2 I\) can be completed by independent Gaussian padding to covariance \(\alpha^2 I\) exactly when \(\alpha\ge\sigma\|T\|\), allowing a degenerate padding Gaussian at equality. This follows from the positive semidefiniteness of \(\alpha^2 I-\sigma^2TT^\top\). The theorem above quantifies this random norm in a fixed-module-shape, growing-field model; it does not extend that paper's hardness theorem, treat growing module shapes, or analyze any cryptosystem.

[Davis–Mikosch, Theorem 2.1 and Lemma 3.4](https://pure.rug.nl/ws/portalfiles/portal/72126009/euclid.aop.1022677270.pdf) established the scalar Gumbel law at ordinary Fourier frequencies for a fixed iid coefficient distribution, using smoothed finite-frequency densities, and [Liu–Shao](https://doi.org/10.1214/09-AOS774) obtained Cramér-type refinements for periodograms. Here the density method is used on fixed-size matrix blocks at the odd-root grid; the coefficient law is triangular. At the critical sparse variance, conditioning on coefficient counts and retaining the fourth cumulant gives (3). Complex Gaussian Wishart eigenvalue densities used below are classical; see [Forrester, §§1–2](https://arxiv.org/abs/1401.2572) for the complex Gaussian product viewpoint including the single-matrix case, or [Chiani, Theorem 3](https://doi.org/10.1016/j.jmva.2014.04.002) for the finite complex-largest-eigenvalue distribution.

## 1. Fourier coordinates and comparison tail

The \(N\) complex places, one out of each conjugate pair, evaluate at \(\exp(i\pi u/d)\) for \(u=1,3,\ldots,d-1\). Under the canonical embedding multiplication is block diagonal, with complex blocks \(F_d(\exp(i\pi u/d))\). Weighting each complex place by \(\sqrt2\) on both domain and codomain leaves the operator norm unchanged. Write \(B_{d,u}\) for the block divided by \(\sqrt{d v_d}\), and \(\mathcal M_d^2/(dv_d)=\max_u\|B_{d,u}\|^2\).

For any fixed \(k\) distinct selected places, take real coordinates \((\sqrt2\operatorname{Re},\sqrt2\operatorname{Im})\) for each matrix entry and place. A real coefficient \(W_i=Z_i/\sqrt{v_d}\) in one entry contributes via the vector
\[
 a_i=\sqrt{2/d}\,(\cos(\pi u_j i/d),\sin(\pi u_j i/d))_{j=1}^k .
\]
These vectors have squared norm \(2k/d\) and \(\sum_{i=0}^{d-1}a_i a_i^\top=I_{2k}\). Indeed the sums and differences of two odd frequencies are even, and the geometric sum over \(i\) vanishes unless the frequency is divisible by \(2d\). The only constant terms are from identical frequencies in a difference. Independent entries give the corresponding identity for the stacked real vector in dimension \(2kmr\).

The Gaussian reference is therefore \(k\) independent complex \(m\)-by-\(r\) matrices \(H\) with iid complex entries of density \(\pi^{-1}e^{-|z|^2}\). For one such matrix,
\[
 \Pr(\|H\|^2>t)\ \sim\ \frac{t^{m+r-2}e^{-t}}{\Gamma(m)\Gamma(r)}.
                                                                           \tag{4}
\]
For completeness put \(p=\min(m,r)\), \(q=\max(m,r)\), and \(a=q-p\). The unordered eigenvalues of the complex Wishart matrix on its \(p\)-dimensional side have density proportional to
\(e^{-\sum_i\lambda_i}\prod_i\lambda_i^{a}\prod_{i<j}(\lambda_i-\lambda_j)^2\) on \([0,\infty)^p\), with integral \(Z_{p,a}=\prod_{j=1}^p\Gamma(j+1)\Gamma(a+j)\). Integrating out all but a large first value \(\lambda_1=z\) gives power \(z^{a+2p-2}\) and factor \(Z_{p-1,a}\) by dominated convergence, since \((1-y/z)^2\le(1+y)^2\) for \(z\ge1,y\ge0\). Intersections with two eigenvalues above \(t\) cost \(e^{-2t}\) times a polynomial: use \(|\lambda_i-\lambda_j|\le(1+\lambda_i)(1+\lambda_j)\). Thus the leading constant is \(p Z_{p-1,a}/Z_{p,a}=1/(\Gamma(p)\Gamma(q))\). The same two-large bound, with a second threshold \(\eta t\) for fixed \(\eta>0\), implies that given \(\|H\|^2>t\),
\[
                 H/\sqrt t\ \Longrightarrow\ U V^* .                    \tag{5}
\]
The first squared singular value divided by \(t\) tends to 1 by (4); all remaining squared singular values divided by \(t\) tend to 0. To justify the directions, apply independent Haar unitary rotations on both sides of \(H\), which preserve its conditional distribution and make the dominant left and right directions independent uniform vectors for any fixed singular values. This proves (5), including rectangular shapes and \(p=1\).

In particular \(N\Pr(\|H\|^2>b_d+x+o(1))\to e^{-x}\).

## 2. A compact-smoothing density argument

Here is a fixed-dimensional tool for the two regimes of the proof. Write \(S\) for a real random vector of covariance \(I_D\), with \(D\) fixed. Write \(K(z)=\log\mathbb E e^{z\cdot S}\) wherever the logarithm below is specified by its local power expansion (use complex bilinear squares for complex \(z\)). Let \(h=L^{-3/4}\), and add an independent \(hV_0\) with \(C^\infty\) density supported in the unit ball before scaling. Suppose uniformly for \(\|t\|\le C\sqrt L\), for every fixed \(C\), that
\[
 \begin{split}
 K(t)&=\|t\|^2/2+P(t)+o(1),\\
 K(t+i w)-K(t)-i w\cdot t &\longrightarrow-\|w\|^2/2
                     \quad\text{uniformly on bounded real }w ,
 \end{split}                                                            \tag{6}
\]
with \(P\) bounded on each such region. Also suppose that under exponential tilt by \(t\), the characteristic function of \(S\) is bounded in magnitude by \(\exp(-c_0\|w\|^2)\) for \(\|w\|\le R\), where \(R\ge c_1 L\) for fixed \(c_0,c_1>0\). The smoothed \(S+hV_0\) then has density
\[
      f(z)=(1+o(1))\,\varphi_D(z)\exp(P(z))\qquad(\|z\|\le C\sqrt L),       \tag{7}
\]
where \(\varphi_D\) is the standard real Gaussian density, uniformly in any parameters for which the preceding conditions hold uniformly. It also has probability \(O(N^{-A})\) outside such a ball for any prescribed \(A\) if \(C\) is large enough. The same tail bound holds without smoothing.

To prove (7), tilt at the real parameter \(t=z\). The tilted smoothing kernel, written in its original rescaled coordinates, has density proportional to \(e^{h t\cdot v}\) times its fixed smooth compact density. Since \(h\|t\|=o(1)\), its Fourier transform is bounded by \(C_M(1+h\|w\|)^{-M}\) for every fixed \(M\), uniformly, by integration by parts. Its logarithmic normalizer is \(O(h\|t\|)=o(1)\). The high-frequency part of the Fourier inversion integral for the tilted smoothed density, \(\|w\|>R\), has absolute integral bounded by \(O_{M,D}(h^{-D}(hR)^{D-M})=o(1)\) for \(M>4D\). The low-frequency integral at \(z\) tends to \((2\pi)^{D/2}\) before the \((2\pi)^{-D}\) Fourier normalization, by (6), the Gaussian envelope and dominated convergence. Undoing the tilt multiplies the tilted density by \(\exp(K(z)+o(1)-\|z\|^2)\), proving (7). For the tail bound, by (6) the log moment generating function is Gaussian to within \(O(1)\) for any fixed multiple of \(\sqrt L\). A union bound over signs of the \(D\) coordinates and a Chernoff bound give the claim by increasing \(C\).

The smoothing is confined to a deterministic distance \(h\). For any fixed set of matrix blocks, their operator norms change by at most a fixed multiple of \(h\): the operator norm is 1-Lipschitz in Frobenius norm, and the real coordinate normalization is fixed. At thresholds of size \(\sqrt{b_d+x}\), this changes the squared thresholds by \(O(\sqrt L h)=o(1)\). Thus all joint exceedance comparisons below transfer by deterministic sandwich, without asking for a small **absolute** approximation error in a probability of order \(N^{-k}\).

## 3. Above the critical sparse scale

Let \(\upsilon=\min(1,v_d)\), \(W=Z_d/\sqrt{v_d}\). Uniformly over all \(a_d>0\) and for some constants \(b,B>0\),
\[
   \mathbb E\left[|W|^4 e^{b\sqrt\upsilon |W|}\right]\le B/\upsilon .
                                                                           \tag{8}
\]
For \(a_d\ge1\), \(v_d\) is comparable, with absolute constants, to \(e^{-a_d}\): bound the normalization above and below by constants and compare the remaining \(z^2\)-weighted series to its \(z=\pm1\) terms. The series for \(\mathbb E[|Z_d|^4 e^{b|Z_d|}]\) is similarly at most \(C_b e^{-a_d}\), by extracting \(e^{-a_d}\) and summing \(|z|^4 e^{-(z^2-1)+b|z|}\) over \(z\ne0\). This proves (8) since \(\sqrt{\upsilon/v_d}\le1\). For \(0<a_d\le1\), the normalization is comparable to \(a_d^{-1/2}\) and \(v_d\) to \(a_d^{-1}\), by Gaussian sums and (for the lower second moment) the integers in \([a_d^{-1/2},2a_d^{-1/2}]\). Absorb the linear exponential into half the Gaussian exponent to obtain (8) in this range.

Symmetry, unit variance and (8) give
\(\log\mathbb E e^{zW}=z^2/2+O(|z|^4/\upsilon)\) for complex \(|z|\le b_0\sqrt\upsilon\) with small absolute \(b_0>0\). Taylor expansion with (8) bounds the exponential's remainder; the transform stays near 1 so the logarithm is the power-series branch. Under a real tilt \(t\) in this range, the variance is at least \(1/2\) and the fourth moment is \(O(1/\upsilon)\) after decreasing \(b_0\). These follow by the same Taylor expansion for the first two derivatives: the first derivative of the transform is \(t+O(|t|^3/\upsilon)\), and its second is \(1+O(t^2/\upsilon)\). In the tilted law, for independent \(W,W'\),
\[
 |\mathbb E_t e^{iwW}|^2
    =1-\mathbb E_t[1-\cos(w(W-W'))]\le 1-c w^2
            \quad(|w|\le b_1\sqrt\upsilon),
\]
using the variance and the fourth-order Taylor bound for the cosine. The constants can be fixed independently of \(d\).

Apply these facts to the independent coefficients and the real stacked vectors \(a_i\) in section 1, including their analogous representation across all entries. The complex log moment expansion sums to
\[
 K(z)=z\cdot z/2+O(\|z\|^4/(d\upsilon)),
\]
since \(\sum_i|a_i\cdot z|^2=\|z\|^2\) and \(\max_i\|a_i\|^2\le 2k/d\). For real tilt \(t=O(\sqrt L)\) the single-coefficient bound also applies to \(a_i\cdot w\) for \(\|w\|\le c_2\sqrt{d\upsilon}\); multiplication over coefficients gives the envelope \(\exp(-c\|w\|^2)\). With \(d\upsilon/L^2\to\infty\), (6) holds with \(P=0\) and \(R/L\to\infty\); all estimates are uniform over the selected distinct frequencies.

Let \(V_d(x)\) count places with \(\|B_{d,u}\|^2>b_d+x\). By (7), (4), the tail bound in section 2 with \(A>k\), and the deterministic smoothing sandwich, the joint exceedance probability for any fixed distinct \(k\)-tuple is \((1+o(1))N^{-k}e^{-kx}\), uniformly over tuples. The factorial moments of \(V_d(x)\) converge to \(e^{-kx}\) for each fixed \(k\). Inclusion–exclusion truncated at adjacent even and odd orders (the Bonferroni bounds) therefore gives \(\Pr(V_d(x)=0)\to \exp(-e^{-x})\). No independence assumption on the original Fourier blocks is required.

## 4. Sparse critical scale: conditioning removes the cross cumulants

Suppose \(d v_d/L^2\to c\in(0,\infty)\). Then \(v_d\to0\), \(a_d\to\infty\), \(\Pr(|Z_d|\ge2)=O(v_d^4)\), and
\[
    p_d:=\Pr(|Z_d|=1)=v_d+O(v_d^4).
\]
These estimates follow by factoring \(e^{-4a_d}\) from the \(z\ge2\) terms and using \(v_d\asymp e^{-a_d}\) as above. Replace all coefficient magnitudes \(\ge2\) by zero. The whole matrix law changes by at most \(dmr\,O(v_d^4)=o(1)\) in total variation. The remaining coefficients have independent signed Bernoulli law, with nonzero probability \(p_d\). Put \(\mu=d p_d\sim cL^2\). Normalizing by \(\sqrt\mu\) instead of \(\sqrt{d v_d}\) changes each squared comparison threshold \(b_d+x\) by \(o(1)\), because \(L|p_d/v_d-1|\to0\).

For every matrix entry condition on its number \(s_{ab}\) of nonzero coefficients. Given these numbers, the positions are uniform sets and the signs are independent. For each entry replace the uniform positions by \(s_{ab}\) independent positions in \(\{0,\ldots,d-1\}\), keeping independent signs for each position draw. The laws can be coupled on the entire field grid with disagreement at most \(\sum_{ab}s_{ab}(s_{ab}-1)/(2d)\) conditionally on the counts: whenever the draws are distinct their unordered set is uniform. This probability averaged over the counts is \(O_{m,r}(\mu^2/d)=o(1)\). It is used only for comparison of the whole maximum's law, not for a relative estimate on rare joint events in the original model.

Set \(g_{ab}=(s_{ab}-\mu)/\sqrt\mu\). Work first in the with-replacement model conditional on any such count vector with \(\max_{ab}|g_{ab}|\le C_0\), for an arbitrary fixed \(C_0\). Consider one entry with count \(s\); after dividing its transform by \(\sqrt s\) and taking the real normalization of section 1, its stacked vector at a fixed \(k\)-tuple is a sum of \(s\) iid copies of
\[
   Y=\sqrt2\,D\,(\cos(\pi u_j J/d),\sin(\pi u_j J/d))_{j=1}^k
\]
divided by \(\sqrt s\). Here \(J\) is uniform over the \(d\) positions and \(D\) is an independent uniform sign. This vector is bounded, symmetric, and of covariance \(I_{2k}\).

Call the selected tuple generic if no sum of four signed chosen odd frequencies is divisible by \(2d\) except when the signed frequencies cancel in pairs of equal indices. There are \(O_k(N^{k-1})\) exceptional distinct tuples: any nontrivial relation gives a nonzero coefficient vector with bounded integer coefficients, and for an index with nonzero coefficient there are at most four solutions modulo \(2d\) after fixing the other indices. For a generic tuple and real \(z=(z_j)_{j=1}^k\) with \(z_j\in\mathbb R^2\), direct fourth-moment averaging gives
\[
 \mathbb E(z\cdot Y)^4
       =\tfrac32\sum_j\|z_j\|^4
                       +6\sum_{j<\ell}\|z_j\|^2\|z_\ell\|^2 .
\]
Indeed the fourth power of a single cosine averages to \(3/8\) and the product of two squared cosines averages to \(1/4\) by the frequency condition; there is an overall factor \((\sqrt2)^4=4\). Subtracting \(3(\sum_j\|z_j\|^2)^2\) leaves fourth cumulant \(-\tfrac32\sum_j\|z_j\|^4\); all cross terms cancel.

Consequently the log moment generating function of the normalized sum is
\[
 K(z)=\tfrac12 z\cdot z-\frac{1}{16s}\sum_j(z_j\cdot z_j)^2
                     +O_k(\|z\|^6/s^2)                                  \tag{9}
\]
uniformly up to \(\|z\|\le C\sqrt L+O(1)\), by the boundedness and symmetry of \(Y\). The formula extends to complex \(z\) by the same series, with bilinear squares. On an exceptional tuple the quartic term is \(\kappa_4(z\cdot Y)/(24s)\), a uniformly bounded homogeneous quartic after division by \(s\) on this region, though not the displayed diagonal quartic. Its change between \(t\) and \(t+iw\) for fixed bounded \(w\) is \(O_k((1+\|t\|)^3/s)=o(1)\) in either case. The remainder is \(O_k(L^3/s^2)=o(1)\). The tilted characteristic envelope holds for \(\|w\|\le c_k\sqrt s\); use the same independent-copy cosine argument in each direction, now with bounded \(Y\), covariance \(I\) within \(o(1)\) under tilt \(t/\sqrt s\), and all directional fourth moments bounded after unit normalization. Since \(s\sim c L^2\) uniformly, sections 2 and (9) apply under the conditional law, both to generic and exceptional tuples.

For a final complex entry normalized by \(\sqrt\mu\) rather than \(\sqrt s\), multiply the preceding normalized sum by \(r_{ab}=(s_{ab}/\mu)^{1/2}\). In the following formulas \(H_j\) denotes the complex variable of integration for block \(j\). For a generic tuple the smoothed conditional density relative to the standard complex Gaussian block product on the moderate region is
\[
 (1+o(1))\prod_{a,b}r_{ab}^{-2k}
  \exp\!\left(
  \sum_{j,a,b}\Big[(1-r_{ab}^{-2})|(H_j)_{ab}|^2
                   -\frac{|(H_j)_{ab}|^4}{4s_{ab} r_{ab}^4}\Big]\right).
                                                                           \tag{10}
\]
To obtain it, first apply (7) with quartic (9) to each independent entry, then change variables by \(r_{ab}\) in all its coordinates. The factor \(1/4\) in (10) is the \(1/16\) of (9) times \(4\) from the squared realification norm \(\|z_j\|^2=2|(H_j)_{ab}|^2/r_{ab}^2\). For exceptional tuples the density ratio is uniformly bounded on the same region instead. The exponential factors and Jacobians in (10) are uniformly bounded on the moderate region and on every fixed count rectangle \(\max|g_{ab}|\le C_0\), since
\[
 (1-r_{ab}^{-2})L\ \longrightarrow\ g_{ab}/\sqrt c,
 \qquad
 \frac{L^2}{4s_{ab}r_{ab}^4}\ \longrightarrow\ 1/(4c),
\]
where the difference from the indicated right-hand sides tends to zero uniformly even as the count vectors vary in the rectangle. The deterministic smoothing displacement after scaling is still \(O_{m,r,k}(h)\).

Under the complex Gaussian reference conditioned on \(\|H_j\|^2>b_d+x+o(1)\) for every \(j\), (5) shows that \(H_j/\sqrt L\) converge to independent rank-one matrices with the directions in (2). The probability outside the moderate region is \(o(N^{-k})\) before and after comparison, by increasing its radius with an \(A>k\) in section 2. Hence (10), bounded convergence on this region, (4) and deterministic sandwich give joint exceedance probability
\[
   N^{-k}\big[(e^{-x}\Psi_c(g))^k+o(1)\big]
                                                                           \tag{11}
\]
for generic tuples, uniformly in the count rectangle. For uniformity of the expectation use that the exponential factors are uniformly Lipschitz in \(g\) on the fixed rectangle and moderate region, then a finite net and (5). For exceptional tuples the bound is \(O(N^{-k})\), uniformly. Thus the \(O_k(N^{k-1})\) exceptional tuples have vanishing contribution to the factorial moments.

The conditional factorial moments now differ from \((e^{-x}\Psi_c(g))^k\) by \(o(1)\), for every \(k\) and uniformly on the count rectangle. The parameter \(e^{-x}\Psi_c(g)\) is bounded there. Bonferroni bounds first at a fixed order, then at arbitrarily high even and odd orders, therefore prove the uniform conditional zero-count formula \(\exp(-e^{-x}\Psi_c(g))+o(1)\). Conditioning matters here: unconditional factorial moments in a random-intensity model need not determine the zero-count probability.

Finally the independently binomial counts have \(\mu\to\infty\), \(p_d\to0\), and \(g\) converges in law to a matrix of independent standard normals. This follows from the bounded-summand binomial central limit theorem, since the variance is \(\mu(1-p_d)\sim\mu\). Integrate the zero-count formula first on fixed count rectangles, then let \(C_0\to\infty\) using tightness and continuity of the bounded limit function. The two whole-law couplings at the start of this section cost \(o(1)\). This proves (3).

**Replay.** Run `python3 verify-dyadic-spectral-extreme.py`. The exact checks use the odd-root group sums, the generic fourth-cumulant cancellation, and symbolic incomplete-Gamma determinant polynomials for (4). The verifier is not used in the asymptotic argument.
