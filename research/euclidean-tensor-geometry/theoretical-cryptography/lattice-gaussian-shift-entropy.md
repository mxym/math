# Entropy versus shift for discrete lattice Gaussians

For a full lattice \(L\), a positive definite precision \(P\), and a shift \(z\), let \(X_{P,z}\) have distribution proportional to \(e^{-x^TPx}\) on \(L+z\). Shifting can change the entropy even though the precision is kept fixed. We show:

1. In rank one, **every positive-order Rényi entropy, including Shannon and min-entropy, strictly increases as the center moves from an integral point to halfway to the next point**. The result adds on orthogonal products with product precision. It is not a majorization statement; ordinary majorization already fails in one dimension.
2. On an arbitrary lattice the centered coset minimizes Rényi entropy of order \(k\) and \(1/k\), for every positive integer \(k\ge2\). This follows from a matrix submultiplicativity theorem for normalized Gaussian mass, including noncommuting precisions.
3. For every fixed nonzero coset and every fixed positive finite order, including Shannon, the centered coset strictly minimizes the two-coset comparison at both sufficiently wide and sufficiently narrow ends. We give sharp leading terms. We do not claim all-order optimality at all intermediate widths on general lattices.

These are abstract distribution comparisons; no computation on cryptographic instances or claim about learning hardness is involved.

## 1. Strict coordinatewise monotonicity in rank one

It suffices to treat \(L=\mathbb Z\) with precision \(\lambda>0\) and \(0\le z\le1/2\); general lattice spacings rescale \(\lambda\), and shifts reduce to this interval by reflection and translation. Put
\[
 Z_\lambda(z)=\sum_{n\in\mathbb Z}e^{-\lambda(n+z)^2},\quad
 g(a,\lambda)=-\log\!\left(Z_\lambda(z)/Z_\lambda(0)\right),\quad
 a=2\pi z,\quad \Phi(a,\lambda)=g(a,\lambda)/\lambda .
\]
For \(0<\alpha<\infty\), \(\alpha\ne1\), let \(H_\alpha(X)=(1-\alpha)^{-1}\log\sum_x\Pr(X=x)^\alpha\). The difference between shifted and centered entropies equals
\[
 \Delta H_\alpha=
 \frac{\alpha\lambda}{\alpha-1}
       \left[\Phi(a,\alpha\lambda)-\Phi(a,\lambda)\right],
 \qquad
 \Delta H_1=\lambda^2\partial_\lambda\Phi(a,\lambda).
 \tag{1}
\]
Thus strict increase in \(\lambda\) of \(\partial_a\Phi\), and strict positivity of its \(\lambda\) derivative, are sufficient for strict increase of every entropy with \(a\in(0,\pi)\).

**The theta transform.** Set \(u=\pi^2/\lambda\). By Poisson and the [Jacobi triple product](https://dlmf.nist.gov/20.5.E9),
\[
 g(a,\lambda)=\sum_{n\ge1} h_a((2n-1)u),\qquad
 h_a(x)=\log\frac{\cosh x+1}{\cosh x+\cos a}.
 \tag{2}
\]
Indeed the \(n\)-th normalized theta factor is
\((1+2e^{-(2n-1)u}\cos a+e^{-2(2n-1)u})/(1+e^{-(2n-1)u})^2\).
For \(0<a<\pi\), the functions in (2) and their shift derivatives decay exponentially. With Fourier convention \(\widehat h(t)=\int h(x)e^{-itx}\,dx\), one has
\[
 \widehat h_a(t)=\frac{2\pi(\cosh(at)-1)}{t\sinh(\pi t)},\qquad
 \partial_a\widehat h_a(t)=2\pi\frac{\sinh(at)}{\sinh(\pi t)} .
 \tag{3}
\]
For a derivation, write \(h_a(x)=2\log\cosh(x/2)-\log\cosh((x+ia)/2)-\log\cosh((x-ia)/2)\), with the analytic logarithm on the strip \(|\Im x|<\pi\). Differentiating twice gives the same combination of translates of \(k(x)=\tfrac14\operatorname{sech}^2(x/2)\). Its Fourier transform is \(\Gamma(1-it)\Gamma(1+it)=\pi t/\sinh(\pi t)\), by the substitution \(y=e^x\) in the beta integral. Moving each integration line inside the strip multiplies by \(e^{\pm at}\); division by \(-t^2\) yields (3), with the continuous limits at zero. Now use midpoint Poisson summation in (2):
\[
 \partial_a\Phi(a,\lambda)
 =\frac1{2\pi}\sum_{j\in\mathbb Z}(-1)^j
        \frac{\sinh(a j\lambda/\pi)}{\sinh(j\lambda)} .
 \tag{4}
\]
Here the \(j=0\) ratio is \(a/\pi\). All sums and derivatives used here converge locally normally for \(0<a<\pi,\lambda>0\).

**The sign by a positive mixture.** Set \(c=(a/\pi)^2\in(0,1)\). The Euler product for \(\sinh\) writes the ratio \(\sinh(at)/\sinh(\pi t)\) as
\[
 \frac a\pi \prod_{n\ge1}\left(c+\frac{1-c}{1+t^2/n^2}\right)
     =\frac a\pi\,\mathbb E e^{-t^2 W}.
\]
Here \(W=\sum_{n\ge1}W_n\), the independent \(W_n\) equal zero with probability \(c\), otherwise exponential with rate \(n^2\). The series is finite almost surely (its expected sum is finite) and \(W>0\) almost surely (the probability that every \(W_n=0\) is zero). Insert the mixture into (4), using absolute summability of the ratios for \(a<\pi\):
\[
 \partial_a\Phi(a,\lambda)=\frac{a}{2\pi^2}
       \mathbb E\!\left[\sum_{j\in\mathbb Z}(-1)^j
                 e^{-j^2W\lambda^2/\pi^2}\right].
 \tag{5}
\]
For every \(b>0\), the theta bracket at exponent \(b\) equals
\(\prod_{n\ge1}(1-e^{-2nb})(1-e^{-(2n-1)b})^2\) by the same Jacobi product. This positive product strictly increases in \(b\) with positive derivative: each factor increases, and even retaining just one factor's derivative gives a strictly positive lower bound locally. Therefore (5) is strictly increasing in \(\lambda\), with strictly positive derivative. To see the derivative sign without any mixed-integral regularity assumption, restrict difference quotients to a compact interval \(0<w_0\le W\le w_1<\infty\) having positive probability. There is a positive uniform lower derivative there locally in \(\lambda\), and the rest of the mixture is monotone. Analyticity from (2) supplies the derivative. This proves the desired signs in (1). Continuity extends strict ordering to the endpoints. Min-entropy has a direct check: its value on \(0\le z\le1/2\) is \(\log \sum_{n}e^{-\lambda n^2}\cosh(2\lambda nz)\), strictly increasing. On orthogonal product lattices with corresponding product precision, the distributions factor and every order of entropy adds.

**Why not majorization?** For \(z=1/2\) and \(\lambda\downarrow0\) the shifted coset's two largest masses together exceed the centered coset's: their numerators are \(2e^{-\lambda/4}\) and \(1+e^{-\lambda}\) respectively, with difference \(\lambda/2+O(\lambda^2)\), and the denominators are relatively equal up to \(O(e^{-\pi^2/\lambda})\). Yet the centered coset's largest atom is strictly greater by the min-entropy comparison. Neither sorted probability vector therefore majorizes the other.

## 2. Matrix submultiplicativity on every lattice

Define \(f_P(z)=Z_P(z)/Z_P(0)\), \(Z_P(z)=\sum_{x\in L+z}e^{-x^TPx}\). For all positive definite symmetric \(P,Q\), all \(z\), and no commutativity restriction,
\[
 f_{P+Q}(z)\le f_P(z)f_Q(z).
 \tag{6}
\]
To prove this set \(S=P+Q\), and expand the product of the two masses by grouping the two sampled lattice locations by their difference \(v\in L\). Completing the square gives the exact identity
\[
 Z_P(z)Z_Q(z)=\sum_{v\in L}
        e^{-v^T(P-PS^{-1}P)v}\,Z_S(z+S^{-1}Pv).
\]
The weights are positive and invariant under \(v\mapsto-v\); the exponent matrix is positive definite. The same identity at \(z=0\) normalizes the sum. Equation (4c) of [Regev–Stephens-Davidowitz](https://arxiv.org/pdf/1502.04796), applied after a linear change of metric, states
\[
 \bigl[f_S(z+c)+f_S(z-c)\bigr]/2\ge f_S(z)f_S(c).
\]
Substitute \(c=S^{-1}Pv\) and average with the symmetric weights, proving (6).

Induction gives \(f_{kP}(z)\le f_P(z)^k\) for integers \(k\ge2\). The exact entropy difference from the partition functions is
\[
 H_\alpha(X_{P,z})-H_\alpha(X_{P,0})
 =\frac{\log f_{\alpha P}(z)-\alpha\log f_P(z)}{1-\alpha}.
 \tag{7}
\]
Use the integer inequality directly for \(\alpha=k\), and apply it with base precision \(P/k\) for \(\alpha=1/k\). This proves the dimension-free entropy results. Superadditivity of \(-\log f_{\lambda P}(z)\) in scalar precision, which follows from (6), is **not** asserted to imply that \(-\log f_{\lambda P}(z)/\lambda\) is nondecreasing for all \(\lambda\); the latter is stronger and was proved in rank one by (5).

## 3. Sharp endpoint signs at every fixed finite order

Fix \(P,L,z\notin L\), and let the precision be \(\lambda P\).

**Wide regime** \(\lambda\downarrow0\). In the dual lattice let
\[
 b=\min_{\xi\in L^*:\,\cos(2\pi\langle\xi,z\rangle)\ne1}
                 \pi^2\xi^TP^{-1}\xi,\qquad
 A=\sum_{\substack{\xi\in L^*\\ \pi^2\xi^TP^{-1}\xi=b}}
           (1-\cos(2\pi\langle\xi,z\rangle)).
\]
The set is nonempty because \(z\notin L\). Poisson summation yields \(g_\lambda:=-\log f_{\lambda P}(z)\sim A e^{-b/\lambda}\), with an exponentially separated remainder; the derivative also has the first-shell asymptotic \(g_\lambda'\sim A b\lambda^{-2}e^{-b/\lambda}\). Indeed numerator and denominator Fourier expansions agree until this shell, all omitted terms have a positive next-shell gap, and the same argument applies after termwise differentiation. Therefore the entropy gap in (7) has leading terms
\[
 \Delta H_\alpha\sim\begin{cases}
  A e^{-b/(\alpha\lambda)}/(\alpha-1),&\alpha>1,\\
  A (b/\lambda)e^{-b/\lambda},&\alpha=1,\\
  \alpha A e^{-b/\lambda}/(1-\alpha),&0<\alpha<1 .
 \end{cases}
\]

**Narrow regime** \(\lambda\to\infty\). If the shifted coset has \(K\ge2\) minimizers of \(x^TPx\), it approaches the uniform law on those points, and the entropy gap tends to \(\log K\) at every fixed finite positive order including Shannon, by dominated summation through the gap to the next shell. Otherwise use the unique nearest representative \(z'\in L+z\) in the \(P\)-norm and define
\[
 \delta=\min_{\substack{\ell\in L\\ \ell^TPz'\ne0}}
 \{\ell^TP\ell-2|\ell^TPz'|\}>0.
\]
Let \(N\) be the number of unordered pairs \(\{\ell,-\ell\}\) attaining this minimum in the indicated set. Removing the nearest-energy factor from each partition function causes no entropy change. Relative to the centered partition sum, a nonorthogonal pair contributes the extra
\(2e^{-\lambda\ell^TP\ell}(\cosh(2\lambda\ell^TPz')-1)\).
These terms are nonnegative; for each minimizing pair precisely the lower shifted gap yields the leading coefficient one. There is a positive gap in the next relevant energy levels, by discreteness of the two quadratic spectra. Thus the difference of log partition functions after removing the nearest energies is asymptotic to \(N e^{-\lambda\delta}\), with the corresponding differentiated asymptotic. This gives
\[
 \Delta H_\alpha\sim\begin{cases}
  \alpha N e^{-\lambda\delta}/(\alpha-1),&\alpha>1,\\
  N\lambda\delta e^{-\lambda\delta},&\alpha=1,\\
  N e^{-\alpha\lambda\delta}/(1-\alpha),&0<\alpha<1 .
 \end{cases}
\]
These signs are fixed-shift endpoints, not uniform in \(z\) or the Rényi order.

## Literature and replay

[Agostini–Améndola](https://arxiv.org/abs/1801.02373) develop entropy, cumulants, and maximum entropy at prescribed moments via theta functions; our comparison instead holds precision fixed while varying the coset. The main tools credited above are classical Jacobi products and normalized-theta correlation. The fixed-dimensional replay makes 11,664 exact completed-square assertions and 8,060 numerical comparisons, including the two midpoint Poisson evaluations, fractional orders, Shannon, and the majorization obstruction. The proofs do not rely on the numerical tests.
