# Isolating any fixed phase window in a single-target Goldbach zero-pair formula

The exact dyadic-scale nullspace below comes from the support of the actual arithmetic correlation, not an averaged exceptional-set estimate. Its spectral localization assumes only Dirichlet GRH for primitive conductors dividing the target, including conductor 1, and is conditional as such. The separate evaluation of functional-equation partners is unconditional. No one-sided bound on the surviving amplified arithmetic sum, hence no Goldbach theorem, is claimed.

Use a fixed, real nonnegative \(f\in C_c^\infty((a,b))\), \(0<a<1/2<b<1\), positive near \(1/2\). Put \(m(s)=\int_0^\infty f(u)u^{s-1}du,\ m=m(1)>0\). For even \(N>2\) and \(Y>0\), put
\[
 T_N(Y)=\frac1{Y\varphi(N)}\sum_{\chi\bmod N}\chi(-1)
             \left|\sum_n\Lambda(n)\chi(n) f(n/Y)\right|^2.
\]
Character orthogonality gives exactly the sum of \(\Lambda(n)\Lambda(l)f(n/Y)f(l/Y)/Y\) over \((nl,N)=1,\ n+l\equiv0\bmod N\). At \(Y=N\) the only possible multiple is \(N\). If no actual prime pair in the fixed window is present, \(0\le T_N(N)\ll_f N^{-1/2}\log^2 N\) (count the possible proper powers, \(O(\sqrt N)\), encountering at most one complement for each). In particular a fixed positive lower bound implies an actual pair. Prime pairs with a nonunit prime occur only at \(N=2p\) and do not affect this sufficient implication. **For every** \(j\ge1,\ T_N(N/2^j)=0\) exactly: the two positive operands sum to less than \(bN<N\). These identities concern this same modulus and same target.

## Actual zero-pair formula

Index the nontrivial zeros of the primitive \(L(s,\chi^*)\) with multiplicity. Under the stated GRH write them \(1/2+i\gamma_j\), with real ordinates; no simplicity, no independence, and no symmetry of one complex character's ordinates about zero are assumed. Write \(\Phi=\varphi(N)\). Define
\[
 {\cal Z}_N[Q;U]
 =\Phi^{-1}\sum_{\chi\bmod N}\chi(-1)
 \sum_{\substack{i,j\\z_{ij}\in U}}
 N^{i(\gamma_i-\gamma_j)}m(\tfrac12+i\gamma_i)
 \overline{m(\tfrac12+i\gamma_j)}\,Q(z_{ij}),\quad
 z_{ij}=\exp(-i(\gamma_i-\gamma_j)\log 2).
\]
Both zeros in each pair are from the **same** primitive L-function inducing the indicated character. The restriction is real after summation when \(U\) is invariant under conjugation and \(Q\) has real coefficients (swap \(i,j\)). The sums are absolutely convergent at fixed \(N,Q\).

For \(Q(z)=\sum_{j\le d} c_j z^j\), \(Q(0)=1\), the scale identities and the smooth explicit formula give
\[
 T_N(N)=Q(1/2)\frac{N}{\Phi}m^2
             +{\cal Z}_N[Q;\mathbb T]
             +O_f\!\left(\|Q\|_1\,2^{d/2} N^{-1/2}\log^C(3N)\right)              \tag{1}
\]
provided \(d=O(\log\log(3N))\); here \(\|Q\|_1=\sum|c_j|\). In this note \(\mathbb T\) in the spectral sums denotes the complex unit circle. For (1), the smooth explicit formula for the primitive character gives, uniformly in \(N/2^d\le Y\le N\),
\[
 Y^{-1/2}\sum_n\Lambda(n)\chi(n)f(n/Y)
 ={\bf1}_{\chi=\chi_0}\sqrt Y\,m
     -\sum_i Y^{i\gamma_i}m(\tfrac12+i\gamma_i)
     +O_f(Y^{-1/2}\log^2(3N)).
\]
Indeed shift the Mellin contour from \(\Re s=2\) to \(-1/2\) in \(-L'/L\); smooth decay and the functional equation bound the new integral by \(O_f(Y^{-1/2}\log(3N))\) **before** dividing by \(\sqrt Y\). The possible trivial zero at 0 contributes \(O_f(1)\); discard powers of primes dividing \(N\) to return from \(\chi^*\) to \(\chi\), costing \(O_f(\log^2(3N))\) before division. Standard horizontal contours avoiding zeros justify the shift. The unit-height zero-count bound \(O(\log(N(2+|t|)))\) and rapid Mellin decay imply \(\sum_i|m(1/2+i\gamma_i)|\ll_f\log(3N)\). On squaring, the principal pole-zero cross term is \(O_f(\sqrt N\log N/\Phi)\), and its pole-error cross term is \(O_f(\log^2N/\Phi)\); both are within the error displayed in (1) since \(N/\Phi\ll\log\log(3N)\). For every other character the squared approximation error is \(O_f(Y^{-1/2}\log^C N)\). Sum the resulting formula at \(Y=N/2^j\) with coefficients \(c_j\). The pole changes by \(2^{-j}\), the zero pair by \(z_{ij}^j\), proving (1).

**Arbitrary fixed phase window.** Given any nonempty open conjugation-invariant subset \(U\) of the unit circle, there exists a fixed *real* polynomial \(P\) with \(P(0)=P(1/2)=1,\ P(1)=0,\ \sup_{\mathbb T\setminus U}|P|\le1/2\) (for \(U=\mathbb T\) take \(1+z-2z^2\)). Indeed \(K=(\mathbb T\setminus U)\cup\{0,1/2,1\}\) has empty interior and connected complement unless adding 1 fills the entire gap, impossible for nonempty open U. Specify value zero on the closed arc-set and at 1, and 1 at 0 and 1/2. Polynomial approximation on \(K\) follows from Mergelyan's theorem; symmetrize coefficients by conjugation and correct the three interpolation errors by the fixed node Lagrange polynomials, starting with arbitrarily small uniform approximation error. This proof also works for disconnected windows. With \(k=\lceil 6\log\log(3N)/\log 2\rceil\), (1) gives
\[
 T_N(N)=\frac{N}{\Phi}m^2+{\cal Z}_N[P^k;U]+o_{f,U}(1).                         \tag{2}
\]
Indeed the omitted pairs are bounded in absolute value by \(O_f(2^{-k}\log^2(3N))\); degree \(k\deg P=O_U(\log\log N)\) and coefficient norm \(\le\|P\|_1^k=(\log(3N))^{O_U(1)}\). In particular \(P^k(1)=0\) deletes **every** pair of equal ordinate, including mixed multiplicity indices; the unit-circle window may even be separated from 1. If \(N\) is unrepresented,
\[
 {\cal Z}_N[P^k;U]= -\frac{N}{\Phi}m^2+o_{f,U}(1).
\]
More usefully, proving a uniform one-sided inequality \({\cal Z}_N[P^k;U]\ge -(1-\epsilon)(N/\Phi)m^2\) for a single window and any fixed \(\epsilon>0\) would imply eventual Goldbach under this explicit formula's GRH hypothesis. The \(o(1)\) is absolute, not just relative. This does not estimate the amplified pairs inside \(U\), and does not give localization to a *shrinking* window. The maximum principle already gives \(\max_{|z|=1}|P(z)|>1\): one must pay for shrinking the other phases.

## Independent diagonal computation, and the unconditional partner identity

No localization polynomial is needed for the following. With \(h(t)=m(1/2+it)m(1/2-it)\) entire and even, define the unconditional functional-equation partner diagonal by
\[
 D_N=\Phi^{-1}\sum_{\chi\bmod N}\chi(-1)
       \sum_{\rho\ {\rm of}\ L(s,\chi^*)} m(\rho)m(1-\rho).
\]
For a complex character, the functional equation and conjugation pair \(\rho\) with \(1-\bar\rho\) in this SAME primitive L-function, including multiplicity. Thus the product is that of one term and the conjugate of its partner; the combined dilation power \(Y^{\rho+\overline{1-\bar\rho}-1}\) is identically 1. Under GRH each zero is its own partner and this computes the sum of the \(i=j\) summands; colliding **different** indices at a repeated ordinate are not counted by \(D_N\). Then, uniformly as even \(N\to\infty\),
\[
 D_N=-\frac12\iint\frac{f(u)f(v)}{u+v}\,du\,dv
           +O_f(\log(3N)/\Phi).                                                  \tag{3}
\]

For details, the even-test Weil explicit formula for a primitive character of conductor \(d\) has conductor term \(\log(d/\pi)(2\pi)^{-1}\int h(t)dt\), archimedean term \((2\pi)^{-1}\int h(t)\Re\psi((1/2+\kappa+it)/2)\,dt\) for \(\kappa=0,1\) denoting the parity, and prime terms with \(\chi^*(p^\nu)+\overline{\chi^*(p^\nu)}\), Mellin autocorrelation at \(\nu\log p\), and coefficient \(-(\log p)/\sqrt{p^\nu}\) with the normalized transform. There is a bounded \(h(i/2)+h(-i/2)\) correction for the conductor-one pole. See [Fiorilli–Miller, §2](https://web.williams.edu/Mathematics/sjmiller/public_html/math/papers/DirichletZeros_DFandSJM_90.pdf) (or the usual Weil explicit formula). Autocorrelation in \(\log u\) has support in \([-\log(b/a),\log(b/a)]\), so only finitely many \(p^\nu\le b/a\) can occur, depending solely on \(f\).

Here are all the parity averages, including imprimitive changes.

* Exactly half of the characters modulo \(N>2\) are even. If \(\ell^v\parallel N\), \(M=N/\ell^v\), the signed average of the \(\ell\)-part of \(\log d_\chi\) vanishes unless \(M\le2\), by character orthogonality on the other factor. When \(\ell^v>2\), the signed local sum of conductor exponents is \(-1\) for odd \(\ell\) and \(-2\) for \(\ell=2\): expand the exponent as \(\sum_{j=1}^v(1-\mathbf1_{d_{\chi,\ell}\mid\ell^{j-1}})\), noting that the signed count of characters of modulus \(\ell^{j-1}\) is zero except when that modulus is 1 or 2. Each surviving count is then 1. For \(\ell^v=2\) the exponent is always zero. Thus the averaged conductor logarithm is \(-2\log2/\Phi\) if \(N=2^v>2\), \(-\log\ell/\Phi\) if \(N=2\ell^v\) for odd prime \(\ell\), and zero otherwise.
* For \(p\nmid N\), the signed average of \(\chi^*(p^\nu)\) is \(\mathbf1_{p^\nu\equiv-1\bmod N}\), zero for all sufficiently large \(N\). For \(p^v\parallel N\), nontrivial local conductor at \(p\) gives zero, while the principal local component allows ordinary character orthogonality on \(M=N/p^v\); the exact average is \(\varphi(p^v)^{-1}\mathbf1_{p^\nu\equiv-1\bmod M}\). When it is nonzero, \(M\mid p^\nu+1\ll_f1\) and \(p\ll_f1\), hence the factor is \(O_f(1/N)\). The same holds for complex conjugates. In particular these terms vanish identically when the support ratio is strictly less than 2.
* The conductor-independent \(-\log\pi\) part cancels. The digamma reflection formula gives \(\Re[\psi(1/4+it/2)-\psi(3/4+it/2)]=-\pi/\cosh(\pi t)\). Hence the signed gamma contribution is exactly \(-\tfrac14\int h(t)/\cosh(\pi t)\,dt\). The Fourier integral \(\int e^{itx}\,dt/\cosh(\pi t)=1/\cosh(x/2)\) and \(x=\log(u/v)\) give the reciprocal-sum kernel in (3). The sole zeta pole correction is \(O_f(1/\Phi)\). All estimates in (3) are unconditional when \(D_N\) is defined as above.

For \(a>1/8\), the magnitude of the main diagonal term in (3) is at most \(m^2/(4a)<2m^2\); since \(N/\Phi\ge2\), the principal plus this individual-index diagonal has a uniform positive margin. Neither this fact nor deleting the diagonal using (2) supplies cancellation off the diagonal.

## Inputs and limitation

Low zeros are not inferred from sparse exceptional-set theorems. The recent [Althöfer–Chen–Perelli–Pintz](https://arxiv.org/html/2611.09386v1#S4) calculation sums over exceptional indices before taking its prime restriction norm; [Bhowmik–Grimmelt](https://arxiv.org/html/2607.27282v2#S7) use smooth prime explicit formulae for rational major arcs. Neither asserts the same-character, parity-signed gap bias in (2). Classical work of [Languasco–Perelli on pair correlation and exceptional sets](https://www.research.unipd.it/retrieve/e14fb267-6015-3de1-e053-1705fe0ac030/%5B3%5D.pdf) uses different averaging and does not supply this pointwise one-sided estimate. The method is a fixed-target scale filter with an exact unconditional zero-diagonal evaluation, not a claimed unconditional solution or a claimed derivation of GRH.

[Gou–Wang–Xu v1, §3, equation (3.1)](https://arxiv.org/html/2611.18825v1#S3) already uses the parity twist modulo the target and isolates the sum by its support. Their positive result over the integers in Theorem 1.1 assumes both Dirichlet GRH and their ratios hypothesis. Their fixed-difference detector in §4 uses different cancellations. Here the role of the smaller-scale nullspace is to preserve the principal pole while localizing the zero-gap phase; neither the parity projection nor additive support isolation is new by itself. [Chen–Gupta–Li v2](https://arxiv.org/abs/2507.08296v2) treat zero density and the least Goldbach number in an arithmetic progression, not this same-target signed off-diagonal term.
