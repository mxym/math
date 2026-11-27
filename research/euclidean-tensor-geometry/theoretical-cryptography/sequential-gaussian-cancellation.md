# Exactness and first nonzero error in sequential lattice Gaussian rounding

An ideal sequential Gaussian rounding rule uses one-dimensional discrete Gaussians along an ordered Gram–Schmidt basis. Standard flatness bounds treat all rows using the largest orthogonalized length. We show which rows can actually contribute to the leading statistical error, how distinct rows can cancel across widths, and how a finite test decides whether **all** Gaussian widths are exact for the specified center. The model is a standalone probability comparison with a specified basis and center, not a test on a signer, secret basis, implementation or deployment.

## 1. Model and answer at a fixed shape

Let \(B=(b_1,\dots,b_d)\) be an ordered basis of a full-rank Euclidean lattice. Write \(b_i^*\) for its Gram–Schmidt vectors, \(\ell_i=\|b_i^*\|\), and
\[
 b_j=b_j^*+\sum_{i<j}\mu_{ij} b_i^*,\qquad
 c=\sum_{i=1}^d c_i b_i^*.
\]
Use a Gaussian width \(s>0\) in the convention \(\exp(-\pi\|Bz-c\|^2/s^2)\). The target \(Q_s\) is the law on \(z\in\mathbb Z^d\) proportional to this expression. Define \(P_s\) by drawing \(z_d,z_{d-1},\ldots,z_1\), each \(z_i\) from the one-dimensional discrete Gaussian of width \(s/\ell_i\) centered at \(c_i-\sum_{j>i}\mu_{ij}z_j\). This is the ideal Klein–GPV law. The push-forward under \(z\mapsto Bz\) has identical distances.

Take \(N\) strictly upper triangular with \(N_{ij}=-\mu_{ij}\) for \(i<j\), and let
\[
 G=\overline{\{Nz\bmod\mathbb Z^d:z\in\mathbb Z^d\}}
       \ \subset\ (\mathbb R/\mathbb Z)^d,\quad
 \alpha_i=\frac{\pi}{\ell_i^2}.
\]
Use probability Haar measure on this compact subgroup. For each \(\lambda>0\) in the locally finite set \(\{\alpha_i k(2m+1): i\in[d],\ k\ge1,\ m\ge0\}\), put
\[
 H_\lambda(g)=
 \sum_{\substack{i,\ k\ge1,\ m\ge0\\ \alpha_i k(2m+1)=\lambda}}
 \frac{2(-1)^{k+1}}k\,\cos\bigl(2\pi k(c_i+g_i)\bigr).
 \tag{1}
\]
Every sum in (1) is finite. Ignore constants as functions of \(g\in G\).

**Theorem.** If all \(H_\lambda\) are constant on \(G\), then \(P_s=Q_s\) for every \(s>0\). Otherwise let \(\lambda_*\) be the least index with \(H_{\lambda_*}\) nonconstant and \(H=H_{\lambda_*}\). Then, for the fixed ordered basis and fixed center,
\[
\begin{split}
 e^{\lambda_*s^2}\|P_s-Q_s\|_{\rm TV}
    &\ \longrightarrow\ \tfrac12\int_G |H-\overline H|,\\
 e^{2\lambda_*s^2}\chi^2(P_s\Vert Q_s)
    &\ \longrightarrow\ \int_G (H-\overline H)^2,\qquad
 \overline H=\int_G H .
\end{split}                                                   \tag{2}
\]
The two constants are positive. If such a \(\lambda_*\) exists, exactness at any isolated width is not excluded, but there can be no accumulation of exact widths within \((0,\infty)\).

Call row \(i\) **active** if some \(\mu_{ij}\notin\mathbb Z\) for \(j>i\). For a nonempty active set, the sharp worst-center exponent is simply
\[
             \min_{i\ \mathrm{active}}\alpha_i .
 \tag{3}
\]
Here “sharp” means upper and lower positive constant multiples of its exponential \(e^{-s^2\min\alpha_i}\) for large \(s\), taking a supremum over all real centers; the lower bound already holds at \(c=0\). The maximum Gram–Schmidt length among **inactive** rows imposes no error at all in this comparison. At \(c=0\) exactness, even at a single width, is equivalent to no active rows.

**Proof.** Let \(\theta(q,x)=\sum_{k\in\mathbb Z}q^{k^2}e^{2\pi i k x}\) for \(0<q<1\). Orthogonality gives \(\|Bz-c\|^2=\sum_i\ell_i^2(z_i-c_i-(Nz)_i)^2\). Poisson summation in each one-dimensional normalizer shows that, setting \(g=Nz\bmod\mathbb Z^d\) and \(q_i=e^{-\alpha_i s^2}\),
\[
 \frac{P_s(z)}{Q_s(z)}
     =\frac{V_s(g)}{\mathbb E_{Q_s}V_s},\qquad
 V_s(g)=\prod_i \theta(q_i,c_i+g_i)^{-1}.                     \tag{4}
\]
The factors \(s/\ell_i\) are independent of \(z\) and cancel in (4). The [Jacobi triple product](https://dlmf.nist.gov/20.5) and the logarithm series give, uniformly in real \(x\) at every fixed \(q<1\),
\[
 \log\theta(q,x)=C(q)+
  2\sum_{k\ge1}\frac{(-1)^{k+1}}{k}
       \sum_{m\ge0}q^{k(2m+1)}\cos(2\pi kx).
 \tag{5}
\]
Indeed the factors with \(x\) dependence are \((1+q^{2m+1}e^{2\pi ix})(1+q^{2m+1}e^{-2\pi ix})\); summing their absolutely convergent logarithm series proves (5). Thus the \(g\)-dependent coefficients in \(-\log V_s(g)\) are exactly (1). If all are constant, (4) is identically 1. Otherwise, subtract the value at an arbitrary fixed \(g_0\), which does not affect (4). Local finiteness of the index set and absolute convergence at any fixed positive \(s\) show that, uniformly on \(G\), the first nonconstant term is \(e^{-\lambda_*s^2}(H(g)-H(g_0))\), with an exponentially smaller remainder. Exponentiating and dividing by the \(Q_s\) expectation therefore gives
\[
 \frac{P_s}{Q_s}-1
   =-e^{-\lambda_*s^2}(H(g)-\mathbb E_{Q_s}H(g))
       +o(e^{-\lambda_*s^2})
 \tag{6}
\]
uniformly on \(z\).

Under \(Q_s\), \(Nz\bmod\mathbb Z^d\) tends weakly to Haar on \(G\). For \(a\in\mathbb Z^d\), its \(a\)-character is \(\exp(2\pi i(N^\mathsf T a)\cdot z)\). It is identically 1 exactly when \(N^\mathsf T a\in\mathbb Z^d\). Otherwise Poisson on the full Gaussian quadratic form \(B^\mathsf T B\) says the normalized expectation tends to zero: its numerator is a modulated dual Gaussian sum with no zero frequency (the centers contribute only unit-modulus phases), while the unmodulated denominator tends after normalization to 1. Concretely the absolute numerator is bounded by the mass of \(\mathbb Z^d-N^\mathsf T a\) in the quadratic form \((B^\mathsf T B)^{-1}\) at exponent \(\pi s^2\). Density of restricted torus characters on \(G\) proves the weak limit. Combining this with (6) proves (2); Haar has full support, and \(H\) is continuous nonconstant. For the nonaccumulation assertion choose two points of the dense image of \(N\) where \(H\) differs. The difference of their log-normalizers is real analytic on \(s>0\), from the Gaussian series or (5), and not identically zero by the first nonconstant asymptotic, so its zeros have no interior accumulation.

For (3), inactive factors are constant in (4), and the remaining log-normalizer variations are uniformly \(O(\sum_{\mathrm{active}}e^{-\alpha_i s^2})\); this gives the upper bound independent of \(c\). At \(c=0\) the earliest coefficient from the active rows is \(2\sum_{\alpha_i=\lambda_*,\ i\ \mathrm{active}}\cos(2\pi g_i)\). Every summand is maximized at \(g=0\), and some summand is strictly less at some \(g\in G\) by activity. Earlier exponents from inactive rows are constant. This establishes that the first exponent is exactly (3) and proves the lower bound. Also at any \(s>0\) each \(\theta(q_i,\cdot)\) is maximized at integer arguments, strictly so modulo \(\mathbb Z\) by its positive Fourier coefficients. The product in (4) cannot be constant at \(c=0\) if any factor varies, since all factors are simultaneously maximized at \(g=0\). Equivalently, if all offsets are integral, the unimodular upper triangular Gram–Schmidt change actually produces an orthogonal lattice basis, and (4) is exact for all \(c,s\).

## 2. A finite all-width certificate, including unequal scales

The apparent infinite condition in (1) can always be replaced by finitely many coefficient tests at any fixed basis and center. Partition the rows by rational proportionality of \(\alpha_i\). Different classes never contribute to the same \(\lambda\) in (1). In a class of \(r\) rows, choose a positive \(\alpha_0\) so that \(\alpha_i=m_i\alpha_0\) with each \(m_i\) a positive integer, and put \(M=\operatorname{lcm}_{i}(2m_i)\).

**Finite test.** In each class it is enough to check that the functions \(H_{n\alpha_0}\) are constant for \(1\le n\le4rM\), treating an absent coefficient as zero. If every class passes, the rule is exact at every width. If not, the first nonconstant coefficient within each failing class is already in its tested range, so taking the smallest of these actual exponents gives \(\lambda_*\) in (2). This is a finite analytic certificate, not a time-complexity or finite-arithmetic claim for arbitrary real inputs.

**Proof.** Within the class write \(L_n=H_{n\alpha_0}\) and define
\[
 J_n(g)=
 \sum_{i:\,m_i\mid n}
  \frac{2(-1)^{n/m_i+1}}{\,n/m_i\,}
       \cos\bigl(2\pi(n/m_i)(c_i+g_i)\bigr).
\]
Grouping the odd number \(2m+1\) in (1) gives
\[
                 L_n=\sum_{a\mid n,\ a\ {\rm odd}}J_{n/a}.  \tag{7}
\]
In particular, up to any fixed index, all the \(L_n\) are constant if and only if all the \(J_n\) are, by induction on \(n\) using the \(a=1\) term. We show that the latter condition holds at all indices if it holds through \(4rM\).

Fix a residue representative \(1\le a\le M\), and write \(n=a+pM\) for \(p\ge0\). The set of participating \(i\) in \(J_n\) and their signs \((-1)^{n/m_i+1}\) are fixed, since all \(m_i\) and \(2m_i\) divide \(M\). On multiplying by \(n\), the remaining scalar weight of each cosine is also fixed, equal in magnitude to \(2m_i\). For each fixed \(g\) and reference \(g_0\), express
\[
                (a+pM)\bigl(J_{a+pM}(g)-J_{a+pM}(g_0)\bigr)
\]
as a linear combination of at most \(4r\) sequences \(\beta^p\), by writing the cosines as pairs of complex exponentials. For example from \(g\) the bases are \(\beta=\exp(\pm2\pi i(M/m_i)(c_i+g_i))\); from \(g_0\) they are analogous. If bases coincide, combine their coefficients. Vanishing for the first \(4r\) consecutive values of \(p\) implies all coefficients of the distinct bases are zero by the Vandermonde determinant, hence vanishing at every \(p\). Those first indices are all at most \(4rM\) and the hypothesis holds for every \(g\). This proves all \(J_n\) constant, then all \(L_n\) constant by (7).

Each individual constancy test is finite in terms of \(N\) and the phases \(c\). In a cosine expansion replace each cosine by its two exponential terms. Two frequencies \(a,a'\in\mathbb Z^d\) define the same restricted character on \(G\) exactly when \(N^\mathsf T(a-a')\in\mathbb Z^d\). After grouping identical characters, all coefficients of nontrivial characters must vanish (linear independence by Haar orthogonality). This does not require the torus subgroup to be finite. For rational \(\mu_{ij}\) and rational \(c_i\), the grouping and coefficient cancellations can be checked by integer arithmetic with roots of unity. No knowledge of the target distribution is required for the criterion.

## 3. Exact and nonexact cancellations on public toy bases

Take the first two basis vectors orthogonal of the same length, with the last vector having Gram–Schmidt coefficients \((\mu,\mu)\) in those two rows; all other off-diagonal entries are zero. Set \(c_1=0,c_2=1/2\) in Gram–Schmidt coordinates. For \(\mu=1/2\), the two theta factors are interchanged by changing the parity of the last coefficient, so the rule is exact at every width despite both rows being active. For \(\mu=1/3\), the first shell cancels, but the second shell is \(-2\cos(4\pi g_1)\) on the diagonal group of order three; its values are \((-2,1,1)\), and its mean is zero. In this latter case (2) has TV constant \(2/3\), chi-squared constant \(2\), and exponent \(\lambda_*=2\alpha_1\).

Cancellation can also cross *unequal* scales. From (5), the identity
\[
           \theta(q,x)\theta(q,x+1/2)
           =C_2(q)\,\theta(q^2,2x+1/2)                     \tag{8}
\]
holds with \(C_2(q)>0\) independent of \(x\): the left log series drops its odd \(k\), and its even \(k=2l\) coefficients match the right log series. For a four-dimensional example, take three initial orthogonalized lengths \(\ell,\ell,\ell/\sqrt2\), the first three basis vectors themselves orthogonal, and the only nonzero Gram–Schmidt coefficients \(\mu_{1,4}=\mu_{2,4}=1/4,\ \mu_{3,4}=1/2\). Use centers \(c_1=0,c_2=1/2,c_3=0\); the fourth row is inactive. With \(x=-z_4/4\), the relevant product is
\[
       \theta(q,x)\theta(q,x+1/2)\theta(q^2,2x)
       = C_2(q)C_2(q^2)\,\theta(q^4,4x+1/2).
\]
Since \(4x\in\mathbb Z\), it is constant. Neither the first two factors together nor the third factor is constant separately. This realizes exact statistical rounding by true cancellation across unequal lengths within a rational-proportionality class; testing only equal-length groups would be insufficient.

## 4. Prior scope and replay

[Gentry–Peikert–Vaikuntanathan, *Trapdoors for Hard Lattices and New Cryptographic Constructions*, Theorem 4.1](https://eprint.iacr.org/2007/432) and [Lyubashevsky–Peikert–Regev, *A Toolkit for Ring-LWE Cryptography*, Lemma 2.9 and its discussion](https://sites.cc.gatech.edu/fac/cpeikert/pubs/toolkit.pdf) give the standard large-width guarantee in terms of the largest Gram–Schmidt length. [Ducas–Lyubashevsky–Prest, *Efficient Identity-Based Encryption over NTRU Lattices*, §4 and Algorithm 1](https://tprest.github.io/pdf/pub/gpv-ibe.pdf) analyze statistical accuracy with a divergence bound, and [Wang–Ling, *On the Geometric Ergodicity of Metropolis-Hastings Algorithms for Lattice Gaussian Sampling*](https://arxiv.org/abs/1501.05757) use the product of normalizers for a Markov proposal in (13) and (17). The product identity itself is not new. The [posterior-heat note](gaussian-rounding-posterior-heat.md) studies a different probability experiment: one continuous Gaussian input and one Gaussian rounding, not the sequence of conditional lattice draws. The additions here are the full error exponent and constants after possible cancellation, the active-row worst-center exponent, and the finite analytic all-width criterion. These are not statements on implementations, side channels, concrete schemes, cryptanalysis, or a new computational reduction.

Run `python3 verify-sequential-gaussian-cancellation.py` with Python and mpmath. It checks cyclotomic coefficient cancellations of generated toy Gram–Schmidt data, and replays numerical checks of (8) and of the order-three example. The analytic proofs above do not assume these numerical checks.
