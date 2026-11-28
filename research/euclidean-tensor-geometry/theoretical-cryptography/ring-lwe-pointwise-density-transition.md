# A pointwise density transition far below the total-variation transition

For a random wrapped ring experiment, maximum likelihood-ratio error and total variation can give opposite answers at the same sample size. We compute a quenched additive profile for the maximum error at \(O(d)\) rows, with exponentially small residual, while true total variation is still exponentially small. A fixed nearest-neighbor coefficient covariance moves this pointwise transition by a diverging sublinear number of rows.

## 1. Setup and theorem

Fix an odd integer \(q\ge3\), possibly composite, \(\beta>0\), and dyadic \(d\to\infty\). Let \(R=(\mathbb Z/q)[X]/(X^d+1)\) and \(b=\beta/d\). Let \(U\) be the signed cyclic shift in the power basis. For a fixed \(0\le \rho<1/2\), define
\[
 C=I+\rho(U+U^\top),\quad \delta=1-2\rho,\quad
 f(y)=\sum_{v\in\mathbb Z^d} b^{v^\top C v}\,e^{2\pi i v\cdot y}.
\]
This is a positive wrapped Gaussian density. Denote by \(g\) its uniform shift average over the full \(q\)-grid; equivalently replace \(b\) by \(b^{q^2}\) in the series. With independent uniform public \(A_1,\dots,A_k\in R\), uniform shared label \(S\in R\), and independent \(f\)-errors \(E_i\), take \(Y_i=A_iS/q+E_i\) modulo the coefficient torus. Assume \(1\le k\le C_0 d\) with \(C_0\) fixed. Let \(F_A\) be the density of the fixed-design response mixture, and \(G=g^{\otimes k}\), both with respect to product Haar.

There is a constant \(c>0\) such that, uniformly over these \(k\),
\[
 \left\|\,\|F_A-G\|_\infty-
      q^{-d}\big(f(0)^k-g(0)^k\big)\,\right\|_{L^2(A)}
         \le e^{-cd}.                                         \tag{1}
\]
The inner essential supremum is over all response vectors. Meanwhile
\[
 \mathbb E_A\|F_A-G\|_2^2\le e^{-cd},                           \tag{2}
\]
where the inner \(2\)-norm is over Haar response vectors. In particular the distance in total variation from the grid reference is exponentially small in mean for every \(k\le C_0 d\), even if the pointwise error in (1) is large. This does not supply a test of nonnegligible probability on a random response.

Writing \(B=\log q\) and \(a_d=k\log f(0)-dB\), if \(a_d\to a\in\mathbb R\) the pointwise error in (1) tends to \(e^a\) in \(L^2(A)\). It tends to zero for \(a_d\to-\infty\), and after division by \(e^{a_d}\) tends to one for \(a_d\to+\infty\). The same statements hold for \(\|F_A/G-1\|_\infty\), since \(G=1+o(1)\) uniformly. For example, \(D_\infty(F_A\|G)=\log\operatorname{ess\,sup}(F_A/G)\) tends to \(\log(1+e^a)\) in probability in the finite window.

For independent coefficients (\(\rho=0\)), \(\log f(0)=2\beta-2\beta^2/d+O(d^{-2})\). Thus along any subsequence with \(2\beta k-dB\to u\), the limiting error is \(e^{u-\beta B}\). For fixed \(0<\rho<1/2\), the exact center is \(k_*(d)=dB/\log f(0)\), and its leading displacement is
\[
 k_*(d)=\frac{B}{2\beta}d
        -\frac{B}{2}\beta^{\delta-1}d^{1-\delta}(1+o(1)).       \tag{3}
\]
The \(O(1)\)-offset profile uses the exact center rather than truncating its expansion. The two results are sharp for the stated random-design experiment, not claims about runtime, parameters in use, or general covariances.

## 2. Algebraic ingredients and uniform Fourier tails

For each fixed odd prime \(p\mid q\), all irreducible factors of \(X^d+1\) over \(\mathbf F_p\) have degree \(\operatorname{ord}_{2d}(p)=\Omega_p(d)\). Every root has exact order \(2d\), and \(v_2(p^{2^j}-1)=v_2(p^2-1)+j-1\) for \(j\ge1\), yielding the linear asymptotic and stabilization of the degree ratio along the dyadic tower. Consequently there is a constant \(c_q>0\) such that every nonzero ideal \(J\) of \(R\) has size at least \(e^{c_q d}\): it contains a simple submodule, whose cardinality is the size of one of these residue fields. For a tuple \(w\in R^h\) not identically zero, with \(h=1\) or 2, \(\sum_i s_i w_i\) is uniform in the nonzero ideal \(\sum_i Rw_i\) for independent uniform \(s_i\).

We also need one fact about the coefficient geometry of a nonzero ideal. There is a fixed dyadic \(d_0\), depending only on \(q\), such that, with \(d=\ell d_0\), every ideal \(J\) in the larger ring decomposes in coefficient coordinates as \(\ell\) copies of some base ideal \(J_0\) in \((\mathbb Z/q)[X]/(X^{d_0}+1)\), interleaved in the \(X^a\)-blocks for \(0\le a<\ell\). To see this, for a prime power \(p^e\Vert q\) factor \(X^{d_0}+1\) into coprime monic Hensel lifts modulo \(p^e\). Substitution \(X\mapsto X^\ell\) gives the factorization at \(d\), still reducing to irreducible factors by the stabilized residue degree. In each corresponding local factor quotient all ideals are powers of \(p\): the quotient modulo \(p\) is a field, all elements nonzero there are units, and an element of minimal \(p\)-valuation in an ideal generates the corresponding power. Thus CRT idempotents and the powers describe every ideal already by extension from the base ring. The direct sum \(R=\bigoplus_{a<\ell}X^aR_{d_0}\) under this substitution proves the coefficient-block statement. In particular there are finitely many base possibilities, and \(J\ne0\) implies \(J_0\ne0\).

Fix a sufficiently small constant \(\varepsilon>0\) and put \(L=\lfloor \varepsilon d/\log d\rfloor\). With probability \(1-e^{-\Omega(d)}\) over either one uniform \(s\), or two independent uniform \(s,s'\), there is no relation \(\sum \overline{s_i}w_i=0\) with nonzero tuple \(w\) of total scalar weight \(\le L\), with \(s_1=s\), \(s_2=s'\) as applicable. Here \(\bar s=s(X^{-1})\) is a uniform-preserving involution. Each nonzero tuple is a relation with probability \(e^{-c_qd}\) by the ideal fact, and there are at most \(\exp(O(\varepsilon d))\) candidate short tuples. Choose \(\varepsilon\) small enough before taking \(d\to\infty\). This genericity refers to labels when bounding an average over labels, not to conditioning on the unknown true label.

For one or two row frequency vectors, among all integer frequency tuples with total support \(>L\), the absolute sum of their Fourier coefficients \(b^{\sum v_i^\top C v_i}\) is \(\exp(-\Omega(d))\). Indeed \(C\succeq\delta I\), and \(\sum_{a\ne0}b^{\delta a^2}=O(b^\delta)\). For \(h=1,2\), bound the sum by \(\sum_{j>L}\binom{hd}{j}(C_1 b^\delta)^j\). The ratio \(eC_1hd b^\delta/L\) is \(O(d^{-\delta}\log d)\), so the geometric resulting upper bound has log at most \(-\Omega(\delta L\log d)=-\Omega(d)\). This holds for each fixed \(\rho<1/2\), without a uniform claim as \(\rho\to1/2\).

## 3. Exact bulk control at the origin

We first record bounds on the single-row density used also in the variance estimate. With \(f_0(y)=\prod_{j=1}^d f_b^{(1)}(y_j)\), where \(f_b^{(1)}\) is the scalar wrapped density, \(f,f_0\) are uniformly bounded above and away from zero, and
\[
 \|f-f_0\|_\infty=O(d b^{1+\delta})=o(1),\quad
 g(0)=1+O(d b^{q^2}),\quad
 \sum_{v\in\mathbb Z^d} b^{2v^\top C v}=1+O(db^2).             \tag{4}
\]
For \(\rho=0\) the first bound is exact with zero error and the other two are products. For \(\rho>0\), use \(v^\top C v=\delta\|v\|^2+\rho\|(I+U)v\|^2\). A proper connected support component on the cycle of length \(j\ge2\) has energy \(\ge\delta\sum v_i^2+2\rho\) by its two integer boundary terms, while a singleton has energy its integer square. For a power \(h=1\) or 2, summing activities of non-singleton components gives \(O(d b^{h(1+\delta)})\) by a geometric series in \(\sum_{a\ne0}b^{h\delta a^2}\), and full-cycle support is negligible. The total singleton activity is \(O(db^h)\). Different separated components add energies; ignoring compatibility bounds their partition by the exponential of the activity sum. Thus in comparing \(f,f_0\), the only differing frequencies contain an adjacent pair, whose summed absolute weight is obtained by marking one nonsingleton. This proves the first estimate and boundedness including positivity because \(f_0\) is uniformly bounded above and away from zero. The other estimates follow by the same partition bound with parameter \(b^{q^2}\) or power \(h=2\). The absolute Fourier sum bound also gives \(\|g-1\|_\infty=O(d b^{q^2})\), so \(G=1+o(1)\) uniformly for \(k\le C_0 d\).

For fixed \(s\), define \(B_s(A)=\prod_{i=1}^k f(A_is/q)\), where one can use the positive argument rather than its negative since \(f\) is even. Under good labels from §2,
\[
 \mathbb E_A B_s=g(0)^k+O(e^{-cd}),\qquad
 \mathbb E_A B_sB_{s'}=g(0)^{2k}+O(e^{-cd})
                                                               \tag{5}
\]
for good pairs. Indeed with one row expand the positive-Fourier density or product and use orthogonality under uniform \(A\), retaining a congruence \(\bar s v=0\) or \(\bar s v+\overline{s'}w=0\). The all-zero-residue tuple contributes exactly \(g(0)\) or \(g(0)^2\); all remaining surviving tuples must have scalar support \(>L\). Their absolute sum is exponentially small by §2. Raise the one-row bound to \(k=O(d)\), using (4), to get (5).

For use on the rare bad labels, all nonzero \(s\) satisfy uniformly
\[
 \mathbb E_A B_s^2\le\exp(o(d)).
                                                               \tag{6}
\]
Here uniform \(A_i s\) is uniform on a nonzero ideal \(J\). In the block description of §2, each coefficient of a uniform \(J_0\) ranges uniformly over a nontrivial additive subgroup of \(\mathbb Z/q\): a nonzero ideal has a nontrivial projection somewhere, and signed shifts transfer that to every coordinate. The mean of the primitive first cosine is zero on every such subgroup. For the independent product density, its **squared** value on one base block has Taylor expansion \(1+4b\sum \cos(2\pi y_j)+O(b^2)\), uniformly in that fixed-dimensional block. Thus \(\mathbb E_J f_0(A_i s/q)^2=1+O(db^2)\) (view \(A_i s\) as the uniform draw on \(J\)). Using (4) and boundedness, replacing \(f_0^2\) by \(f^2\) changes this by \(O(d b^{1+\delta})\). Multiplying over \(k\) gives (6): \(k(db^2+d b^{1+\delta})=O(1+d^{1-\delta})=o(d)\), and the estimate is uniform. The pair expectation for any two nonzero labels is bounded by the same order by Cauchy–Schwarz.

Let \(H_A=q^{-d}\sum_{s\ne0} B_s(A)\). The first and second moments of \(H_A\) are \((1-q^{-d})g(0)^k\) and its square, respectively, up to exponentially small absolute errors: insert (5) for the good labels/pairs, and use (6) times the exponentially small exceptional fractions. Hence
\[
 \|H_A-(1-q^{-d})g(0)^k\|_{L^2(A)}\le e^{-c'd}.                \tag{7}
\]
The excluded label \(0\) has exactly \(B_0=f(0)^k\). It can be much larger than the other contributions and is not included in the rare-label bound.

## 4. Supremum versus integrated distance

The Fourier coefficients of the mixture \(F_A\) are nonnegative: at \((v_i)_{i\le k}\) the weight is \(b^{\sum_i v_i^\top C v_i}\) times the indicator \(\sum_i\overline A_i(v_i\bmod q)=0\). The reference \(G\) subtracts exactly the contributions with every residue vector zero. Hence \(F_A-G\) also has only nonnegative Fourier coefficients. Its continuous Fourier series converges absolutely; by the triangle inequality
\[
 \|F_A-G\|_\infty=F_A(0)-G(0)=q^{-d}f(0)^k+H_A-g(0)^k .
\]
Now (7) gives (1). There is no assumed statistical independence among likelihoods of different labels.

For the integrated squared norm, each frequency that remains has at least one nonzero residue vector, so its survival probability over \(A\) is at most \(e^{-c_qd}\) by the ideal size argument. The sum of all **squared** weights is at most \((1+O(db^2))^k=O(1)\) by (4). Parseval proves (2). The claims for the likelihood ratio use the inequalities with \(G(0)\) and \(\inf G\): the positive supremum of \(F_A/G-1\) is at least \((F_A(0)-G(0))/G(0)\), and the absolute supremum is at most \(\|F_A-G\|_\infty/\inf G\). Both denominators tend to 1 uniformly. In particular a large pointwise spike does not imply a measurable event of comparably large probability gap.

## 5. Correlation correction to the center

For \(\rho=0\), \(f(0)=f_b^{(1)}(0)^d\) and \(f_b^{(1)}(0)=1+2b+O(b^4)\), giving \(d\log f_b^{(1)}(0)=2\beta-2\beta^2/d+O(d^{-2})\). This gives the claimed product offset.

For fixed \(\rho>0\), energy is additive on separated support components. The minimum among connected components of size at least two is \(1+\delta\), with exactly the \(2d\) adjacent signed dipoles of magnitude-one entries. For a length-2 component this follows by direct computation, including the sign at the wrap edge; other sign or magnitude choices have a fixed positive gap. The length-\(\ge3\) bound is \(1+2\delta\) or more by its two endpoint contributions. The total activity of all non-minimal nonsingletons is therefore \(o(d b^{1+\delta})\); two or more nonsingletons contribute \(O((d b^{1+\delta})^2)e^{O(db)}=o(d b^{1+\delta})\).

A configuration with exactly one minimal dipole contributes its weight \(b^{1+\delta}\) times the partition of compatible monomers. Write \(a=\sum_{m\ne0}b^{m^2}\). Ignoring any monomer incompatibility this partition is \((1+a)^d=f_0(0)\). Under the independent monomer weights, each site is occupied with probability \(a/(1+a)=O(b)\). Excluding the \(O(1)\) sites touching the dipole, and excluding adjacent occupied pairs elsewhere, costs relative \(O(b+db^2)=o(1)\) by a union bound. Thus all one-minimal-dipole configurations sum to \(2d b^{1+\delta} f_0(0)(1+o(1))\). The monomer-only partition agrees for both models; the rest of the independent partition contributes only \(O(db^2)\), negligible since \(0<\delta<1\). Consequently
\[
 \log f(0)=d\log f_b^{(1)}(0)+2d b^{1+\delta}(1+o(1))
          =2\beta+2\beta^{1+\delta}d^{-\delta}(1+o(1)).
\]
Inverting gives (3), and the exact center in (1) does not require control of all smaller corrections.

## 6. Earlier work and boundary

Rényi resolvability and the distinction of order-\(\infty\) smoothing from weaker distances are standard, for example [Pathegama–Barg, Smoothing of Binary Codes](https://arxiv.org/abs/2308.11009) and [Yu–Tan, Rényi Resolvability](https://arxiv.org/abs/1707.00810). Those results do not supply (7) for these correlated ring designs. The earlier [correlated-noise TV critical window](https://github.com/mxym/math/blob/2877b200cbe11c7a381b91f86db5b29668b94000/research/euclidean-tensor-geometry/theoretical-cryptography/ring-lwe-correlated-noise-critical-window.md) proves a window at \(\Theta(d^2)\) rows, with a squared Fourier dipole entropy correction. Here the pointwise transition is at \(\Theta(d)\) rows and the *unsquared* dipole activity is needed; the new step is the quenched pointwise profile to exponentially small additive accuracy. This is an abstract statistical theorem, not a solver or a claim about deployment parameters.
