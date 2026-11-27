# Full variance and a fixed-scale limit law for Erdős #1210

Let \(p^-(m)\) be the least prime factor of \(m>1\), with \(p^-(1)=+\infty\). For \(n\ge2\), write
\[
\begin{split}
 \mathcal M(n)&=\max_{\substack{A\subseteq[1,n)\cap\mathbb Z\\A\text{ pairwise coprime}}}
                    \sum_{a\in A}\frac1{n-a},\\
 \mathcal L(n)&=\sum_{1\le d<n}\frac{\mathbf1_{\{p^-(n-d)>d\}}}{d},\\
 \mathcal U(n)&=\sum_{16\le d<n}\frac{\mathbf1_{\{p^-(n-d)>d/(2\log d)\}}}{d}.
\end{split}
\]
The [pointwise question of Erdős](https://www.erdosproblems.com/1210) asks whether \(\mathcal M(n)\le\sum_{p<n}1/p+O(1)\) for all \(n\). [Eric Li, arXiv:2606.17955v2](https://arxiv.org/html/2606.17955v2), proved that \(\mathcal M(n)\) has normal order \(e^{-\gamma}\log\log n\), giving the Erdős bound outside an exceptional set of size \(O(N\log\log\log N/\log\log N)\). Li gave an \(O(N)\) centered second moment for a suitable truncated \(\mathcal L\) in Theorem 4.8; the untruncated bound was left as (4.3)/(4.35), and Question 4.19 asked about the limiting distribution of the centered truncation. We address both of those questions without estimating fine fixed-power two-point Buchstab asymptotics.

## Results

**Theorem 1 (untruncated second moment).** For \(F=\mathcal L,\mathcal U,\mathcal M\) and integer \(N\to\infty\),
\[
 \sum_{N<n\le 2N}\big|F(n)-e^{-\gamma}\log\log N\big|^2\ll N.
 \tag{1}
\]
In particular, the variance around the actual mean of each quantity is \(O(1)\) in the uniform dyadic probability space. For every fixed \(\varepsilon>0\),
\[
 \#\left\{n\le X:\big|\mathcal M(n)-e^{-\gamma}\log\log n\big|>
                      \varepsilon\log\log n\right\}
 \ll_\varepsilon \frac{X}{(\log\log X)^2},
 \tag{2}
\]
where finitely many small \(n\) can be discarded. The same bound \(O(X/(\log\log X)^2)\) is valid for the number of \(n\le X\) with \(\mathcal M(n)>\sum_{p<n}1/p\).

**Theorem 2 (truncated limit law).** Put \(V(t)=\prod_{p\le t}(1-1/p)\). Independently for each prime \(p\), sample a uniform residue \(R_p\bmod p\), and write
\[
 J_d=\mathbf1_{\{R_p\ne d\bmod p\text{ for all }p\le d\}},
 \qquad W=\sum_{d\ge 2}\frac{J_d-V(d)}{d}.
 \tag{3}
\]
The series defining \(W\) converges in \(L^2\), with mean zero and \(\operatorname{Var}(W)\ge(5/36)^2\). For **every** cutoff \(Y=Y_N\) with \(Y_N\to\infty\) and \(\log Y_N/\log N\to0\), the law under uniform sampling of \(N<n\le2N\) of
\[
 W_N(n)=\sum_{1\le d\le Y_N}
             \frac{\mathbf1_{\{p^-(n-d)>d\}}-V(d)}{d}
 \tag{4}
\]
converges to the law of \(W\), and the first two moments also converge. The \(d=1\) term is zero for large \(N\). The assertion does not identify the untruncated \(O(1)\)-scale limiting law, and (1) does not imply the conjectured bound at every \(n\).

## 1. Uniform arithmetic-to-residue comparison

Allow either threshold \(g(d)=d\) for \(d\ge2\), or \(g(d)=d/(2\log d)\) for \(d\ge16\). Both are increasing; in either case \(2\le g(d)\le d\), and \(\log g(d)\asymp\log d\) on the given domain. Define
\[
 I_d(n)=\mathbf1_{\{p^-(n-d)>g(d)\}},\quad
 J_d^{(g)}=\mathbf1_{\{R_p\ne d\bmod p\text{ for all }p\le g(d)\}},\quad
 v_d=V(g(d)).
\]
Throughout the comparison \(d\le B\le N^{\beta_0}<N\), with an absolute fixed \(0<\beta_0<1/10\). Use \(\mathbb E_N\) for averaging over the \(N\) integers \(N<n\le2N\), and \(\mathbb E_*\) for the independent-residue model. For any one or two indices \(d,e\le B\), with repetition allowed, we have
\[
 \mathbb E_N I_d I_e
 =\mathbb E_* J_d^{(g)}J_e^{(g)}
       \left(1+O\!\left(e^{-c\log N/\log B}\right)\right)
       + O(N^{-2/3}\log N).
 \tag{5}
\]
Taking \(e=d\) includes the one-index comparison.

To verify (5), for each prime up to the greater threshold exclude one or two residue classes \(d,e\bmod p\) for \(n\), according to which thresholds include the prime. If these exhaust a prime's residue classes, both probabilities are zero identically (in particular handle the parity obstruction at \(p=2\) exactly). Otherwise write \(\nu_p<p\) for the number of excluded residues, with \(0\le\nu_p\le2\). For squarefree \(\ell\), the simultaneous excluded-class condition has \(\nu(\ell)=\prod_{p\mid\ell}\nu_p\) solutions modulo \(\ell\), by CRT. Its count in the dyadic sample is \(N\nu(\ell)/\ell+O(\nu(\ell))\).

Apply the standard beta-sieve fundamental lemma with sifting cutoff at most \(B\) and distribution level \(D=\lfloor N^{1/3}\rfloor\). Its dimension bound is uniform:
\(\prod_{w<p\le z}(1-\nu_p/p)^{-1}\ll(\log z/\log w)^2\) for \(2\le w\le z\), by Mertens, \(\nu_p\le2\) for odd \(p\), and the finite factor at \(2\). The version with bounded combinatorial weights gives relative error \(O(e^{-c\log D/\log B})\) and total absolute remainder bounded by \(\sum_{\ell\le D}2^{\omega(\ell)}\ll D\log(2D)\). The last estimate follows from \(2^{\omega(\ell)}\le\tau(\ell)\), and summing divisors. This yields (5) after division by \(N\), with the product \(\prod_p(1-\nu_p/p)\) exactly the model joint probability. For the fundamental lemma see Friedlander–Iwaniec, *Opera de Cribro*, Ch. 6; [Tao, Lemma 17 and Corollary 19](https://terrytao.wordpress.com/2015/01/21/254a-notes-4-some-sieve-theory/); or [Li, proof of Lemma 4.4, (4.19)](https://arxiv.org/html/2606.17955v2). Use the lemma in its relative-error form with a parameter depending on this particular \(B\); we need no error tending to zero at a fixed-power cutoff.

## 2. Signed residue-model variance on any one band

Write \(j_d=J_d^{(g)}\). For \(d<e\) with \(h=e-d\), independence across primes gives
\[
 \mathbb E_* j_dj_e=v_dv_e C_{g(d)}(h),\qquad
 C_y(h)=\prod_{p\le y}
    \left(1-\frac1{(p-1)^2}+\frac{p}{(p-1)^2}\mathbf1_{\{p\mid h\}}\right).
 \tag{6}
\]
Indeed, at common primes the allowed proportion is \(1-1/p\) when \(p\mid h\) and \(1-2/p\) otherwise, before dividing by \((1-1/p)^2\). At primes belonging only to the greater threshold the ratio is \(1\).

We recall the finite signed-cancellation argument of [Li, Lemma 4.6](https://arxiv.org/html/2606.17955v2); it applies equally with \(y=g(d)\). Expand \(C_y(h)=\sum_{q\mid \prod_{p\le y}p} a_y(q)\mathbf1_{\{q\mid h\}}\). All \(a_y(q)\ge0\). The sum of \(a_y(q)/q\) is \(1\) because each prime's contribution to it equals \(1\); their unweighted sum is \(C_y(0)=1/V(y)\ll\log(2y)\). Thus
\[
 \left|\sum_{1\le h\le H}(C_y(h)-1)\right|
       \le \sum_q a_y(q)\ll\log(2y)
 \tag{7}
\]
for every integer \(H\ge0\), from the error at most one in replacing \(\lfloor H/q\rfloor\) by \(H/q\).

For a band \(A<d\le B\), the off-diagonal part of the model variance of \(\sum j_d/d\) consists of rows with \(d\) fixed. The weights \(v_e/e\) are nonincreasing in \(e\), so summing by parts in \(h\), using (7), gives the signed row bound
\[
 \left|\sum_{d<e\le B}\frac{v_e}{e}\{C_{g(d)}(e-d)-1\}\right|
 \ll \log(2g(d))\frac{v_{d+1}}{d+1}\ll \frac1d.
 \tag{8}
\]
The row is multiplied by \(v_d/d\ll1/(d\log d)\), which makes the outer sum absolutely convergent over rows. The diagonal is bounded by \(\sum_{d>A} v_d/d^2\). Consequently, uniformly in \(B>A\ge2\),
\[
 \operatorname{Var}_*\left(\sum_{A<d\le B}j_d/d\right)\ll 1/A .
 \tag{9}
\]
In particular this bound is not obtained by taking absolute values of individual covariances; the signed row sum matters.

## 3. Summing whole logarithmic bands, not a single worst relative error

Consider now \(2\le A<B\le \min(A^2,N^{\beta_0})\), using only \(d\) in the domain of \(g\). Let \(S(n)=\sum_{A<d\le B}(I_d(n)-v_d)/d\), and put \(T=\sum_{A<d\le B}j_d/d\). Because \(B\le A^2\),
\[
 \mathbb E_*T\ll\sum_{A<d\le A^2}\frac1{d\log d}\ll1,\qquad
 \mathbb E_*T^2\ll1
\]
by (9). Expand \(S^2\) and compare its mean to the centered model moment. Each joint probability has the error in (5), and the single probabilities in the centering terms do as well. The relative errors summed over the band are bounded by
\(O(e^{-c\log N/\log B})(\mathbb E_*T^2+(\mathbb E_*T)^2)=O(e^{-c\log N/\log B})\).
The absolute errors are \(O(N^{-2/3}\log N)(\sum_{d\le B}1/d)^2=O(N^{-2/3}(\log N)^3)\). With (9) and a square root, we obtain
\[
 \|S\|_{L^2(\mathbb E_N)} \ll A^{-1/2} +e^{-c'\log N/\log B}+N^{-1/4}.
 \tag{10}
\]

For an interval of indices \(D_0<d\le Y\le N^{\beta_0}\), with \(D_0\ge4\), set \(B_0=Y\), \(B_{j+1}=\sqrt{B_j}\) and stop once \(B_j\le D_0\). Include the last partial band above \(D_0\), if needed. All bands satisfy \(B\le A^2\), and their number is \(O(1+\log\log N)\). Their contributions of \(A^{-1/2}\) sum to \(O(D_0^{-1/2})\): working backwards from the last band, the lower cutoffs grow by successive squaring. Their exponential terms sum to
\[
 \sum_{j\ge0} \exp\!\left(-c'2^j\log N/\log Y\right)
 \ll \exp(-c'\log N/\log Y).
\]
The constants are uniform since \(\log N/\log Y\ge1/\beta_0\). **Minkowski's inequality** therefore gives the useful estimate
\[
 \left\|\sum_{D_0<d\le Y}\frac{I_d(n)-v_d}{d}\right\|_{L^2(\mathbb E_N)}
 \ll D_0^{-1/2}+\exp(-c'\log N/\log Y)
       +(1+\log\log N)N^{-1/4}.
 \tag{11}
\]
This avoids multiplying the largest sieve relative error by the total unbounded mass of all the small-distance bands. It also avoids estimating the cross-band covariances directly.

## 4. Full variance and the extremal quantity

Use (11) from a fixed \(D_0\) up to \(Y=N^{\beta_0}\); the omitted finite initial block is bounded. This bounds the centered low part in \(L^2\) by \(O(1)\). The **entire high part** \(N^{\beta_0}<d<n\) is pointwise \(O(1)\). Indeed, on \(D<d\le2D\) any counted \(n-d\) avoids primes up to \(D^{1/3}\) once \(D\) is large, for either threshold. By the uniform interval upper sieve, e.g. [Li, Lemma 2.3](https://arxiv.org/html/2606.17955v2), the number of possible \(d\) is \(O(D/\log D)\); this holds even if we drop the cutoff \(d<n\) in the divisibility count. The weighted contribution is \(O(1/\log D)\). Summing the dyadic bands from \(N^{\beta_0}\) to \(2N\) costs
\[
 O\!\left(1+\log\frac{\log(2N)}{\log(N^{\beta_0})}\right)=O_{\beta_0}(1).
\]
In particular mere boundedness of the high part suffices here; neither a prime correlation estimate nor an asymptotic formula in the fixed-power transition range is needed for bounded variance.

The deterministic center of the low part is \(e^{-\gamma}\log\log N+O(1)\). Indeed, the quantitative Mertens product gives \(V(t)=e^{-\gamma}/\log t+O(1/(\log t)^2)\), and for either \(g\) we have
\[
 V(g(d))=\frac{e^{-\gamma}}{\log d}
       +O\!\left(\frac{1+\log\log(3d)}{(\log(2d))^2}\right).
\]
The error is summable against \(1/d\), and \(\log\log(N^{\beta_0})=\log\log N+O_{\beta_0}(1)\). This proves (1) for \(\mathcal L,\mathcal U\).

For completeness, Li's sandwich \( \mathcal L(n)\le\mathcal M(n)\le C_0+\mathcal U(n)\) follows by two short arguments. If \(d,e\) are distinct self-rough distances then a common prime factor of \(n-d,n-e\) would divide \(d-e\) but would exceed \(\max(d,e)\), a contradiction. For the upper bound, charge any selected \(a>1\) with \(d=n-a\ge16\) and a prime divisor \(p\le d/(2\log d)\) to \(1/(p\log p)\), which pays at least \(1/d\). No prime is charged twice in a pairwise coprime set, and \(\sum_p1/(p\log p)\) converges. Elements with no such prime are counted by \(\mathcal U\); the other finite-weight exceptions cost \(O(1)\). Thus (1) for \(\mathcal M\) follows by bounding the centered value by the two endpoints in \(L^2\). Chebyshev and summation over dyadic intervals now give (2), using \(\log\log n=\log\log N+O(1/\log N)\) in \((N,2N]\); intervals below \(\sqrt X\) may be discarded. Mertens's reciprocal-prime estimate and \(e^{-\gamma}<1\) give the sharper exceptional count for the Erdős benchmark.

## 5. The fixed-scale limit law

Use \(g(d)=d\). The model variance tail (9) makes the centered series (3) a Cauchy sequence in \(L^2\). For each fixed \(D_0\), the law of the terms \(d\le D_0\) averaged over the dyadic interval tends to the model law by exact CRT periodicity, including convergence of its first and second moments. For the remaining arithmetic tail up to \(Y_N=N^{o(1)}\), (11) gives \(\limsup_{N\to\infty}\|\text{tail}\|_2\ll D_0^{-1/2}\), since \(\log N/\log Y_N\to\infty\). The model tail has the same bound by (9). First let \(N\to\infty\), then \(D_0\to\infty\). The triangle inequality, tested against bounded Lipschitz functions, gives weak convergence. The \(L^2\) bounds for the approximation errors and uniform boundedness of the \(L^2\) norms give convergence of first and second moments as well.

The law is nondegenerate: conditional on \(R_2=0\), the conditional means of \((J_d-V(d))/d\) are \(-V(d)/d\) for even \(d\) and \(+V(d)/d\) for odd \(d\). The sign reverses for \(R_2=1\). The series of conditional means converges by alternation (or by the established \(L^2\) convergence). By pairing each even index with the next odd one, the magnitude in the \(R_2=0\) case is at least the first pair's difference \(V(2)/2-V(3)/3=5/36\), and the conditional variance inequality gives the stated lower bound. Equivalently, the limiting variance can be computed by the diagonal series plus twice the iterated row sums in (8), taking \(B\to\infty\) first within each row.

## Finite checks

Run `node verify_erdos1210_variance_law.js`. It checks exact CRT covariance formulas, the finite singular-series mean and signed error, the parity projection, integer endpoint partitioning at dyadic log-scales, and the deterministic coprime-set sandwich on small inputs. The analytic estimates are proved above and are not inferred from computations.
