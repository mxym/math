# An actual one-sided estimate for a balanced triple part of the adaptive residual

Use the \(K_P\)-weighted mixed carrier \(W\), its genuine matched reference \(R_N\), \(c_{\rm sf}(m)=\mu^2(m)(W(N-m)-R_N(m))\), and the actual asymmetric Vaughan coefficient \(\mathcal B(m)\) from [AsymmetricVaughanSmoothResidual.md](AsymmetricVaughanSmoothResidual.md). Write \(Q_0=x^q,\ .618<q<.625,\ H(m)=m/Q_0,\ U=\sqrt x,\ V=Q_0/U\), and \(W_{\rm tot}=\sum_n W(n)\). The shifted variable \(m\) lies in \(J=[x,1.5x)\). Let \(b=.3685\), and let \(\mathcal T_b\) be the actual squarefree \(m=p_1p_2p_3\in J\) with all three primes \(\le x^b\).

Then for every sufficiently large fixed \(s\) in the carrier construction,
\[
       \sum_{m\in\mathcal T_b}\mathcal B(m)c_{\rm sf}(m)
                           \le .984\,\mathfrak S(N)W_{\rm tot}
                               +o_s(\mathfrak S(N)W_{\rm tot}),
 \tag{1}
\]
uniformly in the fixed even target. This is a pointwise one-sided estimate on a nonshrinking real part of the adaptive residual. It is not a bound on the complete positive triple chamber or a positivity conclusion for actual primes.

## 1. Exact rank-three coefficient

On a squarefree triple with all prime factors at most \(\sqrt x\), let \(j=\#\{p_i\ge H(m)\}\). In (3) of the asymmetric note, no prime \(d\) is \(>U\). A contributing \(k\) is thus a single prime, and its bracket is zero unless \(V<k<H\), in which case it is \(\log k\) and \(d=m/k>Q_0>U\). Here \(d\) is a product of two distinct primes. Its full product exceeds \(Q_0/k\) since \(m>Q_0\), so the short coefficient sum on \(d\) is \(1-2\) times the number of its prime factors at most \(Q_0/k\), i.e. \(1-2j\): a prime factor of \(d\) is \(\le Q_0/k\) exactly when the other is \(\ge H\). Hence \(b(d;k)=2(1-j)\), and
\[
             \mathcal B(m)=2(1-j)\sum_{V<p_i<H(m)}\log p_i .
 \tag{2}
\]
Weak equality faces use the indicated inequalities. On \(\mathcal T_b\), each \(p_i\ge x^{a}\) where \(a=1-2b=.263\), since \(m\ge x\); also \(p_i<H\) and \(p_i>V\). Thus \(j=0\), and \(\mathcal B=2\log m\) exactly in the wedge.

## 2. One-sided actual estimate

Set \(h=b-a=.1055\) and \(f(\alpha)=\max((\alpha-a)/h-1/3,0)\) for \(\alpha\in[a,b]\), zero outside. For every triple in the wedge \(\sum_i f(\log_x p_i)\ge1\), since \(\sum_i\log_xp_i\ge1\) and \(1-3a=2h\). Also \(\int_a^b f(\alpha)\,d\alpha=2h/9\). The upper marker cost contains no replacement of a prime factor by a model integer: for an actual marked prime \(p\) of exponent \(\alpha\), write \(m=p k\) and majorize the remaining two-factor condition by \(P^-(k)\ge z_p=(Q_0/p)^{1/2}\). This is valid since \(\log_x z_p\le(.625-a)/2<a\).

For \(p\nmid N\) the nonnegative weighted sequence \(W(N-p k)\) has Type I counts in \(d\mid k\) with population \(W_{\rm tot}g_N(p)\), \(g_N(p)=1/\varphi(p)\), and local \(g_{N,p}(d)=g_N(pd)/g_N(p)\) on squarefree \(d\). For a prime \(l<z_p<p\), this is \(1/(l-1)\) if \(l\nmid N\), and zero if \(l\mid N\). Thus (uniformly in \(p,N\)) the dimension-one sieve product is
\[
 \prod_{l<z_p}(1-g_{N,p}(l))
       =(1+o(1))\,\frac{e^{-\gamma_{\rm E}}\,\mathfrak S(N)}
                             {\log z_p},
\]
where the tail of the \(N\)-dependent singular correction costs \(O((\log x)/z_p)\), and the local product condition is bounded uniformly by the unrestricted odd-prime product with \(g(l)=1/(l-1)\). If \(p\mid N\), the actual weight is identically zero when \(p\mid m\): then \(p\mid(N-m)\), but no prime dividing the carrier exceeds its .25 macro band, whereas \(p\ge x^{.263}\). The reference is nonnegative, so nonreduced marks do not hurt this upper bound.

Use the ordinary dimension-one Rosser–Iwaniec upper sieve with \(\log(Q_0/p)/\log z_p=2\), whose main term has \(F(2)=e^{\gamma_{\rm E}}\); see, e.g., the dimension-one theorem stated and used in [Matomäki, author's version, Lemma 2](https://users.utu.fi/ksmato/wp-content/uploads/sites/1432/2025/04/Goldbach_k2pl2p1.pdf). The prime log \(\log m=L+O(1)\) gives the factor \(2L+O(1)\) in the weighted triple coefficient. Sieve error terms sum to arbitrary log savings at modulus \(r=pd\le Q_0\), by (10) of the flexible-carrier theorem and its divisor-moment version: at most \(\tau(r)\) possible marked primes \(p\) per \(r\), all multipliers at most \(O(L)\) and standard upper weights bounded by 1. We can drop squarefreeness in this positive upper count because it only enlarges the count. The uniform dimension-one main-term error is \(o(1)\) relative, and the actual comparison is thus
\[
 \frac{\sum_{m\in\mathcal T_b}2\log m\,W(N-m)}
      {\mathfrak S(N)W_{\rm tot}}
  \le 4\int_a^b \frac{f(\alpha)}{\alpha(q-\alpha)}\,d\alpha+o_s(1)
  \le \frac{(8/9)(b-a)}{b(.618-b)}+o_s(1).
 \tag{3}
\]
Here the prime reciprocal measure is \(d\alpha/\alpha\) by PNT, using \(1/\varphi(p)=1/p+O(p^{-2})\), and the last denominator lower bound follows from concavity of \(\alpha(.618-\alpha)\), whose minimum on \([a,b]\) is at \(b\) for these stated values. The asymptotic error is relative to the genuine \(W_{\rm tot}\asymp_{s,\eta,C_*}x/L\), not to an unrestricted unweighted sequence.

## 3. Matched-reference lower bound

Keep the **same** subpower cutoff \(Z\), normalization \(V_0\) and mesh multipliers \(a_j\) of \(R_N(m)=a_j1_{P^-(N-m)\ge Z}/V_0\) on \(J_j\). Put \(b_1=.3684<b\). For ordered first two actual prime exponents \(\alpha,\beta\) with
\[
      \alpha,\ \beta,\ 1-\alpha-\beta\le b_1 ,
\]
each exponent is \(\ge1-2b_1>.263\). For every \(m\in J\), the available third prime interval \(J_j/(p_1p_2)\) has exponent \(1-\alpha-\beta+O(1/L)<b\), with the fixed buffer \(b-b_1>0\), and is inside the desired range whenever the third slot is prime. The reference on that slot, for fixed \(a'=p_1p_2\), is on the **actual arithmetic expression** \(N-a'p_3\). Expand its subpower rough mask by the same even/odd Bonferroni products as in the carrier proof. Every relevant divisor is \(x^{o(1)}\), and \(p_1,p_2>Z\), so each individual prime progression is reduced unless a divisor contains a prime dividing \(N\), in which case it contributes no \(p_3>Z\). Apply ordinary maximal prime BV at \(X'=x/a'\), at least \(x^{1-2b_1}\), then partial summation for the factor \(\log m/\log p_3\). For each fixed \(a'\) the aggregate error for these moduli is \(O_B((x/a')L^{-B})\), uniformly also in the mesh endpoint, by the BV maximal residue bound and the truncated Euler-product tails. The Bonferroni model product divided by \(V_0\) is \(\mathfrak S(N)(1+O(L^C/Z))\), uniformly in \(N\). The sum of reciprocal \(a'\) over the two prime slots is bounded, and the fixed log-power number of mesh intervals is absorbed with an extra reserve. Repeated prime slots cost a power saving by counting integers divisible by a prime square \(\ge x^{2(1-2b_1)}\); prime-factor representations per such integer are at most a fixed divisor power, and \(R_N\) is log-power bounded.

The two remaining prime reciprocal sums tend to the integral in \(\alpha,\beta\), by PNT and box approximation on the compact simplex. Also \(\sum_j a_j|J_j|=W_{\rm tot}\) exactly, and \(\log m/\log p_3=(1-\alpha-\beta)^{-1}+o(1)\) uniformly there. Ordered triple representations cost a factor \(3!\); restricting the ordered tuples to the buffered simplex only decreases their nonnegative reference sum, regardless of the (O(1/\log x)) difference in the actual third exponent. Thus
\[
 \frac{\sum_{m\in\mathcal T_b}2\log m\,R_N(m)}
      {\mathfrak S(N)W_{\rm tot}}
 \ge \frac{2}{6}\int_{\alpha,\beta,1-\alpha-\beta\le b_1}
        \frac{d\alpha\,d\beta}{\alpha\beta(1-\alpha-\beta)}
      +o_s(1)
 \ge \frac{(3b_1-1)^2}{6b_1^3}+o_s(1),
 \tag{4}
\]
where the coordinate simplex area is \((3b_1-1)^2/2\). One can also obtain the asymptotic with \(b\) in place of \(b_1\) by sandwiching from either side with fixed buffers tending to zero after \(x\); only the lower bound is needed. All \(m\) in the wedge are squarefree, so these are exactly the reference terms in \(c_{\rm sf}\).

Finally the two rational expressions in (3) and (4) give
\[
 \frac{(8/9)(.1055)}{.3685(.618-.3685)}
     -\frac{(.1052)^2}{6(.3684)^3}<.984 .
\]
This proves (1) with the stated **prime-reference** unit \(\mathfrak S(N)W_{\rm tot}\). Because the carrier has narrowing-dependent mass, the estimate does not say that the complete weighted polynomial-marker discrepancy, normalized by \(M_N\) independently of the carrier, is small.

## 4. Why the same one-marker bound is insufficient for the whole chamber

In the full positive chamber of (2) take the limiting \(b=1-q\in(.375,.382)\), \(a=1-2b\), \(h=b-a\). The \(O(1/L)\) change in the actual cutoff \(H(m)\) disappears in the fixed-region limiting integrals. A nonnegative marker cover for this *specific proof method* is any function \(f\ge0\) with \(\sum_i f(\alpha_i)\ge1\) whenever \(\alpha_i\in[a,b]\) and \(\sum_i\alpha_i=1\). In the coordinates \(s_i=(b-\alpha_i)/h\), this is \(\sum_i g(s_i)\ge1\) on the unit simplex. Let \(Y\) be uniform on \([0,1/3]\); the tuple \((Y,Y+1/3,2/3-2Y)\) has sum 1, and after permutation all three marginals are uniform on \([0,2/3]\). Taking its expectation gives \(\int_0^1g(s)\,ds\ge2/9\). Therefore the specific upper formula in (3) formed by summing one nonnegative marked direct upper sieve has cost
\[
         4\int_a^b\frac{f(\alpha)}{\alpha(q-\alpha)}d\alpha
             \ge \frac{(8/9)(b-a)}{(q/2)^2}>1.1377 .
\]
The full exact matched-reference limiting mass in that chamber is at most \((3b-1)^2/[6(1-2b)b^2]<.108\), since the least product \(\alpha\beta(1-\alpha-\beta)\) on the simplex is at its vertices \((1-2b,b,b)\). So even with exact subtraction these **particular one-marker upper formulas** cannot certify the full positive chamber below one prime-reference unit. This is neither a lower bound on the real signed discrepancy nor a barrier for every paired or signed switching method.

The still uncontrolled contributions include the positive triples in the outer band \(x^{.3685}<P^+(m)<H(m)\), the negative \(j=2\) coefficient against the sign-changing \(c_{\rm sf}\), and higher-rank \(\Omega(m)\ge4\) on the surviving smooth support. For two simultaneous prime marks in the full positive triple chamber, the complementary pair modulus \(p_i p_j=m/p_k\) is \(>Q_0\) identically. This is the concrete missing progressions/switching input; the one-marker estimate does not supply it. No Goldbach conclusion is asserted.

[Arneth's September/October 2026 Goldbach program](https://zenodo.org/records/23215269) also singles out balanced few-prime configurations in a parity-sensitive residual. The estimate here concerns the literal coefficient (2), the particular weighted comparison and the stated one-marker integral. It neither evaluates that other program's signed operator nor resolves the whole balanced region here.
