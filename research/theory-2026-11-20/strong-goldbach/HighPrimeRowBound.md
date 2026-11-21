# Unconditional control of the top prime rows in the one-sign Goldbach criterion

This is a fixed-target bound for **actual** shifted primes. It narrows, but does not solve, the remaining arithmetic hypothesis of [SinglePrimeRoughRowCriterion.md](SinglePrimeRoughRowCriterion.md).

Retain x=N/2, I=(x/2,x], L=log x, M_N=S(N)x/(2L), a(n), b(n), w(n), z, y, J, s and ε=e^(−s/2) from that note. Put R_hi(α) equal to its signed R(N) with the extra condition r≥x^α on the prime row, and R_lo(α)=R(N)−R_hi(α). Fix any 1/4<α<1/3, and fix s sufficiently large that α<1/3−2ε and 1−2α<1/2−(s+2)ε. Then uniformly in even N,

    R_hi(α) ≤ [3 log((1−α)/(2α)) + 9(1/3−α)²/(4α)
                + O(ε) + o_{s,α}(1)] M_N − T_{a,2}(N),              (8)

where T_{a,2} is a nonnegative true shifted-prime weight specified below and may simply be dropped. In particular, at α=4/15 the constant before O(ε) is \(3\log(11/8)+3/80<0.993\). For some sufficiently large fixed s, the sole additional hypothesis

    R_lo(4/15) ≤ 0.003 M_N  for every sufficiently large even N

would imply a positive multiple of M_N/(log N) actual prime pairs at every sufficiently large even N. A less aggressive cutoff, α=11/40=.275, leaves substantially more margin for the same one-sided bound: its displayed constant is <.857, so \(R_{\rm lo}(11/40)\le0.10 M_N\) also suffices with appropriate fixed s. Neither of these low-row inequalities is proved here.

## 1. Exact signs in the high rows

If \(r\ge x^\alpha\), then n=rv∈I and \(P^-(v)\ge r\) imply Ω(v)≤2, since \(r^4>x\). If v is prime, then \(\log_x v\ge1-\log_x r-O(1/L)>1/2\), so \(\omega_J(v)=0\). The weight is \(a(rv)-b(rv)\).

Otherwise \(v=qu\), \(r\le q\le u\), all prime. Both q,u satisfy \(u\le x^{1-2\alpha}\), below the upper marker cutoff by the choice of s. If there is no J marker, both q,u≤x^(1/3+5ε). Consequently \(r>(x/2)x^{-2/3-10\varepsilon}=\frac12x^{1/3-10\varepsilon}\): this is a strip of width \(O(\varepsilon)+O(1/L)\) near 1/3. Its positive actual weight is \(O(\varepsilon)+o(1)\) times M_N by the two-form sieve of §1 of the criterion, fixing r,q and bounding u; the negative b part can be discarded. One J marker gives zero exactly. Two distinct J markers yield \(-a(rv)+b(rv)\); define \(T_{a,2}(N)\) to be the sum of a over precisely this last sector, counting each n once through its unique least factor r. Repeated factors cause no issue for the sign (ω_J counts only distinct factors) and can independently be disposed of in all main-term evaluations at cost \(O(x^{1-\alpha}L)\), since their repeated prime is at least \(x^\alpha\).

## 2. Reference for prime products

For any fixed product h of one or two primes each ≥x^α and with Y=x/h≫x^α, the argument for (4) of the criterion, now in the last variable, gives uniformly

    Σ_{Y/2<v≤Y, v prime} b(hv)
               =(1+o_{s,α}(1)) S(N)Y/(2 log Y).                    (9)

Indeed all divisors d in the Bonferroni expansion of the subpower cutoff \(P^-(N-hv)\ge Z\) have \(d\le (1+Z)^{O(L^{1/4})}=x^{o(1)}\) and so are coprime to h. The excluded class is \(h^{-1}N\bmod d\). For \((d,N)=1\), ordinary Bombieri–Vinogradov at scale Y against the maximal reduced residue supplies the error \(O(Y/L^B)\) for arbitrarily large fixed B, uniformly in h and N. A nonreduced class cannot contain any prime v∼Y greater than d. The rank tail and local factor after division by V₀ are the same as for (4); this remains true if h shares a *large* prime with N since all those primes exceed the sieve product divisors. The missing \(p\ge Z\) factors in S(N) are uniformly \(1+o(1)\).

For semiprime ha with h=r in the high row, this gives \(M_N\int_{\alpha}^{1/3-2\varepsilon} dt/[t(1-t)]+o(M_N)\), using prime reciprocals and \(\log(x/r)=(1-t)L\).

For the two-marker ternaries, upper bound the b-mass by summing first over r and q with \(x^\alpha\le r\le x^{1/3}\), \(x^{1/3}\le q\le\sqrt{x/r}\), and then use all primes u∈(x/(2rq),x/(rq)] instead of enforcing \(u\ge q\) or the J cutoff in the inner sum. The new last scale is always at least q≥x^(1/3), so (9) applies. Partial summation of the reciprocal prime sums, or fixed mesh Riemann sums on the closed logarithmic region, gives normalized limsup at most

    ∫_{α}^{1/3} ∫_{1/3}^{(1-t)/2} du dt/[t u(1−t−u)].

The denominator factors have t≥α and u,1−t−u≥1/3. The triangular area is \((1/3-\alpha)^2/4\), proving the second term in (8). The density is bounded on the displayed compact region, so open or closed edges have the same limit.

## 3. Factor 4 on the semiprime-product sequence, not on each fixed r

Let A be the unweighted count of distinct-prime semiprimes n=rv∈I with \(x^\alpha\le r<z\), v prime, where necessarily r<v and the factor roles are in disjoint intervals. Ordinary prime counting in the v variable and reciprocal summation over r give

    A=(1+o(1)) x/(2L) · ∫_{α}^{1/3−2ε} dt/[t(1−t)].

To count the **reflected prime condition** \(N-n\) on this sequence, use [Liu–Park–Song, Theorem 3.2](https://link.springer.com/article/10.1007/s40993-017-0089-3#Sec3), the ordinary Bombieri–Vinogradov theorem for products of distinct primes on restricted factor intervals (based on [Bombieri–Friedlander–Iwaniec, equation (1.5)](https://archive.ymsc.tsinghua.edu.cn/pacm_download/117/6385-11511_2006_Article_BF02399204.pdf)). The smaller factor lies in the displayed single interval; the larger can be restricted to [\(x/(2z),x\)] with no effect on I. The two intervals are separated by a fixed power. Theorem 3.2 measures discrepancies against the coprime total in reduced residues, with ordinary unsigned absolute values and no arithmetic filter on the factors. It is applied to the two prefix endpoints x and x/2; rewrite the same factor intervals as powers of the respective endpoints, so the theorem uses u=1 in each application. Its interval cutoffs are uniform in this separated compact power range (the short dyadic blocks in its proof need only the uniform Siegel–Walfisz estimate for interval-restricted prime indicators). The identical assertion follows by applying the separated bilinear estimate to dyadic blocks and Mellin-separating a log-power smoothed product endpoint. The change from a hard endpoint then costs \(O(\Delta x L^{O(1)}+x^{1/2-\tau+o(1)})\) in summed congruence discrepancies for transition width \(\Delta=L^{-C}\): our convolution is bounded by one near each endpoint, and a progression has at most \(O(\Delta x/q+1)\) terms in the transition. Thus there is no moving-endpoint loss in this application.

Consequently we have distribution up to \(x^{1/2-\tau}\) for any fixed τ>0. Divisor-weighted errors follow by Cauchy–Schwarz as in (3) of the criterion. In this use only moduli coprime to N are required. For each modulus q, the semiprime coprime count differs from A by at most \(x\sum_{\ell|q,\ell\ge x^\alpha}1/\ell\), since all prime factors of the sequence exceed \(x^\alpha\). After division by φ(q) and summing with any fixed divisor power, this replaces the coprime total by A at arbitrary log-power precision.

Now apply the dimension-one optimized Selberg square supported on d≤D=x^(1/4−τ/2), squarefree and coprime to 2N, to the condition \(N-n\) prime. Each such prime is >D, the local density on a sieved prime \(\ell\nmid 2N\) is \(1/(\ell-1)\), and the quadratic normalization is

    G_N(D)=Σ_{d≤D,(d,2N)=1} μ²(d)∏_{\ell|d}(\ell−2)^−1
          = (log D)/S(N) + O((log log(3N))²).

For the normalization, factor its Dirichlet series as \(\zeta(1+u)K_N(u)\). For \(\ell\nmid 2N\) the nonconstant local coefficients of K_N are \(2/[\ell(\ell-2)]\) at ℓ and \(-1/[\ell(\ell-2)]\) at ℓ²; for \(\ell\mid2N\) the coefficient is \(-1/\ell\) at ℓ. Hence \(K_N(0)=1/S(N)\), the sum of absolute coefficients is \(O(\log\log(3N))\), and their log-weighted sum is \(O((\log\log(3N))^2)\) (split \(\ell\mid N\) at \(\log N\) and use Mertens below). Convolution with the harmonic sum gives the display, including its uniform error. Standard Selberg diagonalization bounds its coefficients by a fixed divisor power, so the progression errors above are permissible after the square is expanded through D². The unweighted true reflected-prime count is at most \(A/G_N(D)+o(x/L^2)\). Multiplying by \(\log N=(1+o(1))L\) and letting fixed τ decrease yields

    Σ_{high semiprimes} a(n) ≤ (4+o(1)) M_N
                          ∫_{α}^{1/3−2ε} dt/[t(1−t)]

in the normalized limsup sense. The 4 comes from \(\log D\to L/4\) at the **full product scale** x; no two-form upper sieve with the shorter log-scale \(\log(x/r)\) was used to get this numerical constant.

Subtracting (9) leaves the coefficient 3 on this part. Extending its positive integral to 1/3 gives \(3\log((1-\alpha)/(2\alpha))\). Combine with the ternary signs and estimates of §§1–2 to prove (8).

## 4. Choosing the margins

The bound \(3\log(11/8)+3/80<993/1000\) can be certified by the first eight terms of \(2\sum_{j\ge0}(3/19)^{2j+1}/(2j+1)\), with tail at most \(2(3/19)^{17}/[17(1-(3/19)^2)]\). The same calculation with \((29/22-1)/(29/22+1)=7/51\) certifies the stated .857 bound at \(11/40\).

Use the full inequality (7) in the criterion, not just its convenient sufficient threshold R≤M_N/2. We may fix s sufficiently large that the sum of the constant parts of (2), (5) and the O(ε) in (8) is smaller than .001 M_N: all decay as \(s\to\infty\) with \(\varepsilon=e^{-s/2}\). Then take N large enough that the accumulated little-o contributions and the loss in (4) are less than .001 M_N. At α=4/15 the high bound plus the posited .003 low bound then leaves at least .002 M_N for genuine shifted weight on prime n (even after discarding \(T_{a,2}\)). The claim remains conditional on that explicit low-row estimate. The exact estimate (8) itself is unconditional and independent of any exceptional-zero hypothesis.

## Independent review and recent-work comparison (21 November 2026)

Checked the product-scale factor 4 using the [restricted-factor Bombieri–Vinogradov theorem](https://link.springer.com/article/10.1007/s40993-017-0089-3#Sec3) at both endpoints, not a sieve conditional on one small prime. Checked its residue normalization, the coprime-total correction, the triangular two-marker integral and the strict numerical margins. The lower rows remain open.

The separate July–21 November pass checked [Salazar v1](https://arxiv.org/abs/2611.10059v1) and [Li–Liu v2](https://arxiv.org/abs/2606.05224v2) for positive covers and sieve losses. The [October SRBRD technical program](https://amral.evemisslab.com/en/goldbach/srbrd/) reports its own Buchstab row-flow and unresolved Type II gap, with different exponent ranges and numerical margins. These checks distinguish the restricted high-row bound in (8) from the earlier actual prime-row criterion and from other signed transports. No matching result was found in the repository or the inspected sources. This is a bounded comparison, not priority.
