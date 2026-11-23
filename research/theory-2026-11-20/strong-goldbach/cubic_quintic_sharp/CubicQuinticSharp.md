# A sharp cubic–quintic Goldbach detector with an exact rough positive block

Let \(N\) tend to infinity through even integers. Let \(J\Subset(0,1)\) be a fixed nondegenerate interval, \(L=\log N\), and \(M=|J|N\mathfrak S(N)\). All pairings have \(x+y=N,\ x\in NJ,\ (x,N)=1\):
\[
 \langle X,Y\rangle=\sum X(x)Y(y),\qquad
 \Pi(n)=(\log n)1_{\{n\ {\rm prime}\}},\qquad R_J=\langle\Pi,\Pi\rangle .
\]
Define a profile on the actual own-log divisor angles:
\[
 F(t)=2(1-2t)_+^3-(1-2t)_+^5,\qquad
 V(n)=\mu^2(n)\log n\sum_{d\mid n}\mu(d)F(\log d/\log n),
 \qquad H=V-\Pi.
\]
Primes and nonsquarefree integers have exactly zero \(H\) on the central range. In particular the following identity does not put an actual prime weight on either argument of \(H\).

**Theorem.** Uniformly in fixed even targets,
\[
 \langle H,H\rangle=R_J+o(M).
 \tag{1}
\]
For every central squarefree integer of odd rank \(r\ge3\), let \(u_1,\ldots,u_r\) be the genuine prime angles in its own logarithm, so \(\sum u_i=1\). Then \(H/\log n\) is exactly
\[
 \begin{cases}
 16(\prod u_i)(3-5\sum u_i^2),&r=3,\\
 -1920\prod u_i,&r=5,\\
 0,&r\ge7 .
 \end{cases} \tag{2}
\]
No minimum-factor or subset-angle-separation restriction enters (2).

Set \(\mathcal B=\{P^-(x),P^-(y)>N^{.150}\}\) within the original physical pairing. The **complete signed** contribution of \(\mathcal B\) satisfies
\[
 \sum_{\mathcal B}H(x)H(y)>.515M+o(M).
 \tag{3}
\]
Consequently \(R_J\ge .515M+\sum_{\mathcal B^c}H(x)H(y)+o(M)\). The residual \(\mathcal B^c\) has at least one actual factor \(\le N^{.150}\); no lower on it is asserted. In particular (3) is neither a uniform positive lower on (1) nor a result on binary Goldbach. This is a new score, not a transfer of a credit from a symmetric quartic, sextic, or the wide affine receiver.

## 1. True two-arm control at the sharp own-log half

Extend the profiles below to the real line by a single compact smooth left cutoff identical to one near \([0,1/2]\). Let \(\chi\) be a fixed smooth function in \([0,1]\) equal to one on \((-\infty,-2]\) and zero on \([-1,\infty)\). For fixed \(0<h<1/20\) set \(F_h(t)=F(t)\chi((t-1/2)/h)\) on \(t\ge0\). The sharp profile is \(C^2\); its third derivative is piecewise smooth of bounded variation. In the compact extension its Fourier transform is \(O((1+|\xi|)^{-4})\), by four integrations by parts with the last derivative a finite measure. More explicitly,
\[
 F_h(t)-F(t)=h^3\Phi_h((t-1/2)/h),
\]
where \(\Phi_h\) is supported on \([-2,0]\), is \(C^2\), and has uniformly bounded \(L^1\) norm and uniformly bounded variation of its third derivative. This follows directly by writing the two terms as the third and fifth powers of the ramp, with the fixed smooth cutoff in the scaled variable. Hence
\[
 |\widehat{F_h-F}(\xi)|\ll h^4(1+h|\xi|)^{-4}.
 \tag{4}
\]
The weighted \(L^1\) norm with weight \((2+|\xi|)^c\) is \(O_c(h^{3-c})\) for every \(0\le c<3\).

We use exactly the true corrected-Henriot envelope and prime harmonic of the [sharp symmetric detector, §§1–2](../halfzero_detector/Proof.md). In detail, on the real pair \(x,N-x\) put \(A_\xi(p)=|1-e^{i\xi\log p/L}|\) and \(W_\xi(n)=\prod_{p\mid n}A_\xi(p)\). The ordinary prime harmonic is
\(\sum_{p\le N}A_\xi(p)/p\le (4/\pi+\epsilon)\log(2+|\xi|)+O_\epsilon(1)\), uniformly in real \(\xi\), as proved there by PNT and the mean of the periodic function \(|1-e^{it}|\). The corrected two-linear-form upper has the genuine initial root product \(O(\mathfrak S(N)/L^2)\). At \(p\nmid N\) there are two disjoint roots; since the weight is constant on positive prime powers, their exact-valuation Euler majorant is \(1+(A_\xi(p)+A_\zeta(p))/p\). At \(p\mid N\) the root is excluded by the actual target units and enters the usual singular product. Accordingly the sum of \(W_\xi(x)W_\zeta(y)\) is
\[
 \ll_{\epsilon,J}(M/L^2)(2+|\xi|)^c(2+|\zeta|)^c,
 \qquad c=4/\pi+\epsilon<2.
 \tag{5}
\]
All growth parameters in the corrected theorem are uniform, since each \(A_\xi(p)\le2\). A true \(\Pi\)-leg can be bounded with \(L\) times the indicator of \(N^{1/4}\)-rough integers instead. Its Euler cost outside the initial root product is bounded, and the same calculation gives (5) without the frequency factor on that leg.

The own-log phase is not replaced by a tangent approximation. Put \(c_n=\log n/L=1+O_J(1/L)\), and apply Fourier inversion in the target variable \(t=\log d/L\) to the *dilated* profile \(F(t/c_n)\). Its transform is \(c_n\widehat F(c_n\xi)\) and is dominated uniformly by \(C(1+|\xi|)^{-4}\). The same dilation of the difference in (4) has the uniform upper in (4), with a changed constant. The exact divisor sum of a character then has absolute value \(W_\xi(n)\) by multiplicativity over actual distinct prime factors. The \(\mu^2(n)\) flag only decreases this upper. Multiplying by the two log factors, (4)–(5) give a true absolute paired error \(O_J(h^{3-c}M)\) on replacing either sharp arm by its own-log taper, against the sharp arm, tapered arm, or true prime arm. In particular this estimate does not first fix the least factor or the rank. For fixed \(h\) the taper is smooth, so the Fourier difference between its dilation and the fixed target-log taper is \(O_{h,J}(L^{-1}(1+|\xi|)^{-4})\) by differentiation in \(c_n\). The same proof gives absolute error \(o(M)\) for that change. Similarly replacing the outside \(\log n\) by \(L\) in the raw tapered arm costs \(o(M)\); the genuine prime score is not changed.

## 2. Exact capped calibration and passage to the identity

Fix \(h\) and use the target-log tapered raw score with outside \(L\). Its actual divisor \(d\le N^{1/2-h}\). Expand \(\mu^2(n)=\sum_{e^2\mid n}\mu(e)\), retaining \(e\le N^{h/4}\). Omitted physical squares occur on \(O(N^{1-h/4}+N^{1/2})\) integers, and all physical weights are bounded by fixed powers of the divisor function times logarithms. Thus the discarded contribution is \(o(M)\). Each actual modulus is \([d,e^2]\le N^{1/2-h/2}\), not a falsely coprime product. On true unit rows the opposite actual moduli are coprime and both prime to \(N\). Opening target units gives the density \(\varphi(N)/(N[d,e^2][d',e'^2])\) in the two-arm CRT and total absolute floors \(N^{1-h+o(1)}\), since at any actual modulus the factorizations have fixed divisor-power multiplicity. A genuine prime cross uses weighted ordinary BV at the strict subroot bound; its reduced denominator is \(\varphi([d,e^2])\), with the spatial interval or its literal reflection.

For clarity, the local completions are exactly those of the [squarefree short odd receiver, §§1–2](../short_odd_receiver/Proof.md). At \(p\nmid N\) the omitted \(p^2\) roots on the two arms are disjoint. For the exponent variables \(s,t\) near 1 the factor before extracting the two inverse zetas is
\[
  1-2/p^2-(1-1/p)p^{-s}-(1-1/p)p^{-t}
\]
because a Möbius label that contains \(p\) on one arm leaves the other arm a \(p\)-unit, and forbids a second \(p\) on its own arm. At \((1,1)\) this is \(1-2/p\). At \(p\mid N\) the factor is one with the separate target-unit density. The prime-cross factor at \(p\nmid N\) before its single inverse zeta is \(1-1/(p(p-1))-p^{-1-s_0}\), \(s_0\) near 0. At \(s_0=0\) this is \(1-1/(p-1)\), with the real target primes still excluded; \((d,e^2)\) is fully allowed in that local calculation. Only in the principal restore the missing square labels: the relative factors are \(1/p\) at \(p\mid(d,e)\) and \(1/p^2\) outside in the integer model, or \(1/p\) and \(1/(p(p-1))\) in the prime model. Rankin at exponent \(1/4\) gives arbitrary-log savings on the omitted tail even with polynomial \(d\) and all actual divisor weights.

After extracting the inverse zeta factors, the resulting coefficient norms on the slight left abscissa \(1-1/(10\log L)\) have only absolutely summable \(O(p^{-2+O(1/\log L)})\) factors off the masks. The primes of \(N\), or of a fixed opposite actual label when completing one variable first, give at worst fixed powers of \(\log L\), by splitting them at \(L^2\). Complete each Möbius variable at \(\exp((\log L)^4)\) by ordinary uniform Mertens tails convolved with these absolute coefficient norms. This is the signed short completion of the cited proof, which also gives fixed higher log-moment bounds by powers of \(\log L\). Tapered derivatives at fixed \(h\) have bounded variation, so completion costs arbitrary inverse log powers as usual. Zeroth log moments vanish. The first/first moment in the two-arm CRT principal is \(\mathfrak S(N)\); the first moment in the prime-principal calculation is \(-\mathfrak S(N)\), with the same sign conventions and local factors just checked.

The taper has \(F_h(0)=1\), \(F'_h(0)=-2\). Thus on the completed short scales \(L F_h(\log d/L)=L-2\log d+O_h((\log d)^2/L)\), the higher derivatives contributing \(o(M)\) after the actual signed completion. This gives \(\langle V_h,V_h\rangle=4M+o(M)\), \(\langle \Pi,V_h\rangle=\langle V_h,\Pi\rangle=2M+o(M)\) for the capped model. Keeping the genuine binary atom leaves \(R_J+(4-2-2)M+o(M)\), not a second copy of it. Taking \(N\to\infty\) first and then \(h\downarrow0\) in §1 proves (1). In particular there is a uniform sharp comparison at scale \(M\); no uniform small-tail assumption on individual factors is being made.

## 3. Exact global odd-rank algebra

For \(u_i=\log p_i/\log n\), the angle of a divisor is the sum \(u(A)\) of its actual subset of the primes. At odd rank \(\mu(A^c)=-\mu(A)\), so complement pairing makes the divisor sum exactly one half the full Möbius sum of
\[
 F(s)-F(1-s)=P(1-2s),\qquad P(z)=2z^3-z^5.
\]
This remains true on any exact tie at half, since both terms vanish. Equivalently this is \(2^{r-1}\) times the coefficient expectation of \(P(\sum_i\epsilon_i u_i)\prod_i\epsilon_i\) over independent signs \(\epsilon_i=\pm1\), an exact finite algebraic identity. A monomial survives only when every \(u_i\) occurs to odd degree. At rank 3 the degree-three coefficient is \(6\prod u_i\); the degree-five coefficient is \(20(\prod u_i)\sum u_i^2\) from exponent pattern \((3,1,1)\). At rank 5 the only term is \(-5!\prod u_i\). These give (2), and rank at least 7 is exactly zero at every genuine squarefree row. No rank sign is assigned on nonsquarefree rows: their score is zero by definition.

## 4. The full actual bilateral rough block, both signs

Take \(a=.150\), with the physical cutoff \(N^a\). There are no nonzero ranks beyond six. The normalized rank-two score, at smaller own angle \(u\), is \(1-F(u)\in[0,1]\). The true rank-three formula is positive on this complete floor because \(\sum u_i^2\le(1-2a)^2+2a^2=.535<.6\). Its positive cap is \(64/81<1\), using \(\prod u_i\le1/27\) and \(\sum u_i^2\ge1/3\). Let \(D_+,D_-\) be the positive and negative magnitudes of \(H\) on this floor. Both are genuine compact fixed-rank product weights. The ordinary mass \(m(X)\) of any such \(X\) is its unopposed normalized angular harmonic (so \(\sum_{x\in NJ}X(x)\sim |J|N\,m(X)\) when nonzero).

First obtain positive paired weight on genuine ranks 2 or 3, with no prime-pair assumptions. Use the same literal two-marginal argument as in the [weighted rough intersection, §§1–3](../sextic_true_tag_rebate/RoughPositiveCredit.md). A genuine rank-two/three source cell \(E\) with angle-score exceeding \(u\) has ordinary ordered mass \(m(E)\), from the actual independent prime labels and largest-prime PNT, with density \(\prod_i u_i^{-1}\) on its ordered angle simplex. Its actual paired \(N^a\)-rough receiver gives marginal count \((k\,m(E)+o(1))M/L^2\) as a lower, where
\(k=2\log(.499/a-1)/.499\).
This is true product BV at the literal sieve moduli \(\le N^{.499}\) and residue \(N\), followed by the linear lower sieve at ratio \(.499/a\in(3,4)\). The conditional prime density is \(1/(p-1)\) off \(Nx\), zero on \(Nx\). The true source factors exceed a fixed power, so their extra Euler factors cost \(1+o(1)\). Real large square rows cost \(O(N^{1-a+o(1)})\) and are excluded from the source. The same lower on \(1-J\) gives the opposite genuine marginal.

The one common ambient \(\mathcal B\) has upper size \((C+o(1))M/L^2\), now using the genuine unweighted dimension-two DHR upper at level \(N^{.999}\), not the weaker Selberg square. Use [Diamond–Halberstam, Theorem 9.1](https://www.cambridge.org/core/books/abs/higherdimensional-sieve-method/sieve-method-for-1/5A00D3EA4C00B3B10D3CB8521D68D10C), as restated in [Franze–Kao, §4, (19)–(22)](https://arxiv.org/pdf/1812.11280), exactly as in the [fixed-target DHR comparison](../sextic_true_tag_rebate/ExactDHRZeroTag.md). There is one root at a prime of the even target (including 2) and two otherwise; the upper may drop target units. The uniform dimension-two product is \((1+o(1))e^{-2\gamma}\mathfrak S(N)/(a^2L^2)\), and the actual accumulated floors are \(O(N^{.999}L^{O(1)})=o(M/L^2)\), with at most \(8^{\omega(d)}\) per label. Thus \(C=e^{-2\gamma}F_2(6.66)/a^2\). Both marginals are subsets of this same physical ambient; there is no assumption of independent ranks.

The checker bounds \(C<14.546526\) using the certified switch cells \(\alpha_2\in(5.3577,5.3578),\ \beta_2\in(4.2664,4.2665)\) and the DHR delay system of that proof. Let \(\mathcal G=\int\rho_2\) be the ordinary Selberg denominator function, \(A(v)=v^2e^{-2\gamma}F_2(v)\), \(B(v)=v^2e^{-2\gamma}f_2(v)\). Up to \(\alpha_2\), \(A(v)=v^2/\mathcal G(v/2)\). In this upper check every required delayed \(B\) value occurs below 5.66, and its derivative \(2v A(v-1)/(v-1)^2\) uses only \(v-1<4.66<\alpha_2\); thus its increment can be upper bounded by \(2v/\mathcal G((v-1)/2)\) starting at the lower endpoint of the \(\beta_2\) cell. Upper-bound \(A\) at the switch by \(\alpha_+^2/\mathcal G(\alpha_-/2)\), and integrate its delayed derivative from the lower endpoint of that cell for a conservative upper. The checker computes \(\mathcal G\)'s lower via the positive delay for \(\rho_2(t)/t\), and uses only upward rational ticks in these two integrations. No numerical approximation near a switch is taken as exact.

At each amplitude threshold \(j/200\) for \(j=1,\ldots,200\), take a lower \(\underline m_j\) using actual ordered interior angular boxes of mesh \(1/1000\) in ranks 2 and 3, as in the linked intersection. For rank two use \(1-F(u_{\rm low})\), and for rank three use \(1-\sum_i P(1-2u_i)\) at the three lower endpoints; \(P(1-2u)\) is decreasing. Harmonic denominators are upper-rounded and all amplitude inequalities are strict before true spatial endpoint/floor errors. For any two thresholds the actual intersection count is at least \(([k(\underline m_j+\underline m_\ell)-C]_++o(1))M/L^2\). The sum of the layer widths on each actual arm is at most its true normalized positive amplitude. Consequently the entire \(D_+,D_+\) term is \(>.575485M+o(M)\); the lower uses just true rank-two/three pairs and their genuinely available common rough ambient.

It remains to pay every genuine mixed-sign row of \(\mathcal B\). In rank 4 put \(G_0(u)=2|1-2u|^3-|1-2u|^5\). Since complementary signs agree in even rank,
\[
 H_4/\log n
 =1-\sum_{i=1}^4 G_0(u_i)
    +G_0(u_1+u_2)+G_0(u_1+u_3)+G_0(u_2+u_3)
\]
on every real quadruple, including those with a giant. The function \(G_0\) is convex on \([.15,.55]\). By Jensen the four singleton terms sum to at least \(4G_0(.25)=.875\); each pair angle is in \([.30,.70]\), with \(G_0\le .11776\). Therefore its positive cap is \(<1\). Use the actual sorted simplex to upper-bound its ordinary negative mass: the checker covers the first three coordinates with \(1/1000\) cells, extends the fourth to its true possible ordered interval and upper-rounds the singleton terms and lower-rounds the three pair terms. Where a pair interval straddles half its lower is zero. Denominator angles are lower-rounded and boxes possibly meeting the sorted boundary can only overcount. This yields \(m(D_{4,-})<.004093559\).

Rank 5 has exact negative mass \(1920(1-5a)^4/(5!4!)<.002604167\), using (2) and cancellation of its harmonic denominators. In rank 6 only the empty, singleton, pair and possible triple subsets occur below half. Its score is at most \(1-6F(1/6)+15F(.30)<1\), by convexity of \(F\) on the singleton range; triples are negative. The negative magnitude is \(<3\), since the singleton sum is at most \(6F(.15)\) and the at most twenty triples cost at most \(20F(.45)\); the constant term must still be counted. Thus its negative ordinary mass is at most \(3(1-6a)^5/(6!5!a^6)<.000030484\). No rank other than 4, 5 and 6 can contribute to \(D_-\) on this floor, and in all ranks \(D_+\le L\).

For any of these true compact negative sources, the actual positive receiver is therefore at most \(40/9\) times its ordinary mass, in units \(M\). Indeed apply the same below-root product BV and the linear upper on the opposing \(N^a\)-rough gate, with ratio \(.499/a>3\) and upper coefficient at ratio 3 equal to \(2/(3a)=40/9\). The true positive upper may include primes, but they have no weight in the score. This prices each opposite sign with the actual source units and split ranks, without pairing independent ordinary masses. Consequently both opposite-sign terms cost together \(<.059807M+o(M)\). The actual \(D_-,D_-\) term is nonnegative and can be discarded. These calculations prove (3) on the **whole** stated chamber, with its literal complement retained in (1).

Run:

    python3 -OB check_cubic_quintic_rough.py
