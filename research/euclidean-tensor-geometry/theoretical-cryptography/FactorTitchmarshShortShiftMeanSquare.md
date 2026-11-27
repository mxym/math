# A two-term Titchmarsh formula for balanced semiprimes in short shift averages

For real $X$ let $\mathcal S_X=\{pq:X<p<q\le 2X,\ p,q\ {\rm prime}\}$ and $M=\pi(2X)-\pi(X)$. Products in this set have multiplicity one. Write $\tau$ for the divisor function and $\gamma$ for Euler's constant. For a positive integer $h$ define
$$
 c_h=\prod_{\ell\mid h}(1-1/\ell)
              \prod_{\ell\nmid h}\left(1+\frac1{\ell(\ell-1)}\right),
 \qquad
 d_h=c_h\left(\gamma+
       \sum_{\ell\mid h}\frac{\log\ell}{\ell-1}
       -\sum_{\ell\nmid h}\frac{\log\ell}{\ell^2-\ell+1}\right).
$$
The products and sums are over primes, and the infinite ones converge absolutely.

**Theorem.** For any fixed $K\ge1$ put $B=4K+20$. Uniformly for every interval $I$ of $H\ge(\log X)^B$ consecutive integers contained in $[-X^2/2,X^2/2]$, one has
$$
 \frac1H\sum_{\substack{a\in I\\a\ne0}}
 \left|\sum_{n\in\mathcal S_X}
  \left\{\tau(n+a)-c_{|a|}\log(n+a)-2d_{|a|}\right\}\right|^2
 \ll_K \frac{M^4}{(\log X)^K}.                         \tag{1}
$$
For example, for every fixed $A\ge1$, by taking $K=3A$ this gives error $O_A(|\mathcal S_X|(\log X)^{-A})$ for all but $O_A(H(\log X)^{-A})$ of the nonzero shifts in each such interval. The interval may be situated at shifts comparable to the size of the semiprimes. No GRH is required; the implied constants can be ineffective. This is a mean-square theorem, not a claim about an individual fixed shift or a way to recover a factor.

### Comparison with published results

[Fujii, Theorem 1](https://doi.org/10.1017/S0027763000017591) covers the shift $-1$ for prime boxes $p_1\le x^\delta$, $p_2\le x^{1-\delta}$ and gives the leading term with an error involving $\log\log x$. At $\delta=1/2$ its constant agrees with $c_1=\zeta(2)\zeta(3)/\zeta(6)$ under the corresponding normalization. [Drappeau–Topaçoğulları](https://arxiv.org/abs/1807.09569) give full expansions for their unrestricted almost-prime family at small shifts; an expansion summed over that family does not isolate the restriction $p,q\in(X,2X]$. [Assing–Blomer–Li, Theorem 1.1](https://arxiv.org/abs/2005.13915) obtain a uniform two-term formula for a single-prime von Mangoldt weight. Their result explains the form of the constants here but concerns a different sequence. [Karthick Babu's 2025 seminar abstract](https://www.mpim-bonn.mpg.de/node/14185) announces a uniform shifted product-of-primes result without a theorem statement to compare. Formula (1) concerns explicit two-term control in arbitrarily located polylogarithmic windows, not an improvement of the pointwise results in their respective domains.

### 1. Residue errors and denominator reduction

Use $L=\log X$ and $e(t)=\exp(2\pi it)$. For any real interval $J$, let $b(n)=\mathbf 1_{n\in \mathcal S_X\cap J}$, and set $B_0=\sum b(n)$, $\mathcal N=\sum |b(n)|^2=B_0\le M^2$. For an integer residue $u$ let
$$
 E_d(u)=\sum_{n\equiv u\bmod d}b(n)
             -\frac{B_0}{\varphi(d)}\mathbf 1_{(u,d)=1},
 \qquad
 \widehat E_d(h)=\frac1d\sum_{u\bmod d}E_d(u)e(-hu/d).
$$
If $q\mid d$ and $(h,q)=1$, then
$$
 \widehat E_d(dh/q)=\frac qd\,\widehat E_q(h).          \tag{2}
$$
For the actual count, the additive exponential factors through $q$. For the center, reduction $(\mathbb Z/d\mathbb Z)^\times\to(\mathbb Z/q\mathbb Z)^\times$ is onto and all fibers have the same size. The full count, including nonunits, is important for this identity. The constant term vanishes. Put $Z_q(u)=\sum_{h\bmod q,\ (h,q)=1}\widehat E_q(h)e(hu/q)$ for $q>1$. Then (2) gives, on combining equal reduced fractions,
$$
 \sum_{d\le T}E_d(u)=\sum_{k\le T}\frac1k
                           \sum_{2\le q\le T/k}Z_q(u). \tag{3}
$$

### 2. Energy at primitive additive frequencies

For $2\le Q\le 3X$, write
$$
 \mathcal E_Q=\sum_{\substack{Q\le q<2Q\\q\le3X}}
                      \sum_{h\bmod q,\ (h,q)=1}|\widehat E_q(h)|^2.
$$
We claim that
$$
 \mathcal E_Q\ll\frac{(X^2+Q^2)M^2}{Q^2}.             \tag{4}
$$
In addition, for all fixed $D,F>0$ one has, uniformly in $J$,
$$
 Q\le L^D \quad\Longrightarrow\quad
 \mathcal E_Q\ll_{D,F} M^4 L^{-F}.                     \tag{5}
$$

For a primitive character $\psi$ of conductor $r$, let $S(\psi)=\sum_n b(n)\psi(n)$. On the unit residues mod $q$ replace $\sum b(n)\chi(n)$ by $S(\psi)$ in the multiplicative character expansion, where $\psi$ induces $\chi$; omit the principal character and set the modified error to zero on nonunits. Denote this modified array by $\widetilde E_q$. The original coefficient of the principal character in the error is minus the mass of the nonunit products. If $q<X$ then there is no modification at all. If $X\le q\le3X$, at most one prime in $(X,2X]$ can divide $q$ for large $X$, so at most $M$ of the products in the coefficient sequence fail to be units. This modifies each multiplicative coefficient by $O(M)$ (including the principal one). The sum of the actual counts on the nonunit residues is at most $M$. Multiplicative and additive Parseval therefore give
$$
 \sum_{h\bmod q}|\widehat E_q(h)-\widehat{\widetilde E}_q(h)|^2
 =\frac1q\sum_{u\bmod q}|E_q(u)-\widetilde E_q(u)|^2
 \ll\frac{M^2}{q}\mathbf 1_{q\ge X}.                  \tag{6}
$$

For a character $\chi$ induced by $\psi$ of conductor $r\mid q$, let $G_q(\chi)=\sum_{u\bmod q}\chi(u)e(u/q)$. At primitive additive frequency the Gauss bound $|G_q(\chi)|^2\le r$ holds even for imprimitive $\chi$. Here is the short derivation. Use inclusion-exclusion on the condition $(u,q)=1$ while writing $\psi(u)$; for a divisor $t\mid q$ with $(t,r)=1$ the $u=tv$ sum becomes $\psi(t)\sum_{v\bmod q/t}\psi(v)e(v/(q/t))$. Group it by $v\bmod r$. It vanishes unless $q/t=r$, leaving the primitive Gauss sum multiplied by $\mu(q/r)\psi(q/r)$. The primitive Gauss sum has squared magnitude $r$: multiplication by units gives equal squared magnitudes at unit additive frequencies, the nonunit frequencies vanish by primitivity, and full additive Parseval gives total $r\varphi(r)$. Thus multiplicative orthogonality in the variable $h$ yields
$$
 \sum_{h\bmod q,\ (h,q)=1}|\widehat{\widetilde E}_q(h)|^2
 =\frac1{q^2\varphi(q)}\sum_{\chi\bmod q,\ \chi\ne\chi_0}
                    |S(\psi)|^2 |G_q(\overline\chi)|^2. \tag{7}
$$
The harmless sign in the additive exponential does not change the Gauss-sum magnitude.

We have $\sum_{y\le j<2y}1/\varphi(j)\ll1$ uniformly for $y\ge1/2$. Indeed $j/\varphi(j)=\sum_{f\mid j}\mu^2(f)/\varphi(f)$; after writing $j=fk$, the harmonic sum over each dyadic range of $k$ is bounded absolutely, and $\sum_f\mu^2(f)/(f\varphi(f))$ converges. Since $\varphi(rs)\ge\varphi(r)\varphi(s)$,
$$
 \sum_{\substack{Q\le q<2Q\\r\mid q}}\frac{r}{q^2\varphi(q)}
 \ll\frac{r}{Q^2\varphi(r)}.
$$
Sum (7) by conductors and apply the primitive character large sieve to the sequence $b$ supported in an interval of length $O(X^2)$:
$$
 \sum_{r\le 2Q}\frac r{\varphi(r)}
       \sum_{\psi\bmod r}^{*}
          |S(\psi)|^2
 \ll (X^2+Q^2)\mathcal N.
$$
The starred sum denotes primitive characters. Together with (6) this proves (4). For (5), if $r\le 2L^D$ and $\psi$ is nonprincipal, Siegel–Walfisz and subtraction at the endpoints give
$\sum_{X<p\le2X,\ p\in J'}\psi(p)\ll_{D,C} X L^{-C}$ for every real interval $J'$ and every $C>0$. In $S(\psi)$, fix the smaller prime $p$ and sum over the larger one, which is restricted to an interval by $J$, by $q>p$, and by $q\le2X$. Thus $S(\psi)\ll_{D,C} M X L^{-C}$. In (7) the number and weight of the remaining conductors and frequencies are bounded by fixed powers of $L$ (there is no correction (6) at these $q$). Increasing $C$ gives (5).

### 3. Short shift intervals and maximal cutoffs

For an arbitrary interval $I'$ of $H$ consecutive integer residues, the dual additive large sieve for reduced fractions with denominators in $[Q,2Q)$ gives
$$
 \sum_{u\in I'}\left|\sum_{q\in\mathcal D}Z_q(u)\right|^2
 \ll (H+Q^2)\sum_{q\in\mathcal D}\ 
                    \sum_{h\bmod q,\ (h,q)=1}|\widehat E_q(h)|^2
$$
for any subset $\mathcal D$ of this block, since distinct reduced fractions are $1/(4Q^2)$-separated modulo one. The inequality is translation invariant in $I'$. For the maximum over prefixes of the block, decompose each prefix into at most $O(L)$ disjoint dyadic subblocks, apply Cauchy–Schwarz, and sum the large-sieve bound for all subblocks. The coefficients are each charged once at each of $O(L)$ depths. This gives the same estimate with a factor $O(L^2)$ for the maximum over prefixes. Summing across the $O(L)$ blocks by Cauchy–Schwarz and using (3) and $\sum_{k\le3X}1/k\ll L$ gives
$$
 \frac1H\sum_{u\in I'}\left(\max_{T\le3X}
                        \left|\sum_{d\le T}E_d(u)\right|\right)^2
 \ll L^6\max_Q (1+Q^2/H)\mathcal E_Q.                  \tag{8}
$$
The two classical large-sieve inequalities used here are the additive and primitive character forms; the latter also follows from the former using the primitive Gauss-sum identity and multiplicative Parseval (see [Montgomery–Vaughan](https://doi.org/10.1112/S0025579300004708)).

For the blocks $Q\ge L^{B}$, (4) and $M\asymp X/L$ bound (8) by $O(M^4 L^8(L^{-2B}+H^{-1}))$. For the smaller blocks (5) absorbs the factor $1+Q^2/H$ and all other fixed log powers. When $H\ge L^B$ we have proved the uniform estimate
$$
 \frac1H\sum_{u\in I'}\left(\max_{T\le3X}
                       \left|\sum_{d\le T}E_d(u)\right|\right)^2
 \ll_B M^4 L^{8-B}.                                   \tag{9}
$$

### 4. Evaluation of the center

Uniformly for $1\le h\le X^2/2$ and $T\asymp X$,
$$
 \sum_{\substack{d\le T\\(d,h)=1}}\frac1{\varphi(d)}
       =c_h\log T+d_h+O(X^{-3/4}).                    \tag{10}
$$
To see this, expand $d/\varphi(d)$ as above and write $d=fk$. The inner sum is
$$
 \sum_{\substack{k\le V\\(k,h)=1}}\frac1k
 =\frac{\varphi(h)}h
       \left(\log V+\gamma+\sum_{\ell\mid h}
                              \frac{\log\ell}{\ell-1}\right)
             +O\!\left(\frac{\tau(h)}V\right).
$$
This follows by Möbius inversion of the harmonic sum. It also holds when some $V/t<1$ in that inversion, since the estimate $H_{\lfloor y\rfloor}=\log y+\gamma+O(1/y)$ holds for all $y>0$ with an enlarged absolute constant. Summing these errors with $V=T/f$ costs $O(T^{-1}\tau(h)\log(2T))$. Extending the convergent sum with coefficients $\mu^2(f)/(f\varphi(f))$ to infinity costs $O_\epsilon(T^{-1+\epsilon}\log(2X))$ for arbitrarily small $\epsilon>0$ by the elementary bound $\varphi(f)\gg_\epsilon f^{1-\epsilon}$ (shrinking the exponent to absorb a logarithm). Use $\tau(h)\ll_\epsilon h^\epsilon$ to get the displayed power saving. Euler multiplication gives $c_h$, and the average of $\log f$ under the product weights is $\sum_{\ell\nmid h}(\log\ell)/(\ell^2-\ell+1)$, giving $d_h$.

### 5. Product bins and the full divisor sum

Partition $(X^2,4X^2]$ into $P=\lceil L^{K+1}\rceil$ real intervals of equal length. In each bin $[v_i,w_i]$ (use disjoint endpoints for membership), and for fixed $a\in I$, use the two cutoffs $T_i^-=\sqrt{v_i+a}$, $T_i^+=\sqrt{w_i+a}$. They lie between $X/\sqrt 2$ and $3X$. By nonnegativity, both cutoffs sandwich
$\sum_{n\ {\rm in\ bin}} b(n)\sum_{d\mid n+a,\ d\le\sqrt{n+a}}1$. Apply (10) to the two centered sums at those cutoffs and the maximal error to the full residual at $u=-a$. Since $\log(w_i+a)-\log(v_i+a)\ll 1/P$, the error over this bin after multiplying by 2 is at most
$$
 O\bigl(B_{0,i}(P^{-1}+X^{-3/4})\bigr)
          +2\max_{T\le3X}\left|\sum_{d\le T}E_{d,i}(-a)\right|.
$$
Finally $\tau(m)=2\sum_{d\mid m,\ d\le\sqrt m}1-\mathbf 1_{m\ {\rm square}}$. The square correction is $O(X)$ for every shift, as there are $O(X)$ squares in the full range and $b(n)\le1$. After summing bins, squaring, and applying Cauchy–Schwarz and (9), the normalized mean square is
$$
 \ll M^4(P^{-1}+X^{-3/4})^2+X^2+
                            P^2 M^4 L^{8-B}
 \ll_K M^4 L^{-K}.
$$
This proves (1).

The companion finite check tests denominator reduction, recombination of rational frequencies, imprimitive Gauss sums (including a repeated-prime-power case through the bounded loops), the arithmetic constant identity, and the hyperbola bounds. It does not test the analytic estimates themselves.
