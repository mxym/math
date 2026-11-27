# Limited binary observations do not reveal a fixed residue of the smaller prime

Let $P<Q$ be a uniform unordered pair of distinct primes from $(X,2X]$, placed in increasing order, and let $N=PQ$. Use the padded binary representation of $N$ of length $w=\lceil\log_2(4X^2+1)\rceil$. Let $m\ge3$ be a fixed integer and $U_m$ an independent uniform element of $(\mathbb Z/m\mathbb Z)^\times$.

**Theorem.** There are positive constants $c_1,c_2$ such that, for sufficiently large $X$ (depending on $m$), even a randomized adaptive observer reading at most $c_1\sqrt{\log X}/\log\log X$ bits of $N$ has
$$
d_{\mathrm{TV}}\big(
(\mathcal T,P\bmod m),\;(\mathcal T,U_m)
\big)\ll_m \exp(-c_2\sqrt{\log X}),
$$
where $\mathcal T$ is its full transcript of queries and replies, and the second pair has the same transcript marginal as the first. Any random choices of the observer are independent of the input. In particular, predicting which of $1,3\bmod 4$ the smaller prime occupies is no better than guessing a fair bit, up to the stated error. Computation between bit queries is unrestricted. No claim concerns reading the whole product, nonuniform prime sampling, computing factors, or computational security outside this query model.

Under the generalized Riemann hypothesis (GRH) for Dirichlet $L$-functions, for any fixed $0<\varepsilon<1/6$, at most $(1/6-\varepsilon)\log X/\log\log X$ queries give $O_{m,\varepsilon}(X^{-\varepsilon/3})$ total variation by the same argument. All logarithms without base indicated are natural.

## A signed prime-product sum

Write $e(t)=\exp(2\pi i t)$. We first show that for each nonprincipal Dirichlet character $\chi$ modulo fixed $m$,
$$
S_\chi(\alpha):=\sum_{X<p<q\le 2X}\chi(p)e(\alpha pq)
  \ll_m X^2\exp(-c\sqrt{\log X}) \tag{1}
$$
uniformly in real $\alpha$, with both $p,q$ prime. The ordering restriction remains present throughout; using the weight on the smaller prime is important for the interpretation.

### Minor arcs

Given coprime integers $a,r$, $r\ge1$, and $|\alpha-a/r|\le r^{-2}$, Cauchy–Schwarz in the $q$ sum followed by completion to all integer $q$ gives
$$
|S_\chi(\alpha)|^2
 \ll X^2\left(X+\sum_{1\le h\le X}\min\big(X,\|\alpha h\|^{-1}\big)\right),
$$
with the zero-distance term interpreted as $X$. To see this, expand
$\sum_{X<q\le2X}|\sum_{X<p<q}\chi(p)e(\alpha pq)|^2$ after fixing the outer Cauchy–Schwarz factor $O(X)$. For fixed $p,p'$, the inner exponential sum is over the interval $q>\max(p,p')$. The coefficients have modulus at most one, and there are $O(X)$ possible $p,p'$ for each difference $h=p-p'$. The interval's location and dependence on $p,p'$ do not affect the geometric sum bound.

On each block of at most $r$ consecutive $h$'s, the fractional parts of $\alpha h$ differ by at most $1/r$ from a shifted set of distinct grid points of mesh $1/r$. Indeed, the first term of the block supplies the shift and the local errors from $(\alpha-a/r)(h-h_{\rm first})$ are bounded by $1/r$. This gives $O(1)$ points in each mesh interval, and the block contributes $O(X+r\log(2r))$ to the sum. Consequently
$$
\frac{|S_\chi(\alpha)|}{X^2}\ll
\left(\frac1r+\frac{\log(2r)}X+\frac{r\log(2r)}{X^2}\right)^{1/2}. \tag{2}
$$
Let $R=\exp(a_0\sqrt{\log X})$, where $a_0>0$ is small. By Dirichlet approximation with height $\lfloor X^2/R\rfloor$, choose $r\le X^2/R$ and $\alpha=a/r+\beta$ with $|\beta|\ll R/(rX^2)$ and $|\beta|\le1/r^2$. If $r\ge R$, (2) is already sufficient for (1).

### Major arcs, including a possible exceptional zero

Here $r<R$. We use a classical effective prime number theorem in progressions with the exceptional term retained. In the notation of [Drappeau and Fiorilli, equation (2.1)](https://doi.org/10.1112/tlm3.12030), take their global scale $2X$ and the modulus cutoff $\lfloor mR\rfloor$. There are an absolute $b>0$ and at most one primitive real exceptional character $\xi$ (with conductor $d$ and real zero $\rho$) for that scale, such that for $t\in[X,2X]$, $s\le mR$ and any unit $v\bmod s$,
$$
\psi(t;s,v)=\frac{t}{\varphi(s)}
 -\mathbf1_{d\mid s}\frac{\xi(v)t^\rho}{\rho\varphi(s)}
 +O\big(X\exp(-b\sqrt{\log X})\big). \tag{3}
$$
In fact the error bound in that reference is summed over these moduli and maximal in the endpoint, with an additional $mR\sqrt X(\log X)^{O(1)}$ term negligible here. Delete the exceptional term if $\xi$ does not exist. The convention is the same exceptional character for all endpoints and moduli in (3). This is a consequence of the Landau–Page uniqueness theorem; see also [Ford–Green–Konyagin–Maynard–Tao, Lemma 7.1](https://www.ams.org/journals/jams/2018-31-01/S0894-0347-2017-00876-2/S0894-0347-2017-00876-2.pdf). The exceptional conductor $d$ exceeds the fixed $m$ for sufficiently large $X$: the near-$1$ window shrinks and the finite set of Dirichlet $L$-functions of conductor at most $m$ have no zero at $1$.

On $(X,2X]$, removing prime powers and partial summation turn (3) into the prime counting measure estimate with density
$$
\frac{1-\mathbf1_{d\mid s}\xi(v)t^{\rho-1}}{\varphi(s)\log t}.
$$
More precisely the prime count with this density subtracted has uniformly $O(X\exp(-b\sqrt{\log X}))$ discrepancy on all subintervals of $(X,2X]$, after decreasing $b$ if necessary. Testing it against $e(\beta p t)$ over $(p,2X]$ costs a factor $O(1+|\beta|X^2)\ll1+R/r$ by partial summation.

For each prime $p$ all contributing $q$ are units mod $r$ since $r<X$. Sum the $q$ progression estimates with their multipliers $e(apv/r)$. Changing units $v$ to $pv$ gives
$$
\begin{aligned}
\sum_{v\bmod r}^{*} e(apv/r)&=\sum_{v\bmod r}^{*}e(av/r),\\
\sum_{v\bmod r}^{*} \xi(v)e(apv/r)
 &=\xi(p)\sum_{v\bmod r}^{*}\xi(v)e(av/r) \qquad(d\mid r).
\end{aligned} \tag{4}
$$
The second identity uses the reality of $\xi$. Thus up to an error $O(X\exp(-b\sqrt{\log X})(r+R))$ in each inner $q$ sum, the principal part is a constant of modulus at most one times
$$
F_0(p)=\int_p^{2X} \frac{e(\beta p t)}{\log t}\,dt,
$$
and, if present, the exceptional part is another such constant times $\xi(p)F_1(p)$ where
$$
F_1(p)=\int_p^{2X}\frac{t^{\rho-1}e(\beta pt)}{\log t}\,dt.
$$
Both weights have supremum plus total variation of order at most $(X/\log X)(1+R/r)$. The varying lower endpoint contributes $O(1/\log X)$ per unit length to the derivative; the oscillatory factor contributes $O(|\beta|X^2/\log X)$, since $t^{\rho-1}\le1$.

The principal part of the outer sum is weighted by $\chi$, a nonprincipal character of fixed modulus $m$ which does not induce $\xi$. The exceptional part is weighted by $\chi\xi$, a character modulo $\operatorname{lcm}(m,d)\le mr$. On the units it is neither principal nor induced by $\xi$. If principal, $\xi$ would have conductor at most $m$, which is excluded. If induced by $\xi$, cancellation by $\xi$ on the units would make $\chi$ principal, also excluded. Orthogonality of characters against both main terms in (3) now bounds either outer prime character's partial sums over $(X,y]$ by $O_m(rX\exp(-b\sqrt{\log X}))$. This is why an exceptional zero of the inner progression estimate does not give an exceptional signed product sum: the outer twist takes it to a different character.

Use partial summation against $F_0,F_1$ and sum the inner-sum errors over the at most $O(X)$ values of $p$. The result is $O_m(X^2 R\exp(-b\sqrt{\log X}))$. Taking $a_0<b/2$ proves (1) on the major arcs as well. The argument uses neither GRH nor an assumption that exceptional zeros are absent.

Under GRH use $R=X^{1/3}$ and replace the error in (3) by $O(\sqrt X(\log X)^{O(1)})$ with no exceptional term, the standard GRH prime progression count from the explicit formula (for this range see [The prime number theorem for primes in arithmetic progressions at large values](https://academic.oup.com/qjmath/article/74/4/1505/7240642)). The same estimates give $|S_\chi(\alpha)|\ll_m X^{11/6}(\log X)^{O(1)}$ on the major arcs, and (2) gives this bound on the minor arcs.

## From exponential sums to adaptive queries

Let $\mathcal A=\{pq:X<p<q\le2X\}$. Unique factorization gives distinct products and the prime number theorem gives $|\mathcal A|\asymp X^2/(\log X)^2$. Thus (1) means each additive character of $N$ has signed expectation against $\chi(P)$ of size $O_m(\exp(-c'\sqrt{\log X}))$, uniformly in its frequency; under GRH this size is $O_m(X^{-1/6}(\log X)^{O(1)})$.

For a binary position $j$, its prescribed value is tested by a periodic zero-one function on $\mathbb Z/(2^{j+1}\mathbb Z)$, the indicator of either half of the residues. Its Fourier coefficients have sum of absolute values $O(1+j)$: the constant coefficient is $1/2$ and the interval geometric series gives $O(1/\min(b,2^{j+1}-b))$ at each nonzero frequency $b$. This is at most $C\log X$ uniformly for $j<w$. Fourier-expanding a conjunction of $\ell$ prescribed bits therefore gives an additive character expansion with coefficient absolute sum at most $(C\log X)^\ell$, regardless of gaps between the bit positions. Consequently in the unconditional case any such conjunction $A$ with $\ell\le k$ satisfies
$$
|\mathbb E[\,\chi(P)\mathbf 1_A\,]|
 \ll_m (C\log X)^k \exp(-c'\sqrt{\log X}). \tag{5}
$$

Fix the observer's random tape. A deterministic tree of depth $k$ has at most $2^k$ leaves. The event for any leaf is exactly a conjunction of the bit values queried on that path (repetitions can be discarded; incompatible leaves have probability zero). Let $L$ be this leaf variable. Since $P$ is a unit mod $m$ for $X\ge m$, orthogonality modulo $m$ gives, for each leaf $\ell$ and unit $u$,
$$
\Pr(L=\ell,P=u\bmod m)-\Pr(L=\ell)/\varphi(m)
 = \frac1{\varphi(m)}\sum_{\chi\ne 1}
       \overline{\chi(u)}\,\mathbb E[\chi(P)\mathbf1_{L=\ell}].
$$
Summing absolute values in $\ell,u$ and dividing by two proves the total variation bound, because $(2C\log X)^k\exp(-c'\sqrt{\log X})$ is still $\exp(-\Omega(\sqrt{\log X}))$ for sufficiently small $c_1$. The bound is uniform in each deterministic tree, so averaging the random tapes (even exposing the tape as side information) preserves it. Under GRH substitute the $X^{-1/6}$ bound in (5); the Fourier and tree cost is at most $X^{1/6-\varepsilon+o(1)}$, giving the stated error. No lower bound on the mass of an individual leaf was assumed, so the theorem is about the unconditional joint law rather than pointwise conditioning on every rare pattern.

## Comparison and finite checks

[Bourgain's prescribed-digit theorem](https://arxiv.org/abs/1307.0398) concerns retaining some prescribed digits of a prime itself. Here the binary restrictions are on a product, and the object estimated is a signed two-prime distribution. [The full factor-output lower bound](FactorFixedLayout.md) is a different task and does not itself imply the single-residue result proved here. We use standard bilinear minor-arc and prime-progression estimates, and keep the exceptional character explicitly until the second prime cancels its contribution. No claim is made about hardness of predicting the residue given arbitrary arithmetic access to $N$.

[The small exact checker](verify_factor_residue_bit_queries.js) tests the unit reindexing identity, orthogonality for toy twists, minor-arc spacing, binary-period coefficient identities, and transcript counting on predetermined small examples. It does not test an asymptotic estimate or recover any input's factors.
