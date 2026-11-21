# An all-moduli beyond-square-root block on the predecessor-tagged binary prime statistic

For a prescribed even integer $P$, write $L=\log P$, $I=[P/3,2P/3]$. For fixed $K$, use any one family of $K$ disjoint prime sets from the [neutral predecessor tag construction](https://github.com/mxym/math/tree/51304b57/research/theory-2026-11-20/strong-goldbach): all its labels $\ell$ lie in $[\exp(L^{.1}),\exp(2L^{.2})]$, avoid $P(P-1)$, and each set has reciprocal mass between $1/4$ and $1/2$. Let $\mathcal A$ be the products of one prime from each set, $\mathcal V=\sum_{a\in\mathcal A}1/a$ and $W(t)=\mathcal V^{-1}\sum_{a\in\mathcal A}{\bf1}_{a|t}$. Bounds are uniform in these sets, hence hold also after averaging the families.

**Theorem.** Write $X=MN\asymp P$, $N=P^{\nu+o(1)}$, $Q=P^{v+o(1)}$. Fix
$$ 0<\nu<1/72,\qquad 1/2\le v<17/33-12\nu/11. $$
(The inequalities on the right must have fixed slack.) For arbitrary complex $|\alpha_m|\le L^C$, and any two intervals inside $(M,2M]$ and $(N,2N]$, with $m,n$ restricted to these intervals,
$$
 \sum_{Q<d\le2Q}\left|
 \sum_{\substack{mn\in I,\ (mn,P)=1\\ mn\equiv P\pmod d}}
 \alpha_m\mu(n) W(P-1-mn)\log((P-mn)/d)
 \right|\ll_{A,C,K,\nu,v} P L^{-A}.                                      \tag{1}
$$
The logarithm may be omitted. Constants may be ineffective. For example $(\nu,v)=(.005,.505)$ works. There is **no exceptional-target or GRH hypothesis**. The absolute values are summed over the complete dyadic interval of moduli, not only the primes, and are outside the sum over source rows. This does not bound absolute values of the individual tagged rows.

**Its precise place in the prime problem.** In the true central sum with weight $W(q-1)$ and $x+q=P$, insert $(x,P)=1$ before expanding either von Mangoldt function. The lost contribution to the full statistic is negligible: $x$ must be a power of a prime dividing $P$, giving $O(L^2)$ possible values, with $W\ll_K L^K$ on the central interval. The exact convolution identity
$$
 \Lambda=\Lambda_{\le U}+\mu_{\le U}*\log
 -(\mu_{\le U}*\Lambda_{\le U}*1)
 +\mu_{>U}*(\Lambda_{>U}*1)
$$
follows from $\log=1*\Lambda$ and $1*\mu$ being the convolution identity. Take for instance $U=P^{.003}$. In the last (positive-sign) term the genuine Möbius factor is $n$, the independent coefficient is $\alpha_m=\sum_{b|m,b>U}\Lambda(b)\le\log m$. In the other leg open the entire identity $\Lambda(q)=\sum_{d|q}\mu(d)\log(q/d)$. Equation (1), now multiplied by the signs $\mu(d)$, deletes the specified simultaneous $n,d$ block of the actual signed statistic. It does not delete other geometries of that term or the other Vaughan terms and does not show that two primes exist. Restricting $mn$ to target units is essential to the proof and was made before the identity, not after selecting its favorable pieces.

## 1. Uniform treatment of the two congruences

One may first work on independent rectangles whose products lie in $I$, with no logarithm. The endpoints and log weight are restored below. For $a|P-1-mn$ and $d|P-mn$, one has $(d,aP)=1$: a common prime of $d,a$ would divide the difference $1$, and a common prime of $d,P$ would divide $mn$. The tag condition is the exact unit-character expansion
$$
 {\bf1}_{mn\equiv P-1\bmod a}
  ={1\over\phi(a)}\sum_{\xi\bmod a}\overline{\xi(P-1)}\xi(m)\xi(n).
$$
Thus the shift in the large-modulus problem is the integer $P$, independent of the modulus; the other large residue $P-1$ has not been treated as small or as a unit modulo an unrelated modulus. We retain the restriction $(d,aP)=1$ on both sides of the centered dispersion comparison.

We use only the classical zero-free region, Landau–Page uniqueness and Siegel's theorem (e.g. Davenport, *Multiplicative Number Theory*, chapters 14 and 20; for the uniform formulation of Page see [Drappeau–Fiorilli, section 2](https://drappeau.perso.math.cnrs.fr/documents/moment1-sw.pdf)). Take height $T=\exp(\sqrt L)$ and modulus bound $T$; every primitive character in this rectangle is zero-free up to $2T$ in $\sigma\ge1-c/\sqrt L$ after fixing $c>0$ small enough, except possibly the one character with conductor $f\le T$ and its potential real zero. This assertion concerns the primitive Dirichlet functions; the zeta pole causes no obstruction for its reciprocal. If there is an exceptional $f$, temporarily remove all tag labels dividing it, **preserving the original normalization**. Dropped products $a$ require at least one such $\ell|P-1-x$. Since $W\ll_K L^K$ on $x\in I$ and $\alpha\ll L^C$, the loss even after taking the modulus absolute values and dropping all signs is at most
$$
 L^{O_{C,K}(1)}\sum_{\ell|f,\ \ell\ {\rm tag}}
 (P/\ell+1)^{1/2}
 \left(\sum_{x\in I}\tau(x)^2\tau(P-x)^2\right)^{1/2}
 \ll P L^{O_{C,K}(1)}e^{-L^{.1}/2}.
$$
Here $\sum\tau(x)^4\ll P L^{15}$, and $f$ has $O(\sqrt L)$ prime factors. This removes no prescribed target. Every retained $a$ is now coprime to $f$.

## 2. The fixed-shift dispersion input: scope and modifications

We use [Fouvry–Radziwiłł, Theorem 1.1, with the equation numbers of arXiv:1811.08672v1](https://arxiv.org/pdf/1811.08672), published in *Annales scientifiques de l'ENS* [55 (2022), 537–568](https://doi.org/10.24033/asens.2501). Their displayed theorem uses $1\le |b|\le X/3$; our $b=P\asymp X$ requires the following proof modifications, not an invocation outside that range.

1. At (25) the numerical $X/3$ ensures $mn-b\ne0$ on the enlarged $m$ smoothing. Here every retained short $n>1$ is coprime to $b=P$, so $mn=b$ is impossible even after enlarging $m$. In the divisor estimates of Lemma 6.1 retain $(n_i,P)=1$ until the divisor bound is applied. For clarity about sign changes in those estimates: when $m$ runs in a progression $m=m_0+jr$ ($r=1$ is allowed), $mn-b$ runs in a progression of step $nr$. Divide by $g=(m_0 n-b,nr)$; then $g|r$ because $(b,n)=1$, and the new residue is reduced. When the progression itself is $m\equiv b\bar n_i\bmod r$, one has
$$g=(n-n_i,r)$$
since $(n_i b,r)=1$. This is exactly the same common factor as in the original bounds, independent of the size of $b$. In the unrestricted $m$ progression $g=1$. To reuse the interval estimate without an endpoint at zero, overbound each sign of the divided absolute values by the entire prefix $[1,C_0 X/g]$ in its reduced class, for a fixed $C_0$ (both $|b|$ and the support products are $O(X)$). The progression step is $nr/g\ll NQ/g$; the prefix length divided by the step is $\gg M/r$, exceeding a fixed power of $P$. Applying their Shiu/divisor Lemma 2.3 on dyadic subintervals or on the full prefix (take its lower endpoint just below 1) therefore has the same $\ll (M/r)L^{O(1)}$ shape, apart from the same divisor factors of $g$ as in their Lemma 6.1. Nonzero signs only double the bound. All later re-enlargements can thus use their original bounds. Their phase separation at (47) uses $|b|/X=O(1)$ for the smooth phase: increasing its fixed bound changes mixed derivative constants by a fixed factor. At (49) the explicit factor is $(1+|b|/X)^{1/2}=O(1)$. The zero frequency, CRT relations and (50) are algebraic. These are the uses of the numerical shift cutoff in the proof of Theorem 1.1.
2. Set their signs $c_d$ in (17) to zero on $(d,aP)>1$. The errors through (49) hold for arbitrary $|c_d|\le1$ on the allowed moduli. Crucially, (50) has $c_{\delta k_1}\overline{c_{\delta k_2}}$: the small-modulus variance (13), (51) may therefore **retain $(\delta,a)=1$** before applying the triangle inequality. One may discard the $k$ coprimalities afterwards. This is the same support-preserving argument used in their proof of Theorem 1.2, but here $d$ ranges over all admissible moduli, not only primes.

Divide $\alpha$ by $L^C$ for now and incorporate the twists and target-unit restrictions separately on each sequence. Let $\beta_n=\mu(n)\xi(n){\bf1}_{(n,P)=1}$ on the chosen short interval (zero elsewhere in $n\sim N$). For $\delta,b',k$ put
$$
 E^*(\delta,b';k)=\sum_{n\equiv b'\bmod\delta,(n,k)=1}\beta_n
 -\phi(\delta)^{-1}\sum_{(n,k\delta)=1}\beta_n ,
\quad
 \mathcal E=\sum_{(\delta,a)=1}\sum_{k\sim Q/\delta}
                  \sum_{b'\bmod\delta}^{*}|E^*(\delta,b';k)|^2 .
$$
Here and below starred residue sums run over units. With $D=\exp(L^{.32})$, the modified Theorem 1.1 bounds the sum of absolute centered errors by
$$
 \ll\sqrt M\left\{(M/Q)\mathcal E+
 L^C(N^2Q+D^{-1/2}MN^2)+D^{C'}X^\epsilon
 [M^{3/20}N^{59/20}Q^{33/20}+N^{23/8}Q^{15/8}]\right\}^{1/2}.
$$
Here the log exponent is a fixed constant of the dispersion bound. With the stated strict rail, their calculation following (56), or direct substitution, makes both bracketed monomials $\ll MN^2 P^{-c_1}$ for some $c_1>0$. Choose $\epsilon>0$ sufficiently small relative to the rail slack: $M>QX^\epsilon$ and $M>N>D^{10}$ hold. All terms except the variance save at least $\exp(-c_2 L^{.32})$ in the resulting bound as a fraction of $P$.

## 3. The small-modulus variance, including all twists

The following elementary zero-free use is only for products of character moduli $a\delta\le\exp(2 L^{.30})$, not for $d\sim Q$. For each $\delta\le Y=\exp(L^{.30})$ with $(a,\delta)=1$ and **nonprincipal** $\xi\bmod a$, every $\xi\chi$ for $\chi\bmod\delta$ is nonprincipal and does not induce the exceptional character: its primitive conductor contains a prime of $a$, coprime to both $f$ and $\delta$. Hence for any short subinterval and $B\le P^{O(1)}$, uniformly,
$$
 \sum_{n\ {\rm in\ interval},\,(n,B)=1}\mu(n)\xi(n)\chi(n)
       \ll N\exp(-c_3\sqrt L).
$$
Indeed use the reciprocal of its primitive Dirichlet $L$-function and remove the Euler factors for primes dividing $Ba\delta$. The classical zero-free-region reciprocal bound in the narrower rectangle $\sigma\ge1-c'/\sqrt L$, $|t|\le T$, is a log power of $T$ (the pole of zeta gives a zero for the inverse). The additional Euler product is $L^{O(1)}$ uniformly: below $\exp(\sqrt L)$ bound $p^{-\sigma}\le e^{c'}p^{-1}$, while above it the $O(L)$ prime divisors contribute negligibly. Truncated Perron up to $T$ at half-integer endpoints of size $\asymp N$ costs $O(NL^{O(1)}/T+L^{O(1)})$ by the bounded coefficients. Moving the contour gives $N^{1-c'/\sqrt L}L^{O(1)}$ and the horizontal tail; $\nu>0$ is fixed. Differences of prefixes allow all the intervals used here. This proof does not presuppose cancellation for arbitrary coefficient twists or for moduli of size $Q$.

By residue orthogonality $E^*$ is bounded by this estimate for $\delta\le Y$ (use $B=Pk$). For $Y<\delta\le2N$, Parseval, or the elementary variance bound, gives
$$
 \sum_{b'}^* |E^*(\delta,b';k)|^2\le
 (1+N/\delta)\sum_{n\sim N}|\beta_n|^2 \ll N^2/\delta .
$$
For $\delta>2N$ that sum is $\ll N$. Thus using $\#\{k\sim Q/\delta\}\ll Q/\delta$ for $\delta\le2Q$ and zero beyond,
$$
 \mathcal E\ll N^2Q\big(Y e^{-2c_3\sqrt L}+Y^{-1}\big)+NQ\log(2Q).
$$
Consequently each nonprincipal $\xi$ costs at most $P\exp(-c_4 L^{.30})$ in absolute centered discrepancy. Its ordinary principal progression term also has absolute $d$-sum $\ll P e^{-c_5\sqrt L}$: apply the same Möbius bound with $\chi=1$ and $B=Pd$, bound the $m$-sum by $O(M)$, and use $\sum_{d\sim Q}1/\phi(d)\ll1$. Thus here even the **uncentered** sums have the saving. With $1/\phi(a)$ normalization the cost per tag is no larger than the supremum over its nonprincipal characters; the number of tags is at most $\exp(O_K(L^{.2}))$.

For the principal $\xi\bmod a$ one needs only arbitrary logarithmic saving **per tag**, since it occurs once, and $\sum_{a\in\mathcal A}1/\phi(a)\ll_K1$ by the reciprocal mass bounds. Repeat the variance calculation with $Y=L^B$, where $B$ is arbitrarily large but fixed. For $\delta\le L^B$, the ordinary Siegel–Walfisz bound for twisted Möbius is $O_{B,R}(N L^{-R})$ for arbitrary fixed $R$, including the restrictions $(n,aPk)=1$. To see uniformity, remove the latter factors by the same Euler product in the narrower classical rectangle; Siegel's real-zero bound $1-\beta\gg_\eta \delta^{-\eta}$ with $\eta<1/(3B)$ keeps every relevant primitive zero outside the $c'/\sqrt L$ contour for large $P$. The principal-character inverse zeta is included. The larger $\delta$ ranges use the same elementary variance bound. Thus for the one principal $\xi$ both the centered discrepancy and its ordinary progression main are $O_{A,K}(PL^{-A})$. This also explains where ineffectivity is permitted. Summing the two kinds of twists and restoring normalization proves (1) without logarithm on independent rectangles.

## 4. Physical endpoints

Partition each supporting interval into relative $L^{-B}$ bins. This creates $L^{O(B+1)}$ pairs of independent rectangles. On those contained in $mn\in I$ the smooth factor $\log(P-mn)$ may be frozen with error $O(L^{-B})$; $-\log d$ outside the inner sum costs $O(L)$. All absolute source, tag and divisibility weights summed trivially over the central region are $\ll P L^{O_K(C+1)}$, by the divisor moment estimates used in section 1. Rectangles touching an endpoint are confined to $O(PL^{-B})$ integer products $x$: their total absolute contribution is $\ll P L^{-B/2+O_K(C+1)}$ by the same fourth-moment Cauchy bound. Choose $B$ for the requested accuracy, then take the per-rectangle logarithmic accuracy large enough for summation. This proves the sharp central-cut statement.

The classical unbalanced dispersion theorem is foundational here; this application does not improve its exponent or bound the balanced remainder. The specific additional feature is controlling an entire signed modulus block despite a growing family of predecessor twists on **both** legs of the source convolution, for the actual fixed target. A signed lower for the still-untreated blocks or an independently sufficient positive comparison is missing.
