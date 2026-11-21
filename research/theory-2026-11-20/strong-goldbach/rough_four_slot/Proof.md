# A signed Type I evaluation and the remaining four polynomial rough slots

Let $P$ be a prescribed large even integer, $I=[P/3,2P/3]$, $L=\log P$, $Z=P^{1/1000}$, $D=P^{.3}$, $U=P^{.003}$, and $X_P=|I|\mathfrak S(P)$ with the usual two-prime singular series. Write $Y_Z(a)=\mathbf1_{P^-(a)>Z}$, $\mu_Z=\mu Y_Z$, and $J_U(n)=\sum_{k|n,\ k>U}\Lambda(k)$. Use exactly the *same* prime-source bulk as the [cross-mark result](https://github.com/mxym/math/commit/312b72605d3fb867dd6ed666537a8db0009f7062):
$$
 H=\sum_{p\in I\text{ prime}}\log p
 \sum_{tb=P-p,\ t>D,\ b>U}\mu_Z(t)Y_Z(b)\log b .
$$
The inner sum is supported on $Z$-rough $P-p$.

Let $\mathcal T_Z$ be the following genuine determinant sum:
$$
 \sum_{\substack{mn+tb=P,\,mn\in I,\,(mn,P)=1\\
           m,t>D,\quad n,b>U}}
  Y_Z(mn tb)\mu(m)\mu(t)\,J_U(n)\log b.                         \tag{1}
$$
It is unconditional that
$$ \limsup_{P\to\infty,\ 2|P}|H-\mathcal T_Z|/X_P<10^{-130}.       \tag{2}$$
The test for a two-prime lower bound may therefore be made on the *four polynomial rough slots*: for example $\mathcal T_Z\ge-.00899X_P$ for every sufficiently large even $P$ would suffice by the linked result. We do not establish this inequality. In (1) the only signs are the true Möbius signs of $m,t$; one may replace $J_U(n)\log b$ exactly by $(J_U(n)\log b+J_U(b)\log n)/2$ by reflection of $I$ and simultaneous exchange of the two products. This symmetry does **not** imply nonnegativity.

There is also an *exact signed asymptotic*. Let $\mathcal T_{\mathrm{free}}$ use the same (1), but replace $Y_Z(mn tb)$ by $Y_Z(tb)$, leaving the artificial source $mn$ unrestricted apart from the stated size/unit conditions. With ordinary Dickman and Buchstab functions $\rho,\omega$,
$$ \frac{H-\mathcal T_{\mathrm{free}}}{X_P}\longrightarrow
 J=\int_{300}^{997}\rho'(u)(1000-u)\omega(1000-u)\,du<0,
 \qquad |J|\le700\rho(300).                                         \tag{3}$$
Indeed the two full Vaughan Type I pieces here respectively tend to $J$ and $0$ in units of $X_P$, before their prescribed subtraction. For the all-four-rough variant the corresponding net principal is $cJ$, where
$$ c=e^{-\gamma_E}\Big[698\rho(300)+\int_0^{300}\rho(u)\,du\Big].   \tag{4}$$
We give an explicit **fixed**, not arbitrarily log-saving, linear-sieve error for that variant. In particular (2) does not assert the sign of its tiny Type I term. No zero-free hypothesis beyond the classical inputs below, no conditional tag amplifier, and no averaging in the target are used.

## 1. Opening the actual source, and a two-factor distribution bound

Write $x=tb\in I$ and $y=P-x\in I$. Impose $(x,P)=1$: removed prime-source rows have $p|P$ and negligible divisor-weighted cost. Replacing the source prime-log by $\Lambda(y)$ costs $P^{1/2+o(1)}$ by the proper power bound. We may therefore use either the unrestricted source or the source additionally restricted to $Y_Z(y)=1$, since all true central primes are $Z$-rough. The exact unequal-cut Vaughan identity is
$$ \Lambda=\mu_{\le D}*\log-\mu_{\le D}*\Lambda_{\le U}*1+
 \Lambda_{\le U}+\mu_{>D}*(\Lambda_{>U}*1).                       \tag{5}$$
The isolated third function vanishes on $I$. The last term is exactly the stated $\mathcal T$ in each variant. Denote the first two terms before subtraction by $I_1,I_2$; we evaluate them with the same reflected $t,b$ forms, not in a product-density surrogate.

Here is the distribution fact used in both variants. On rectangles of dyadic scales $T,B$ with $TB\asymp P$, $T\gg P^{.3}$, $B\gg P^{.003}$, the convolution of either sign-indicator of $\mu_Z(t)$ and $Y_Z(b)$ (also with target-unit masks and log weights by partial summation) has complete centered Bombieri–Vinogradov distribution on unit classes to level $Q=P^{.41}$. More precisely, for any fixed $A,C$ the sum of maximum unit-residue discrepancies with weight $\tau(k)^C$, $k\le Q$, is $O_{A,C}(PL^{-A})$, uniformly for slot subintervals. The principal in modulus $k$ is **exactly** $\phi(k)^{-1}$ times the sum restricted to $(tb,k)=1$. This is the usual elementary convolution consequence of the multiplicative large sieve, not a statement about true primes beyond their level.

For detail, the sign-indicators are finite sums over at most 1000 ordered-by-size polynomial prime factors, without repetition. Nonprincipal characters of conductor $r\le L^C$ have Siegel–Walfisz cancellation $O_{A,C}(TL^{-A})$ even after a further unit mask $(t,lP)=1$ with $l\le P$. Fix all factors but the largest, and sum that prime on its genuine interval with endpoints enforcing order and the product cut. Prefixes below $Z$ contribute nothing; for endpoints $\ge Z$ use the classical prime Siegel–Walfisz bound with arbitrary log accuracy, summed with the reciprocal products of the other factors, a quantity bounded by a fixed power of $L$. Ties and primes dividing $lP$ remove $O(L)$ choices per remaining product of size $\ll T/Z$, with at most a fixed divisor-power multiplicity; this costs $O_A(TL^{-A})$. The same proof holds for the $b$ orientation: for $Y_Z(b)$ its nonsquarefree exception costs $O(B/Z+\sqrt B)$ even before character weighting, since every repeated prime exceeds $Z$. Removing target primes inside masks does not require the target to have fixed prime factors.

By multiplicative orthogonality keep the principal, and write an imprimitive character with primitive conductor $r$ in modulus $rl$; both polynomials acquire the same extra $l$-unit restriction. On $r\asymp R\ge L^E$, fix $l$, use $1/\phi(rl)\ll L/(R\phi(l))$, Cauchy and the multiplicative large sieve on each polynomial. After summing $1/\phi(l)\ll L$ in aggregate the bound is
$$ L^{O(1)}\{P/R+R\sqrt P+P/\sqrt T+P/\sqrt B\}. $$
All large-conductor terms save arbitrary logs with $E$ chosen large, and small nonprincipal conductors do so by the preceding Siegel–Walfisz bound and $\sum_{r\le L^E}\phi(r)\ll L^{2E}$. Fixed divisor weights on the modulus follow by Cauchy: the complementary bound with twice the divisor power costs $PL^{O(1)}$, since on $Z$-rough $x\le P$ there are at most $2^{1000}$ divisors (also with multiplicity in its prime factors), and a unit class has $\ll P/k+1$ candidates. Constants depending on the fixed cutoff exponent are harmless. This proves the distribution fact. See also the related moving-cutoff convolution proof in the [tagged comparison, §3](https://github.com/mxym/math/commit/6bd046d4); there the Möbius principal itself cancels to log accuracy, which is **not** true here.

Log-fine slot rectangles of relative width $L^{-K}$ separate the coupled endpoints $tb\in I$; discard rectangles within relative $O(L^{-K})$ of either endpoint and then let $K$ be sufficiently large for the required log saving. Their actual contribution is $O(PL^{C-K/2})$ or better by Hölder and fixed divisor moments in $y$ (and bounded multiplicities in $x$), since the total discarded $x$ interval length is $O(PL^{-K})$. The same elementary count with principal modulus weights $\ll L^{O(1)}$ handles principal boundaries. Inside a rectangle the varying term $\log(P-tb)=L+\log(1-tb/P)$ may be separated to error $O(L^{-K})$; the sharp $t,b$ one-slot cuts can simply be kept. This justifies using the distribution fact with the actual smooth log and endpoints, uniformly over $d,k$ below. Physical divisor weights in these estimates have fixed order, even after insertion of the sieve weights.

## 2. The signed average without progression constraints

Write a star on $\sum_{tb}$ for $t>D,b>U,tb\in I,(tb,P)=1$. Let
$$
 M=\sum^*_{tb}\mu_Z(t)Y_Z(b)\log b,\qquad
 M_{\rm abs}=\sum^*_{tb}|\mu_Z(t)|Y_Z(b)\log b.
$$
Then
$$ M/|I|\to J,\qquad M_{\rm abs}/|I|<3\cdot10^6                  \tag{6}$$
for all sufficiently large $P$. To see the second bound, for $B_*=(2P/3)/t\ge U$ the ordinary positive rough count is at most $(1+o(1))B_*/\log Z$ uniformly by the [classical Buchstab estimate](https://arxiv.org/abs/2306.03347) at parameters in a fixed compact subset of $(1,\infty)$, where $0\le\omega\le1$. Also $\sum_{Z\text{-rough }t\le P}\mu^2(t)/t\le\prod_{Z<r\le P}(1+1/r)\sim1000$. This yields the stated bound. The target-unit exclusions in each sum cost $o(P)$: divisibility of $tb$ by any $r|P,r>Z$ has total headcount $O(P L/Z+L)$, and the rough multiplicity and log per integer are bounded by $2^{1000}L$.

For (6), the interval $P/(3U)<t\le2P/(3U)$ can have a clipped $b$ range but contributes $o(P)$, since its positive rough harmonic mass is $O(1/\log Z)$ by the ordinary Buchstab bound. On the remaining range the $b$ sum is uniformly $(|I|/t)[v\omega(v)+o(1)]$, $v=1000-\log t/\log Z\in[3-o(1),700]$, by the same ordinary rough-number asymptotic and partial summation. Fixed-limit harmonic signed measures $\sum\mu_Z(t)/t$ on $u=\log t/\log Z$ converge to $\delta_0+\rho'(u)du$: expand into finitely many distinct primes and use Mertens, or see [rough inversion §3](https://github.com/mxym/math/commit/6f877f72). The same limit holds with $1/\phi(t)$ or further unit deletions $r|Ptb$ on the dummy summation variable, uniformly, since all affected primes exceed $Z$ and the relevant parameters are in fixed compact sets. Here $\rho'(u)=-\rho(u-1)/u<0$ on $u>1$. This proves (6) and the sign and absolute bound in (3).

## 3. Unrestricted artificial source: both Type I principals

For $I_1$ with unrestricted artificial source, apply §1 to the conditions $d|P-tb$, $d\le D$, omitting $(d,P)>1$ since $tb$ is a target unit. Write $M_0=Ptb$ and $c_{M_0}(d)=\mu(d)\mathbf1_{(d,M_0)=1}/\phi(d)$. Its genuine principal multiplier inside $\sum^*\mu_Z(t)Y_Z(b)\log b$ is
$$ \sum_{d\le D}c_{M_0}(d)\{\log(P-tb)-\log d\}
     =\mathfrak S(M_0)+O_A(L^{-A}). $$
This is the [classical uniform signed Euler calculation here, §2](https://github.com/mxym/math/commit/488c8f84): the full moments are zero and $-\mathfrak S(M_0)$, with arbitrary-log tail error at fixed polynomial cuts, uniformly for even $M_0\le P^2$. We apply only this elementary unconditional Mertens calculation, not an over-root assertion. All additional primes of $M_0$ beyond those of $P$ are $>Z$, so $\mathfrak S(M_0)=\mathfrak S(P)(1+O(1000/Z))$ uniformly.

For $I_2$ the congruence is to modulus $dk$, $d\le D,k\le U$, with coefficient $\mu(d)\Lambda(k)$ and no extra log in the source. For each target-unit $k=\ell^j$ coprime to $tb$, the inner $d$ principal is
$$ \phi(k)^{-1}\sum_{d\le D}c_{M_0}(d)(1-\mathbf1_{\ell|d}/\ell). $$
The full unmarked inner sum is $O_A(L^{-A})$, as is its restriction to $\ell|d$: if $\ell\nmid M_0$ use $c_{M_0}(\ell)c_{M_0\ell}(d/\ell)$ on squarefree $d$ and $D/\ell\ge P^{.297}$. Thus $\sum_{k\le U}\Lambda(k)/\phi(k)\ll L$ is affordable with arbitrary-log savings. Equations (5)–(6) now give (3).

## 4. Fixed polynomial roughness in all four slots

In (5) impose $Y_Z(y)=1$. In the $I_1$ progression write $y=dv$, requiring $d,v$ rough; in $I_2$ write $y=dkv$ with $d,k,v$ rough. Sieve the free $v$ using positive upper/lower dimension-one weights of level $E=P^{.10}$ on the primes $h\le Z$ not dividing $P$. Primes dividing $P$ cannot divide $y$ as $x$ is a unit. The choice of upper/lower bounds depends on the signs of $\mu_Z(t)$ and $\mu_Z(d)$; on their separated sign classes the factors $\log b$ and $\log(y/d)$ (when present) are nonnegative. A sieve modulus $e$ is coprime to $d,k$ and $tb$. The actual unit progression in $tb$ is to $de$ or $dke$, always $\le P^{.403}$. Its principal from §1 has $\phi(e)^{-1}$ *separately* and retains $(dk,Ptb)=1$, including any common factors of $d,k$ in $\phi(dk)$. Hence the upper/lower sieve model on each sign class can replace the $e$ multiplier by
$$ V_P(Z)=\prod_{h\le Z,\ h\nmid P}(1-1/(h-1))
   \sim e^{-\gamma_E}\mathfrak S(P)/\log Z $$
with relative error at most $\Delta(100)+o(1)$, $\Delta(100)=2e^{\gamma_E}\rho(99)/100$; this is the same dimension-one linear sieve gap as in the [prescribed-cutoff proof](https://github.com/mxym/math/commit/186ebdd0). The error is charged against the **absolute** principal and is not arbitrarily log-small.

For clarity the combined normalized absolute sieve budget is $<10^{13}(\Delta(100)+o(1))$. Indeed (6) controls $M_{\rm abs}$, $\sum_{Z\text{-rough }d\le D}\mu^2(d)/\phi(d)\le(1+o(1))300$, $\log(y/d)\le L$, and $V_P(Z)L/\mathfrak S(P)\le1000$ eventually. The second piece has in place of $L$ at most $\sum_{k\le U}\Lambda(k)/\phi(k)\le L$ eventually, since $U=P^{.003}$; also $\phi(dk)^{-1}\le(\phi(d)\phi(k))^{-1}$. This calculation pays every diverging logarithm before using a fixed small constant.

For $I_1$, the principal $d$ sum uses the harmonic signed measure from §2 with cut 300 and dummy-variable unit mask $(d,Ptb)=1$. Its zeroth moment is $\rho(300)+o(1)$ and its $\log d/\log Z$ moment is $300\rho(300)-\int_0^{300}\rho+o(1)$. As $\log y/\log Z=1000+o(1)$ uniformly, after including $V_P(Z)$ the multiplier divided by $\mathfrak S(P)$ tends uniformly to $e^{-\gamma_E}[700\rho(300)+\int_0^{300}\rho]$. For $I_2$, rough $k=\ell^j\le U$ have $\ell>Z$. Their factor $1-\mathbf1_{\ell|d}/\ell$ changes the absolute model by a relative $O(1/Z)$ budget; the genuine remaining sum $\sum_{k\le U,\;Y_Z(k)=1,\,(k,Ptb)=1}\Lambda(k)/\phi(k)=(2+o(1))\log Z$ by Mertens with the above large-prime omissions. This gives $2e^{-\gamma_E}\rho(300)$ for its normalized multiplier. Subtracting yields (4), and therefore
$$
 \limsup\left|\frac{H-\mathcal T_Z}{X_P}-cJ\right|\le10^{13}\Delta(100).
$$
Since $|J|\le700\rho(300)$, $|c|<2$, $\rho(j)\le1/j!$, and $e^{\gamma_E}<2$, this proves (2). The companion script verifies the stated uniform error slack with rationals, checks the oriented prime-power local factor, and checks (5) in both source variants on finite inputs. These controls do not supply the missing fixed-target sign in (1).
