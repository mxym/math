# The two pure exponents at first incidence must eventually be coprime

In the three-label exceptional autonomous component of [Bożek's actual divisor graph](https://arxiv.org/abs/1909.09900v1), suppose the largest label occurs to the first power. The [elementary first-power reduction](EACThreeExponentGaps.md) gives the only remaining form
$$ N=p+q^d=q+Pr=r+p^b,\qquad P=p^e<q<r,\quad d\ge2,\ e\ge1. $$
Here $p,q,r$ are distinct odd primes. **Only finitely many such centers have $\gcd(b,d)>1$.** No fixed-prime or bounded-exponent hypothesis, no numerical cutoff, and no claim about the coprime branch. The proof uses the powerful numerator in an asymmetric Padé approximation, not an assumption of uniformity of Roth's theorem in a moving field.

## 1. Uniform parameters

Set $B=P-1$. The exact identity is $B(q^d+p)+q=Pp^b$. Thus
$$ 0< Pp^b/(B q^d)-1=(p+q/B)/q^d\le2q^{1-d}. $$
Apply [Matveev](https://doi.org/10.1070/IM2000v064n06ABEH000314) in the weighted-exponent rational form [Bugeaud, Thm. 2.2](https://ir.library.osaka-u.ac.jp/repo/ouka/all/68354/ojm55_02_315.pdf), with bases $p,B,q$, exponents $e+b,-1,-d$ and $q$ last. Taking the bounding heights as $\log p,\max(1,\log B),\log q$, its coefficient parameter is $O(d)$: $P<q$ and $p^b<N<2q^d$. The resulting bound is
$$d\ll (\log p)(\log P)(1+\log d),\qquad d\ll(1+\log P)^3.$$
If $P$ is bounded, $p,e,d$ each have finitely many possibilities. For each fixed triple choose $u\equiv b+e\bmod3$, $0\le u<3$. The polynomial $B X^d+X+pB$ is squarefree: a common root with its derivative would have $z=-dpB/(d-1)$ but $|z|^{d-1}=1/(Bd)$. The cubic cover $BX^d+X+pB=p^uY^3$ is geometrically integral by Eisenstein at a simple root; Riemann–Hurwitz gives genus $d-1-(\gcd(3,d)-1)/2\ge1$ (ramification 3 at all simple roots; the infinity contribution is $3-\gcd(3,d)$). Siegel gives only finitely many integral points. We may therefore assume $P\to\infty$ and always use $g\le d\ll(1+\log P)^3$.

Suppose $g=\gcd(b,d)\ge2$, and put $m=d/g$, $n=b/g$, $U=q^m$, $M=p^n$. Write
$$ \alpha=(1-1/P)^{1/g},\quad F=M/\alpha,\quad F^g-U^g=p+q/(P-1). \tag{1} $$
Then $M<U<F<2M$. Since the difference $U-M$ of distinct odd positive integers is at least 2, $U^g-M^g\ge2g M^{g-1}$. But $B(U^g-M^g)=M^g-(pB+q)<M^g$, so $M>2gB>P$ and $n\ge e+1$. In particular $M\ge pP$. We will use
$$ 0<F-U\le \frac{p+q/(P-1)}{g U^{g-1}}. \tag{2} $$

## 2. Wide regime: integrating the asymmetric Padés

Suppose $U>P^{100}$. The Padé integrality and determinant lemmas of [Corvaja–Zannier (2013), Lemmas 2.4 and 2.5, pp. 725–727](https://www.numdam.org/item/10.5802/aif.2774.pdf) give, for positive integer indices $r_0,s$, polynomials $G,H$ with **integer** coefficients (after their supplied common multiplier), of degrees at most $s,r_0$ respectively. Put $j=r_0+s$. Their coefficient sizes are at most $(2g)^{4j}$; $G(z)-(1-z)^{1/g}H(z)$ has order $\ge j+1$ at 0. Passing to the simultaneous neighboring indices $(r_0+1,s+1)$, the two pairs have nonzero determinant at every nonzero $z$, even after clearing their respective multipliers. For $z=1/P$ these facts imply
$$ |G(z)|+|H(z)|\le C_g^{j+1},\qquad |G(z)-\alpha H(z)|\le C_g^{j+1}P^{-j-1},\quad C_g=(20g)^{10}. $$
Indeed the coefficients of $(1-z)^{1/g}$ have absolute value $\le1$; the coefficients of the difference are bounded by $(j+2)(2g)^{4j}$ and its tail is geometric at $1/P$. In particular $\log C_g=o(\log P)$ uniformly.

Take $t=\lfloor n/e\rfloor$, $s=\lceil t/8\rceil$, $r_0=t+s$ and $z=1/P$. Both here and at the neighboring indices ($s$ increases by 1, $t$ unchanged),
$$ D=P^s[U G(z)-M H(z)]\in\mathbb Z. $$
This is because $P^t\mid M$ and the higher-degree polynomial multiplies $M$. At least one of the two integers is nonzero by the determinant lemma. Yet
$$ |D|\le C_g^{t+2s+1}\big(U P^{-t-s-1}+P^s|U\alpha-M|\big). \tag{3} $$
The wide condition gives $t\ge99$ and $t/8\le s\le0.15t$ at either index. Also $P^t\le M<U<2P^{t+1}$, and $C_g^{t+2s+1}\le P^{t/50}$ eventually, uniformly. If $(g,m)\ne(2,1)$, (2), $q=U^{1/m}$ and $p\le P<U^{1/100}$ give $|U\alpha-M|\ll U^{-0.49}$: for $g=2$ we have $m\ge2$, and for $g\ge3$ even $q=U$ is harmless. Both terms after multiplication in (3) tend to zero. Contradiction.

For $(g,m)=(2,1)$ use instead the exact completed square
$$ W=2(P-1)q+1,\quad V=2P M,\quad W^2=V^2(1-1/P)+1-4p(P-1)^2. $$
Thus $W\asymp V$ and $|W-\alpha V|\ll pP^2/W\ll W^{-0.9}$ in the wide regime. Put $t=1+\lfloor n/e\rfloor$, so $P^t\mid V$ and $2P^t\le V<2P^{t+1}$. Take again $s=\lceil t/8\rceil$, but swap the Padé indices, so $\deg H\le s$, $\deg G\le t+s$. Use the integer $P^s[W H(z)-V G(z)]$ and its neighbor. The same bound as (3), with $V$ in the first term and $|W-\alpha V|$ in the second, contradicts their nonzero determinant.

## 3. Narrow regime: a rational gap with bounded truncation degree

Now $U\le P^{100}$. Set $k=\lfloor n/e\rfloor\in[1,100]$, $v=n-ke$, $M=P^k p^v$. We may hold $k$ fixed. Also $m\le k$: indeed $U=q^m>P^m$ but $U<2M\le(2/p)P^{k+1}<P^{k+1}$. Use the positive binomial expansion
$$ F=M\sum_{j\ge0} a_j P^{-j},\quad a_0=1,\quad a_j=\frac{(1/g)(1+1/g)\cdots(j-1+1/g)}{j!},\quad 1/(gj)\le a_j\le1. $$
Write $S_J$ for the sum through $J$, including $M$. For $J=k$, its denominator divides $k! g^k$. For $J=k+1$, its denominator divides $(k+1)!g^{k+1}p^{e-v}$. Fix the truncation:
- if $p^{e-v}\ge P^{1/4}$, use $J=k$;
- otherwise use $J=k+1$, so $M>P^{k+3/4}$.

The positive tail satisfies
$$ M P^{-J-1}/[g(J+1)]\le F-S_J\le2 M P^{-J-1}. \tag{4} $$
The upper bound tends to zero faster than the inverse allowed denominator: for $J=k$ it is $O(P^{-1/4})$, and for $J=k+1$ it is $O(P^{-1})$. The factor $g^{k+1}$ is polylogarithmic in $P$ uniformly since $k$ is bounded.

### Cases $(g,m)\ne(2,1)$

The ratio of the upper bound in (2) to the lower bound in (4) is at most
$$ (J+1)(p+4 M^{1/m}/P)P^{J+1}/M^g. \tag{5} $$
Here $q=U^{1/m}\le2M^{1/m}$. We check it tends to zero. For $J=k$, the second summand is $O(P^{k-(g-1/m)k})=o(1)$; the first is $O(pP^{1-(g-1)k})$. For $g\ge3$ this tends to zero except possibly $g=3,k=1,p\asymp P$; if $k=1$, $n>e$ forces $e\ge2$ and $p\le P^{1/2}$. For $g=2$, $m\ge2$ and hence $k\ge2$; the only possible boundary is $k=2,e=1$ (otherwise $k\ge3$ or $p\le P^{1/2}$). Then $n=2,m=2$, i.e. $b=d$, impossible because $q^d-p^d\ge(q-p)q^{d-1}$ and $r\ge q^d-p^d$ would imply $pr>q^d$ whereas $pr\le N-q=q^d+p-q<q^d$. For $J=k+1$, substitute $M>P^{k+3/4}$ in (5). Its first term is $O(P^{k+3-g(k+3/4)})$ and its second $O(P^{k+1-(g-1/m)(k+3/4)})$. Both decay for $g\ge3,k\ge1$, or $g=2,m\ge2,k\ge2$. This checks (5) uniformly, so $0<U-S_J\le F-S_J$ eventually, an impossibility for the integer $U$ by the displayed denominator bounds.

### Remaining $(g,m)=(2,1)$

Here $U=q$, $a_j=\binom{2j}j/4^j$ are fixed dyadic rationals. With $\delta=F-U$, exactly
$$ \delta=(p+U/(P-1))/(F+U),\qquad P\delta=\tfrac12(1+pP/M)+o(1), $$
uniformly: $U/M,F/M\to1$ and $pP/M\le1$. For $J=k+1$, (4) or its leading coefficient gives $P(F-S_{k+1})=a_{k+2}p^v/P+O(P^{-1})\le a_{k+2}/p+o(1)<1/2$; thus $U-S_{k+1}<0$ and its size is $O(1/P)$, too small for a nonzero difference.

Suppose $J=k$. Then $P(F-S_k)=a_{k+1}p^v(1+O_k(P^{-1}))$. If $p^v\to\infty$ this dominates bounded $P\delta$; (4) and (2) still put $|U-S_k|$ below the denominator threshold. Otherwise pass to a fixed odd value $L=p^v$. For $k=1$ we have $v\ge1$ as $n>e$, thus $a_2 L\ge9/8>1\ge(1+pP/M)/2$. For $k\ge2$, after a subsequence $pP/M$ tends to 0 or equals 1: if $p$ stays bounded then $e\to\infty$, $n\ge2e$; if $p\to\infty$, $n=e+1$ gives 1 and $n\ge e+2$ gives $\le1/p$. Neither $1/2$ nor $1$ equals $a_{k+1}L$: for $j\ge2$, $\binom{2j}j$ has 2-adic valuation at most $j$ (from $\binom{2j}j=2^j(2j-1)!!/j!$), so the reduced denominator of $a_j$ is divisible by 4, unchanged by the odd factor $L$. The difference $U-S_k$ is therefore nonzero and tends to zero with bounded denominator, again impossible.

Every possibility for unbounded $P$ with $g\ge2$ has now been eliminated. The asymmetric use of $P^t\mid M$ is essential in the wide case; an ordinary irrationality exponent near 2 would not cover all the boundary cases. The conclusion does not exclude three-label components with $\gcd(b,d)=1$ or imply Goldbach.

For the related September 2026 terminal-component claim, see the scope note in [the exponent gaps](EACThreeExponentGaps.md). The named Padé lemmas and the weighted logarithmic inequality are older inputs; the claim here is confined to the actual shared-pure-exponent branch. No priority inference from a bounded comparison is made.
