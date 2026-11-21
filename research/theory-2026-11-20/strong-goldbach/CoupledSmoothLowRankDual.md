# A low-rank dual and a prescribed-target triprime test for coupled smooth cutoffs

Let $B(s,t)$ be any fixed real smooth function on the closed positive quadrant, with a smooth compact extension to the plane, identically zero there when $s\ge1/2$ or $t\ge1/2$ in the positive quadrant. In particular its supported upper faces are flat; there is no support restriction in the extension at the axes $s=0,t=0$. We do **not** assume a finite sum of separated templates, monotonicity or positivity. For a one-variable test put $Ef=f(0)$, $Cf=-f'(0)$ and $Df=Cf-2Ef$. Define
$$ M(B)=(E\otimes C+C\otimes E-C\otimes C)B.                         \tag{1} $$
There are two different assertions.

* If $M(B)>0$, the bare composite-by-composite divisor response cannot be nonnegative on all of the rank pairs $3\times3,3\times2,2\times3$. This conclusion is valid even for actual central pairs over true even targets, not just for hypothetical profiles. The proof gives a positive weighted angular dual.
* For **symmetric** $B$, every sufficiently large prescribed even $P$ has a signed negative response of size $M(B)+O_B(h)+o_{P;h,B}(1)$ in absolute natural units, when one leg is tested by a universal nonnegative, polynomially rough, unbalanced **true triprime** weight. Here $h>0$ is small and fixed first. The response is that of the actual two-divisor proxy. Its other leg can be a prime: the resulting exact prime-or-composite debit is detailed below. This is not a negative bound on the prime-inert residual by itself and proves no Goldbach positivity.

## 1. The actual calibrated main

Set $I=[P/3,2P/3]$, $L=\log P$, $y=P-x$, and $X_P=|I|\mathfrak S(P)$ with the standard two-prime singular series for even $P$. For clarity use the common $L$ for all logarithmic weights and exponents. Set $s_d=\log d/L$ and write $A_x f=\sum_{d|x}\mu(d)f(s_d)$. Then define
$$ U_B(x,y)=L^2(A_x\otimes A_y)B,\qquad
 V_B(x,y)=L^2[(A_x-\mathbf1_{x\ {\rm prime}}E)\otimes
                    (A_y-\mathbf1_{y\ {\rm prime}}E)]B. $$
On central primes the corresponding leg of $V_B$ vanishes exactly; on composite pairs $V_B=U_B$. No $\Lambda$-weighted powers are called primes here. If $G_L(P)=L^2\#\{x\in I:x,y\ {\rm prime}\}$, then uniformly for large even $P$
$$
 B(0,0)G_L(P)=M(B)X_P+\sum_{x\in I} V_B(x,y)+o_B(X_P).                \tag{2}
$$
Thus $M$ is precisely the analytic reserve in this ledger; a positive comparison to the genuine pair count also requires $B(0,0)>0$. Using $L$ instead of the two prime logs changes the genuine count by relative $O(1/L)$ on this central interval, including when it is zero.

Here are details of the elementary calibration for a general coupled weight. Expanding both divisors, the CRT density for $d|x,e|y$ is $\mathbf1_{(d,e)|P}/[d,e]$, with error $O(1)$ per pair. The summed floor error, including $L^2$, is $o(P)$: for $d,e\le\sqrt P/L^K$ this is immediate with large fixed $K$; if either is above this point the multiplier is $O_{B,A,K}((\log L)/L)^A$ by upper-face flatness. There are only $O(P)$ candidate pairs. For a prime-marked single-divisor sum, apply maximal Bombieri–Vinogradov in the residue $P\bmod e$ below $\sqrt P/L^K$, with $K$ chosen for a sufficiently large fixed log saving. For $e$ sharing $P$ no central prime can be that residue (it would divide $e\le\sqrt P$). Above the cutoff the same flat bound times $\sum_{e\le\sqrt P}(P/e+1)$ suffices. Partial summation for unweighted primes gives $\int_I dt/\log t=|I|L^{-1}(1+O(1/L))$ for the main; the signed divisor scalar multiplying it is evaluated next, not bounded termwise at this point.

For completeness, the two remaining scalar functionals on fixed smooth tests are
$$
 L\sum_{(d,P)=1}\frac{\mu(d)f(s_d)}{\phi(d)}
       =\mathfrak S(P)(Cf+o_f(1)),\quad
 L^2\sum_{d,e}\frac{\mu(d)\mu(e)\mathbf1_{(d,e)|P}}{[d,e]}B(s_d,s_e)
       =\mathfrak S(P)((C\otimes C)B+o_B(1)).                         \tag{3}
$$
A direct joint Mellin verification also records uniformity in $P$. Write a compact smooth extension as the Fourier inverse of $e^{s+t}B(s,t)$ times $e^{-s-t}$, with phases $e^{-ius-ivt}$. The density series has Euler factors at exponents $z=(1+iu)/L,w=(1+iv)/L$
$$ 1-p^{-1-z}-p^{-1-w}+\mathbf1_{p|P}p^{-1-z-w}. $$
Factor $1/[\zeta(1+z)\zeta(1+w)]$. The residual Euler product at $z=w=0$ is $\mathfrak S(P)$, since its local factor is $(1-2/p)/(1-1/p)^2$ for $p\nmid P$ and $(1-1/p)^{-1}$ for $p|P$. In dimension one the unfactored factors are $1-p^{-z}/(p-1)$ for $p\nmid P$ and $1$ otherwise; removing $1/\zeta(1+z)$ gives the same residual product at zero. On $|u|,|v|\le L^{1/4}$ the residual products equal $(1+o(1))\mathfrak S(P)$ uniformly. Indeed the non-target factors have uniformly summable logarithmic derivative $O(\log p/p^2)$ on $\operatorname{Re}z,\operatorname{Re}w\ge0$ near zero (separately bound finitely many small $p$); at $p|P$ allow $O(\log p/p)$, whose sum is $O(\log L)$ by splitting at $L^2$ and applying Mertens below. These factors stay bounded away from zero primewise for large $p$; the finite small prime factors are nonzero near zero since $P$ is even. Use $1/\zeta(1+z)=z(1+O(|z|))$ there. Outside the frequency window use the absolute unnormalized series, bounded by $L^{O(1)}$ from the Euler factors at real exponents $1/L$ (and the extra $\prod_{p|P}(1+O(1/p))$). Rapid Fourier decay pays all losses. Fourier inversion now identifies the multipliers $(1+iu)$ and $(1+iu)(1+iv)$ exactly with $C$ and $C\otimes C$ at the origin. This proves (3) without a tensor-product assumption on $B$. Expanding $V_B$ and inserting the two prime-marked terms proves (2). This is the usual smooth divisor-sum mechanism, cf. [Green–Tao, Appendix D](https://arxiv.org/abs/math/0606088); the short modulus range and the varying exceptional primes have been checked here directly.

## 2. A positive dual concentrated on ranks two and three

For an angular prime profile $u=(u_1,\ldots,u_k)$ with positive entries summing to one, put $A_u f=\sum_{S\subseteq[k]}(-1)^{|S|}f(\sum_{i\in S}u_i)$. At a semiprime $(b,1-b)$ with $b<1/2$, $A_u f=f(0)-f(b)$, which tends to $Ef$ as $b\uparrow1/2$. At a triprime $(t,a,1-t-a)$ with $a,t>0$, $a+t<1/2$, the exact response is
$$ \Delta_{t,a}f=f(0)-f(t)-f(a)+f(t+a). $$
For $0<h<1/20$ define positive mixtures **of these evaluations**
$$ D_h f=\frac1h\int_h^{2h}\frac2t\int_h^{1/2-t}\Delta_{t,a}f\,da\,dt,\qquad
 E_h f=\frac1h\int_{1/2-2h}^{1/2-h}\left(f(0)-f(b)\right)db.        \tag{4}
$$
They do not mean positive functionals on arbitrary nonnegative $f$. One has
$$ |D_h f-Df|+|E_h f-Ef|\ll h\|f\|_{C^2}.                             \tag{5}
$$
Indeed $\Delta_{t,a}f/t=f'(a)-f'(0)+O(t\|f''\|_\infty)$, and $2\int_0^{1/2}(f'(a)-f'(0))da=-2f(0)-f'(0)$ as $f(1/2)=0$. Removing the endpoint intervals costs $O(h\|f\|_{C^2})$ after averaging, and the claim for $E_h$ follows from $f(1/2)=0$. In particular $D_h$ has bounded operator norm on $C^2$, although the total underlying positive sampling mass is of order $1/h$. Formula (5) for $B$ is valid successively in each variable in the $C^{2,2}$ norm.

The exact identity
$$ -M(B)=(D\otimes D+D\otimes E+E\otimes D)B                         \tag{6} $$
therefore makes $-M(B)+O(h\|B\|_{C^{2,2}})$ a positive mixture of genuine composite-profile responses at the three stated rank pairs. If $M(B)>0$, fix $h$ sufficiently small, then at least one pair has response strictly negative on an open product of two angular cells. All coordinates can be kept distinct, away from their endpoints, with the first factor of each chosen triple in $(h,2h)$. To obtain actual integers, apply the prime-product PNT on the two legs separately in proportional rectangles in $(x,y)$ inside $N\le x+y\le2N$, $x\in[(x+y)/3,2(x+y)/3]$. Their macroscopic lengths are tied by this polygon; after averaging targets the two angular variables are independent on each rectangle. The log exponents with denominator $L=\log(x+y)$ converge uniformly to the own-argument exponents. The selected squarefree odd products automatically yield even targets; collisions of a common prime cost $o(N^2/\log^2N)$ since every selected prime exceeds a fixed power of $N$. This proves the asserted true adverse cells (weighted lower mass on the dyad), **not** a fixed-$P$ lower for any specified pair of ranks. See [the rank-law PNT transfer](https://github.com/mxym/math/commit/5aeca28bc339a9a27fa1200758e45a71ed2b1ce2).

## 3. A signed fixed-target test

Define the nonnegative weight $T_h(x)$ only on squarefree unbalanced triprimes. For each ordered labeling of the three primes of $x$, form their own-log angles $(t,a,1-t-a)$ and add $2t a(1-t-a)/(h t)$ if $h<t<2h$ and $h<a<1/2-t$. Otherwise add zero. Summing every qualifying labeling is intentional, not a uniqueness assumption; $T_h\ll1/h$. Then for every fixed $B,h$ and all even $P\to\infty$,
$$
 \frac{1}{X_P}\sum_{x\in I} T_h(x)U_B(x,P-x)
       =(D_h\otimes C)B+o_{B,h}(1).                                  \tag{7}
$$
In particular for symmetric $B$ the right side equals $-M(B)+O_B(h)+o_{B,h}(1)$ because $(D\otimes C)B=(C\otimes C-2E\otimes C)B=-M(B)$. No target averaging, prime-pair asymptotic or distribution of the individual constituent prime pairs is invoked in (7).

Here is the arithmetic verification, including the late modulus edge. The marked $x$ has three distinct primes all $\gg_h P^{h}$ up to a constant depending on $h$. One may discard $(x,P)>1$ at power saving using $\sum_{p|P,\,p\gg P^h}(P/p+1)\ll_h P^{1-h}L$ and $\tau(P-x)\ll P^{o(1)}$. Open the divisor $d|x$ inside its three prime slots (at most eight choices), but **do not open** the actual prime factors on the partner side. For the remaining $e|P-x$, use the signed finite-rank convolution source. To spell out the distribution used, fix a slot choice and log-fine rectangles of relative mesh $1+L^{-B_0}$ in the three prime variables. The constraints in (4), squarefreeness and the paired boundary $x\in I$ have jumps only along a fixed number of affine log inequalities; off their boundaries the weight and the angles have bounded derivatives for fixed $h$. Boundary rectangles have total positive mass $O_{h,B_0}(P L^{-B_0+C}+P^{1-c(h)})$, by fixing all other slots and dropping primality on the one in a narrowed interval. Coincident labels can instead be treated the same way or removed as a power saving. Each full-rectangle convolution has maximal centered distribution with arbitrary log saving to $Q=\sqrt P/L^K$ for sufficiently large $K$: the classical primitive large-sieve dyad of conductor $D_0$ is bounded by
$$ L^{O(1)}\left(P/D_0+D_0\sqrt P+P/\sqrt{N_1}+P/\sqrt{N_2}\right), $$
where $N_1,N_2$ are the sizes of the first prime slot and the product of the other two, both polynomial. For small primitive conductor use Siegel–Walfisz on the first prime slot (allowed additional unit masks remove only $O(L)$ primes). The precise dyadic argument including induced characters, boundary rectangles, sign-split and maximal prefix is recorded in [the finite-slot distribution proof, §3 and references there](https://github.com/mxym/math/commit/bf13a6e1d1a9b35bdea274481e7a9c4e2d26a1b8); here a logarithmic gap at the upper endpoint only changes $K$ in the displayed term $D_0\sqrt P$. Apply it to the fixed number of polynomial slots. The number of rectangles is a fixed power of $L$ once $B_0$ is fixed. On each rectangle freeze the smooth $s_d$-dependence of $B(s_d,s_e)$ uniformly in $e$, to error $O_B(L^{-B_0})$. The remaining multiplier depending on $e$ has bounded size and is permitted by summed absolute discrepancy. For the positive boundary envelope its principal has additional loss only $\sum_{e\le Q}1/\phi(e)\ll L$; thus choose $B_0$ large first and $K$ afterward. Equivalently bound the smooth-freezing error by the full positive rectangle envelope times $L^{-B_0}$. Above $Q$ flatness of $B$ in its second argument gives arbitrary inverse powers of $L$ (with fixed powers of $\log L$). Here drop all primality, the weight $T_h\ll_h1$, and sum the eight $d$-slots against $\sum_{e\le\sqrt P}(P/e+1)$; this avoids any longer progression claim.

The resulting actual principal, up to $o_{h,B}(X_P)$, is
$$ L^2\sum_{x\in I} T_h(x)\sum_{d|x}\mu(d)
             \sum_{(e,Px)=1}\frac{\mu(e)}{\phi(e)} B(s_d,s_e). $$
The additional primes dividing $x$ are $\gg_h P^h$, hence deleting them costs $O_h(P^{-h}L^{O(1)})$ in the inner unsigned harmonic sum. The harmless $(x,P)>1$ rows may be restored. Now (3) in one variable applies uniformly to the compact family of slices $B(s_d,\cdot)$: all Fourier seminorms needed there are uniformly bounded. Thus the normalized principal is the ordinary mean of $L T_h(x) A_x[(1\otimes C)B]$ plus $o_{h,B}(1)$; the absolute mass of $L T_h$ is $O_h(1)$ by fixed-rank PNT. Finally (3) in the signed rank-law paper gives exactly the functional $D_h$ in this mean: the $1/3!$ for ordered prime slots cancels the sum over labelings, and $t a(1-t-a)$ cancels the harmonic simplex density. The own-log and $P$-log angles differ by $O(1/L)$ here. This proves (7).

For a symmetric template with $M>0$, set $B_0(s)=B(s,0)$. The literal consequence for any sufficiently small fixed $h$ and each sufficiently large even target is
$$
 \frac{L^2}{X_P}\left[
   \sum_{\substack{x\in I\\y\ {\rm prime}}} T_h(x)(-A_x B_0)_+
   +\sum_{\substack{x\in I\\y\ {\rm composite}}}T_h(x)(-(A_x\otimes A_y)B)_+
 \right]\ \ge\ M-O_B(h)-o_{h,B}(1).                                 \tag{8}
$$
On the first population the proxy really is $L^2 A_x B_0$; its contribution to the prime-inert residual is **zero**. On the second, the proxy equals the residual before taking a sign. Since $T_h$ is nonnegative and bounded for fixed $h$, either true prime-plus-unbalanced-triple rows or true adverse composite-plus-unbalanced-triple rows must pay the displayed debit, in the weighted sense. Formula (7) is a signed statement for their *sum*, not a proof that both populations occur at every target or that either has the needed sign in the unweighted full ledger. In contrast to a synthetic parity example it tests the original primes and divisors. The prime-inert fixed-target sign in (2) remains unresolved.
