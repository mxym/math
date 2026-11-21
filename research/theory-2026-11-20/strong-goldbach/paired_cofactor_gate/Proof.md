# Almost every prime witness in a fixed-target bilinear rectangle has nearby odd, rough, smooth switches on its own cofactor

Fix a large even target $P$, let $L=\log P$, $Y=P^{1/25}$, and take the integers $a$ and primes $\ell$ in the rectangle
$$
 .41P/Y\le a\le .42P/Y,\qquad Y\le\ell\le1.01Y .
$$
Use rows with $a\ell$ squarefree and $(a\ell,P)=1$. Write $m=P-a\ell$; thus $m>P/2$. A **prime witness** is a pair $(a,\ell)$ in this rectangle with $m$ prime. Multiplicities here are pairs, not distinct $m$. For a squarefree integer $m>1$ put $M(m)=\sum_{d\mid m,\ d^2<m}\mu(d)$. All estimates hold at the prescribed $P$.

**Theorem.** There are $\asymp P/L^2$ prime witnesses. Fix $B\ge1$ and $0<\eta<1$. There exists a **fixed** $\epsilon=\epsilon(\eta)>0$ such that, for all sufficiently large even $P$ (threshold allowed to depend on $B,\eta$), at least $(1-\eta)$ of the prime witnesses have at least
$$
 c_\eta\,Y/L^{B+3}
$$
distinct prime alternatives $\ell'$ with the **same integer $a$**, $|\ell'-\ell|\le Y/L^B$, in the original rectangle. For each alternative $a\ell'$ is again squarefree and target-coprime, and the actual $m'=P-a\ell'$ is squarefree, has $M(m')<0$, and has an **odd** number of prime factors, all in $(P^\epsilon,\sqrt{m'})$. In particular it is a composite of rank between 3 and $\lfloor1/\epsilon\rfloor$. The sign condition is on its exact own-log half divisor sum, not merely a parity heuristic.

The hundreds or millions of possible alternatives implicit in the growing lower bound need not have distinct large cofactors: the theorem requires them all to keep the original cofactor. The long integer $a$ is **not asserted prime** or prime-like. This result gives neither a binary Goldbach representation nor a positive count of prime witnesses when restricting to prime $a$.

## The progression input and the absolute cofactor norm

Partition the short interval into $O(L^B)$ disjoint bins of width at most $Y/L^B$. For a bin $I$ and admissible $a$, define
$$
 R_z(a,I)=\sum_{\substack{\ell\in I\ {\rm prime}\\a\ell\ {\rm squarefree},\ (a\ell,P)=1\\
               m=P-a\ell\ {\rm squarefree},\ P^-(m)>z}} M(m).
$$
Here admissible $a$ means in the displayed long interval; inadmissible pair terms are simply omitted. We prove
$$
 \sum_{a,I}|R_{P^\epsilon}(a,I)|\le
       (K(\epsilon)+o_{\epsilon,B}(1))\,P/L^2,\qquad
     K(\epsilon)\longrightarrow0\quad(\epsilon\downarrow0).
 \tag{1}
$$
This absolute value is **outside the full short-prime sum for each separate cofactor and bin**. It follows by taking an arbitrary real long multiplier $\alpha_{a,I}$ with $|\alpha_{a,I}|\le1$, in particular the sign of that whole sum. No estimate for a fixed individual modulus or a fixed individual $a$ is assumed.

The relevant theorem is [É. Fouvry, *Autour du théorème de Bombieri–Vinogradov II* (1987), Corollaire 1, pp. 617–619](https://www.numdam.org/article/ASENS_1987_4_20_4_617_0.pdf). For long and short coefficients supported in $[M,2M]$, $[N,2N]$, $x=4MN$, with the short one satisfying (1.3), the result estimates the reduced-class discrepancy of their convolution at a fixed common shift $|a_0|\le x$, summed with **arbitrary order-$K$ modulus coefficients**. Its sufficient range, with a small fixed power margin, is
$$
 Qx^\delta\le\min(x^{1/2}N^{1/2},x^{4/7}N^{-6/7}),\qquad N\ge x^\delta .
$$
Here the discrepancy in a reduced class subtracts the actual sum restricted to inputs coprime to that modulus, divided by its totient. One may choose the modulus coefficient to be the sign of the discrepancy for each fixed pair of source coefficients, or apply the signed estimate to the collected coefficients directly. This is the **first corollary** (from $S=1$ in (C.1)), not the second, well-factorable corollary used for the larger $5(1-\nu)/9$ level in the [Li–Liu formalization](https://subfish-zhou.github.io/goldbach-lean/blueprint/chap-foundations.html). Sharp Möbius divisor coefficients need not be well-factorable here.

Subdivide both axes into independent fine intervals of relative width at most $L^{-H}$, refining the bins $I$. The shift $a_0=P$ is permitted: using the actual lower endpoints of each pair of intervals for $M,N$ gives $4MN>(1.6-o(1))P$. The short exponent is $1/25+o(1)$, so the two bounds have exponents $.52+o(1)$ and $(4-6/25)/7+o(1)>.537- o(1)$; in particular all moduli $\le P^{.505+o(1)}$ fit strictly. The long coefficient includes $\alpha_{a,I}$ and $1_{\mu^2(a)=1,(a,P)=1}$, and is bounded. The short coefficient is the indicator of primes in an arbitrary fine interval, with any $\ell\mid P$ omitted. It satisfies (1.3) uniformly: for moduli at most a fixed large log power use prime Siegel–Walfisz and interval prefix differences; for larger moduli use $O(N/k+1)$ in a residue and $O(N/\varphi(k))$ for the reduced mean. The coprimality filter in (1.3) on a supplementary integer deletes only its prime divisors, bounded by its allowed divisor factor; deleting the $O(L)$ primes dividing $P$ is negligible in this polynomially long slot. Choosing the small/large threshold large enough gives every fixed log saving asked there. Extra square/sieve factors go in the modulus, **not** into a new variable residue for the SW input. The condition $\ell\nmid a$ may be omitted during distribution: there are $O(P^{1-1/25+o(1)})$ multiple-$\ell^2$ pairs in the rectangle, even before weights bounded by fixed divisor powers. Restore it in physical conclusions.

Freeze the upper endpoint of $d<\sqrt m$ on each fine rectangle at any $\sqrt{P-a_*\ell_*}$ from that rectangle. The total cost of disagreement is $O_J(PL^{-J})$ for any $J$ on choosing $H$ sufficiently large. A changed label has $d\asymp\sqrt P$ with $|m-d^2|\ll PL^{-H}$ and $m=dk$; the number of such $(m,d)$ is $O(PL^{-H}+\sqrt P)$ by counting the integers $k$ within $O(\sqrt P L^{-H})$ of $d$. Count physical $m$ with such a label and use Cauchy with fixed divisor moments of $m,P-m$ to allow all the tuple multiplicities. The union bound is over the single physical boundary strip, **not** separately charged at this size for every fine rectangle. All principal sums below may keep their frozen upper limits, each with logarithm $L/2+O(1)$. All fine-box multiplicities are polynomial in $L$ and can be paid from Fouvry by choosing his log accuracy last.

## The true rough mask and its signed principal sum

Keep $\epsilon>0$ fixed and sufficiently small, $z=P^\epsilon$, and put $D=P^{1/200}$. On the $z$-rough inputs, discarding squarefreeness of $m$ costs $O(P^{1-\epsilon+o(1)}+P^{1/2+o(1)})$: sum over square divisors $p^2\mid m$ with $p>z$ and use the maximal divisor bound for source multiplicities. In this calculation continue to define the auxiliary divisor sum by the same formula on these rare nonsquarefree inputs. Now only $z$-rough squarefree $d$ enter the Möbius sum; restrict to $(d,P)=1$, an actual necessity since $(a\ell,P)=1$.

Sieve the other primes $p\le z$, $p\nmid P$, in $m$. Use the upper and lower fundamental-lemma weights $\lambda^\pm_w$ of level $D$, on squarefree $w$ with factors $\le z$, $|\lambda^\pm_w|\le1$. They bound the roughness indicator by their divisor sums. For example [Koukoulopoulos, *The Distribution of Prime Numbers*, Theorem 19.1](https://dms.umontreal.ca/~koukoulo/documents/publications/primes.pdf) supplies a common pair of weights with relative model error $O(s^{-s/2})$ for $s=\log D/\log z=1/(200\epsilon)$ sufficiently large and the stated fixed dimension bound. Use the upper weights on positive $\alpha_{a,I}\mu(d)$ and the lower on negative for an upper estimate; reverse for the lower estimate. Split the long weights and the modulus sign classes accordingly. Thus one never multiplies an inequality by an unaccounted signed sequence.

The sieve and original moduli are coprime, since $d$ is $z$-rough while $w$ is $z$-smooth. The physical condition $dw\mid m$ gives the reduced class $a\ell\equiv P\bmod dw$. The collected order-one modulus coefficients are bounded (the partition of $dw$ into its smooth $w$ and rough $d$ is unique), with any extra sign split costing a constant. We have $dw\ll P^{1/2+.005}$; use precisely the distribution just verified. Upon reversing the resulting coprime principal averages, fix a genuine source input $n=a\ell$. The modulus denominator is $\varphi(w)\varphi(d)$ and $(wd,nP)=1$. The local sieve probability is $1/(p-1)$ at $p\nmid nP$, zero otherwise. Its dimension-one bound is uniform because omitting primes can only shrink the interval product, bounded above by the ordinary product for odd primes, $\ll(\log y/\log x)(1+O(1/\log x))$ on $x\le p\le y$ (with leading constant 1 in the usual Mertens dimension axiom, enlarging the error constant at small $x$). The same fixed weights from Theorem 19.1 apply for **all** $n$; only their evaluation varies. Thus the $w$-main is
$$
 V_{nP}(z)(1+O(s^{-s/2})),\qquad
 V_{nP}(z)=\prod_{\substack{p\le z\\p\nmid nP}}(1-1/(p-1)).
$$
The signed $d$-main per source is $V_{nP}(z)$ times
$$
 \sum_{\substack{d<D_0,\ P^-(d)>z\\(d,nP)=1}}\frac{\mu(d)}{\varphi(d)},\qquad
 \log D_0=L/2+O(1),
 \tag{2}
$$
with an absolute error $O(V_{nP}(z)\epsilon^{-1}s^{-s/2})$, because the absolute $d$ sum is bounded by $\prod_{z<p\le P}(1+1/(p-1))\ll1/\epsilon$. The sign split does not force the main terms to be estimated absolutely before recombination.

Uniformly in the actual $n$, (2) is $\rho(1/(2\epsilon))+o_\epsilon(1)$, where $\rho$ is Dickman's function. In the absolute harmonic majorant the removal of primes $p\mid nP,\ p>z$ costs $O_\epsilon(L/z)$, and replacing $\varphi(d)$ by $d$ costs $o_\epsilon(1)$ since there are at most $1/\epsilon$ factors, each above $z$. Sorted squarefree tuples or ordered tuples divided by $k!$ give, by prime Mertens and the negligible repeated labels, the limit at $u_0=1/(2\epsilon)$
$$
 \sum_{k\le u_0}\frac{(-1)^k}{k!}
    \int_{\substack{x_1,\ldots,x_k\ge1\\\sum_i x_i\le u_0}}
                  \frac{dx_1\cdots dx_k}{x_1\cdots x_k}.
$$
The domain boundary has zero measure; the slight change in the upper limit on different fine boxes is uniform by squeezing. Differentiating each simplex integral and using $u_0=\sum x_i$ on its moving face gives $u_0 \rho'(u_0)=-\rho(u_0-1)$, with value 1 on $[0,1]$. In particular it is $\rho$, not a derivative or an unsigned reciprocal moment. Its standard bound, or iteration of $u\rho(u)=\int_{u-1}^u\rho(v)\,dv$, gives decay faster than every inverse power of $u$.

We must pay the varying target primes at the same scale as the ordinary prime witnesses. Mertens and $\prod_{p>2}(1+O(p^{-2}))<\infty$ give
$$
 V_{nP}(z)\ll\frac1{\epsilon L}\frac P{\varphi(P)}\frac a{\varphi(a)}
$$
on the source (the extra prime $\ell$ has bounded factor). Uniformly for the long interval of length $\asymp A=P/Y$,
$$
 \sum_{\substack{a\ {\rm in\ the\ interval}\\(a,P)=1}}\frac a{\varphi(a)}
           \ll A\,\frac{\varphi(P)}P .
$$
Indeed expand $a/\varphi(a)=\sum_{g\mid a}\mu^2(g)/\varphi(g)$ and count coprime multiples as $(\text{length}/g)\varphi(P)/P+O(\tau(P))$ when $(g,P)=1$. The reciprocal main converges; the error is $\tau(P)L^{O(1)}$ and is negligible here. With $O(Y/L)$ genuine short primes and $|\alpha|\le1$, the total of the positive local factors over **all** rectangles is therefore $\ll P/(\epsilon L^2)$, not this amount per bin. Together with (2), and with the BV errors already summed, this proves (1) with
$$
 K(\epsilon)\ll \epsilon^{-1}\rho(1/(2\epsilon))+
                    \epsilon^{-2}s^{-s/2}\to0 .
$$
The constants here are fixed before $\epsilon$ is shrunk; the elementary limits in (2) and the final threshold in $P$ may depend on the fixed $\epsilon$.

## Actual prime occupancy and a strict same-cofactor switch

There are absolute constants $c_0,c_1>0$ for which the prime-witness count lies between $c_0P/L^2$ and $c_1P/L^2$. Here is the positive lower without supposing $a$ prime. Fix $\ell\nmid P$ and reverse to primes $p=P-a\ell$ in an interval of length $.01\,P\ell/Y\asymp P$, always $p>P/2$. Any such prime is coprime to $P$. Open squarefreeness of $a$ with $\sum_{k^2\mid a}\mu(k)$, trimming at $k\le L^{K'}$. Over all $\ell$ the omitted tuples cost $\ll(Y/L)(A/L^{K'}+\sqrt A)$, before testing primality; the similarly omitted model tail in $k$ is negligible. When $(k,P)>1$ no prime in this central interval can occur. For the other $k$ sum the usual maximal-prefix prime Bombieri–Vinogradov theorem over the reduced classes $p\equiv P\bmod\ell k^2$. These moduli are below $P^{.04}L^{2K'}$ and are distinct over the retained $\ell,k$ for large $P$, so the two varying endpoints cost arbitrary log savings in total. The principal count per $\ell$ is its positive logarithmic prime integral divided by $\varphi(\ell)$ times
$$
 \prod_{p\nmid P}\bigl(1-1/[p(p-1)]\bigr)+o(1)
$$
in its multiplier (the summed BV error is separate). This factor is bounded below absolutely since $P$ is even; $k$ is smaller than $\ell$ before extension. Replacing the ideal infinite $k$ sum by the true trim or conversely costs $o(1)$ in the local multiplier. The few excluded $\ell\mid P$ and tuples $\ell\mid a$ have negligible total cost. The prime number theorem in the fixed short-slot ratio $[Y,1.01Y]$ now gives the claimed two-sided total. No uniform pointwise prime estimate in each $\ell$-class was used.

At a squarefree prime $m$, $M(m)=1$. At any squarefree $m>1$ of even rank the complementary lower/upper divisor lists have the same signs and half the total alternating sum is zero. If a prime $p\mid m$ exceeds $\sqrt m$ and $m$ is composite, all divisors of $m/p$ lie below $\sqrt m$ and are exactly the lower divisors, again giving zero. Consequently every actual $M(m)<0$ row is a squarefree odd-rank composite, all of whose primes are $<\sqrt m$. On the rough restriction its absolute score is at most $H_\epsilon=2^{1/\epsilon}$. Write $N_p(a,I)$ for the number of prime witnesses and $N_-(a,I)$ for the number of strictly negative rough rows on that cofactor and bin. Since all the prime witnesses survive the fixed rough cutoff,
$$
 (N_p(a,I)-H_\epsilon N_-(a,I))_+\le |R_{P^\epsilon}(a,I)|.
$$
Thus bins with fewer than $N_p/(2H_\epsilon)$ alternatives account for at most $2\sum |R|$ prime witnesses. Independently the bins with $N_p\le Y/L^{B+3}$ contain only $O(P/L^3)$ witnesses, using $O(A L^B)$ cells. Choose $\epsilon$ so small that $2K(\epsilon)<c_0\eta/2$, then let $P$ grow. This proves the theorem, with for instance $c_\eta=(2H_\epsilon)^{-1}$; opposite signs make the switch distinct.

For comparison, [Guo's October 2026 rough-sign problem](https://github.com/aster2024/openai-math-followups#rough-goldbach-parity--sums-of-two-rough-numbers-with-prescribed-liouville-signs) concerns Liouville signs on two rough summands; [Pham's October reflected-prime comparison](https://www.preprints.org/manuscript/202610.3061) studies other signed weights and rough-pair estimates. Our conclusion is a switch between a true prime and a negative sharp half-divisor sum at logarithmically close short primes **on the same long cofactor**, with polynomial roughness and square-root smoothness for the negative rows. It is an unconditional signed compensation inside one explicit bilinear family; there is no transfer here to the increments needed to force two prime summands.
