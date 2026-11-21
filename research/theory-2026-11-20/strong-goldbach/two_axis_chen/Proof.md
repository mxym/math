# A fixed-target parity corner with two low-rank source axes

Let $P$ be a sufficiently large even integer, $L=\log P$, $Y=P^{.04}$, $A=P^{.96}$, $\mathcal L=\{\ell\in[Y,1.01Y]:\ell\text{ prime},\ \ell\nmid P\}$, and $J=[.41A,.42A]$. A *long cofactor* is a squarefree $a\in J$ with all prime factors greater than $A^{.1}$ and $1\le\Omega(a)\le2$. Use the normalized Goldbach singular series $\mathfrak S(P)$ of [the tagged Chen proof](https://github.com/mxym/math/commit/5267e5b7). Set $\kappa=1/50000$. All our auxiliary primes $h$ satisfy $P^\kappa<h<P^{2\kappa}$, $h\nmid P$.

**Theorem.** Fix $B\ge1$, and split $J$ into $\lceil L^B\rceil$ equal intervals $I$. For every $D>0$ all but $O_{B,D}(Y/L^D)$ of the primes $\ell\in\mathcal L$ satisfy the following **simultaneously in every interval** $I$. There are at least
$$
  .01\frac{\mathfrak S(P)|I|}{L\log A}
$$
distinct long cofactors $a\in I$ for which $P-\ell a$ is a prime; there are at least the same number for which $P-\ell a=h p'$ with $p'$ a prime. The latter is an **exact, squarefree semiprime**, with unique small prime label $h$. Thus for a single short prime, and within distance $A/L^B$ on its other coordinate, both true Möbius signs occur abundantly, even after both long cofactors are required to be prime or squarefree semiprime.

Combining this with the [same-long-cofactor signed switch](https://github.com/mxym/math/commit/5267e5b7) gives a literal two-axis corner. For each fixed $\eta>0$, at least a $(1-\eta)$ proportion of the central true prime witnesses $(a,\ell)$ with $a$ a long cofactor have both:
* on the **same $a$**, $\gg_\eta Y/L^{B+4}$ alternative prime $\ell'$ within $Y/L^B$, with $P-a\ell'$ squarefree, odd composite, negative half-divisor sum $\sum_{d\mid P-a\ell',\ d<\sqrt{P-a\ell'}}\mu(d)$, and all factors between $P^{\epsilon(\eta)}$ and $\sqrt{P-a\ell'}$;
* on the **same $\ell$**, at least $.01\mathfrak S(P)|I|/(L\log A)$ distinct alternative long cofactors $a'\in I\ni a$ for which $P-a'\ell$ has Möbius sign $+1$. In fact the linear half-divisor score $\sum_{d\mid m,\ d<\sqrt m}\mu(d)(1-2\log d/\log m)$ is exactly $2\log h/\log m>2\kappa$ on these semiprimes $m=h p'$.

This does not place an even and an odd partner on **the same long cofactor**. It does not assert that the long cofactors in either population are independently prime, or resolve binary Goldbach. There is no lower bound here for the unrestricted difference of the two signed populations.

## 1. The arbitrary selected-cell inequality

Let $\mathcal E$ be **any union** of cells $(\ell,I)$, and put $U=\sum_{(\ell,I)\in\mathcal E}|I|$, $R=\mathfrak S(P)U/(L\log A)$. In the following proof choose the tag family $\mathcal H=\{1\}$ or all the auxiliary primes $h$ above. For either choice count true rows in the selected cells with $a$ a long cofactor and $P-\ell a=h p$ with $p$ prime. Denote the count by $N_{\mathcal H}(\mathcal E)$. We prove, **uniformly in the selection**, that for each $E>0$
$$
   N_{\mathcal H}(\mathcal E)\ \ge\ .018 R-O_{B,E}(P L^{-E}).                         \tag{1}
$$
To derive the theorem from this, take $\mathcal E$ to consist of all cells whose count for the given family is less than $.01\mathfrak S(P)|I|/(L\log A)$. Then $.008 R\ll P L^{-E}$. Since $|I|\asymp A/L^B$, $\mathfrak S(P)\gg1$, there are $O_{B,D}(Y/L^D)$ such cells for arbitrary $D$. Take the union over the two tests and discard their short primes. These discarded primes support at most $O_{B,D}(P/L^D)$ prime witnesses by the trivial $O(A)$ possible cofactors apiece. The full witness family has size $\gg\mathfrak S(P)P/L^3$ by the tagged Chen theorem; intersect with its $1-\eta/2$ same-long assertion for the corner.

Use the Chen inequality $T_0-T_1/2-T_2/2$ of the tagged proof, now with each row labelled by $h$ and with $p=(P-\ell a)/h$ prime. Here $z=A^{.1}$, $y=A^{1/3}$, $T_0$ requires $P^-(a)>z$, $T_1$ counts each prime $r\mid a$, $z<r<y$, and $T_2$ counts the exceptional $a=rst$, $z<r<y\le s\le t$. As before any squarefree rank $\ge3$ has at least two small marks or this exceptional triple with precisely one mark. A repeated-prime rough row costs a power saving: each physical $P-\ell a$ has at most $1/\kappa$ possible polynomially large $h$'s even if primality is dropped; the number of squareful rough $a$ is $O(A/z+\sqrt A)$. In a true $h p$ row $p\gg P^{1-2\kappa}$, so $h$ is actually *unique* and $h\ne p$.

## 2. Direct sieve with the labelled true prime

Put $\sigma_h=\log h/L$, also $\sigma_1=0$. For the cell $(\ell,I)$ the source prime has range $(P-\ell I)/h$ and residue $P h^{-1}\bmod \ell$, with the usual interpretation $h=1$. The principal mass is
$$
 X_{\ell,I,h}=\frac1{\ell-1}\int_{(P-\ell I)/h}\frac{dt}{\log t}
 =(1+o(1))\frac{|I|}{h(1-\sigma_h)L}.
$$
The error is relative and uniform in the cells and the tags. For a sifted divisor $d$, the actual modulus for $p$ is $\ell d$ (or $\ell r d$ after marking $r$), residue $P h^{-1}$. At the direct stage omit primes dividing $P\ell h$ from the sifting set. Since $h\mid P-\ell a$, $h\nmid P$, $h\ne\ell$, we *already* have $h\nmid a$; this is not an independence assumption. If a prime dividing $P$ divided $a$, it would divide the complementary prime $p$, which is bigger than $a$. A failure $\ell\mid a$ when $\ell$ is omitted costs $O(P^{1-.04+o(1)})$ over all selected cells, again using bounded physical tag multiplicity. These statements cover also the singly marked upper sieve; the mark $r>z$ is larger than $h$ and $\ell$.

Use the same $\theta=.479$ and levels $A^\theta$, $A^\theta/r$ as in the tagged proof. The maximal physical modulus is $\ll P^{.49984}$. For every $h\le P^{.00004}$ this is below $(P/h)^{1/2}$ by a fixed power. Apply prime Bombieri–Vinogradov with maximal interval endpoints and maximal reduced residue at scale $P/h$, **for each $h$ separately**. On summing the resulting $O_E((P/h)L^{-E})$, the reciprocal mass of the tag family is bounded. For each $I$ and $h$ the mask on $\ell$ is arbitrary and bounded, and the choice of the polynomially large marked divisor(s) of each original modulus has bounded multiplicity. Summing $O(L^B)$ interval choices costs only logs.

The linear sieve has local density $1/(q-1)$ at primes outside $P\ell h$, zero otherwise. Its Mertens product is uniformly $(1+o(1))\mathfrak S(P)e^{-\gamma}/\log z$, since the extra tags change the product by $1+O(P^{-\kappa})$ and the omitted target primes $>z$ cost $O(L/z)$. The dimension-one inequalities have uniform $o(1)$ *relative to the selected principal mass*. Let
$$
 H=\sum_{h\in\mathcal H}\frac1{h(1-\sigma_h)}.
$$
The normalized direct difference $T_0-T_1/2$ is bounded below by
$$
 RH\left(10 e^{-\gamma} f(10\theta)-5e^{-\gamma}
     \int_{.1}^{1/3} F(10(\theta-t))\frac{dt}{t}-o(1)\right)-O_{B,E}(PL^{-E}).
$$
The correction to $F$ above argument 3 is included. The model for direct rows depends on $I,\ell,h$ only through the displayed mass and negligible relative Euler factors.

## 3. A sieve with an arbitrary masked short-prime slot

In the exceptional triple write $n=\ell r s t$. Before reverse sifting we require $n\equiv P\bmod h$; now a sifting divisor $d$ of $(P-n)/h$ gives **modulus $hd$**, not just $d$, in the physical source. Use $D'=P^{.499}$, $z'=P^{.249}$, omitting primes dividing $Ph$. Thus $hd\le P^{.49904}$. For a given physical modulus there are at most $1/\kappa$ ways to choose a tag $h>1$; the prime $h$ is polynomially large, not a sum over an uncontrolled weight multiplicity.

For each fixed $I$ partition each of the four prime slots into disjoint intervals of relative width $\le L^{-J_0}$ with $J_0>B+5$. Keep full boxes touching the restrictions $z<r<y\le s\le t$, $rst\in I$, and retain the exact initial mask $1_{(\ell,I)\in\mathcal E}$ on the prime $\ell$. This majorizes the original count because the upper-sieve divisor sum is nonnegative. There are only a fixed power of $L$ many boxes. The full boxes enlarge $rst\in I$ by $O(A L^{-J_0})=o(|I|)$, and enlarge factor boundaries only by a relative $1+O(L^{-J_0})$. Prime-slot representations in the enlarged measure are counted with the indicated roles $(r,s,t)$; no presumed cancellation of boundary points or factor of two is needed.

Here is the required distribution estimate, which allows an *arbitrary* masked short slot. Group $b=\ell r s$; its coefficient $u_b$ is bounded by a fixed divisor function (indeed by $3!$). The last coefficient is $v_t=1_{t\text{ prime in its box}}$. In particular $v$ is Siegel–Walfisz; $u$ need **not** be. The two lengths $M,N$ have $MN\asymp P$, $M,N\in[P^{.2},P^{.8}]$ for large $P$. The sum of absolute reduced-class discrepancies of $u*v$ for $q\le P^{.49904}$ is $O_E(PL^{-E})$. We recall the proof to expose the induced characters. By orthogonality the main is $\varphi(q)^{-1}\sum_{(n,q)=1}(u*v)(n)$. Write each nonprincipal character as a primitive one modulo $r>1$ lifted to $q=kr$, inserting $1_{(b,k)=1}$ and $1_{(t,k)=1}$ in both sums. For $r\le L^C$ the prime SW bound for differences of prefixes gives $O_E(N L^{-E})$ uniformly with the extra coprimality mask (at most $O(L)$ prime divisors are removed). Sum these conductors trivially with $1/\varphi(kr)\ll L/(kr)$, increasing the arbitrary SW exponent after choosing $C$. For $r\asymp R>L^C$ apply Cauchy and the [multiplicative large sieve](https://personal.science.psu.edu/rcv4/571s25/Class571-05.pdf) at fixed $k$. The $(k,R)$ block is
$$
 \ll \frac{L^{O(1)}}{kR}\sqrt{(M+R^2)(N+R^2)MN}
 \ll \frac{L^{O(1)}}k\left(P/R+P^{.91}+\sqrt P R\right).
$$
The last term saves a power as $R\ll P^{.49904}$; the first saves any desired logs on increasing $C$. Sum $1/k$ and dyadic blocks. No pointwise large-modulus PNT, SW on the masked slot, or paired prime independence enters. Uniform bounds in all fine boxes absorb their polylogarithmic number.

After distribution, reverse the reduced averages: the contribution per physical source and $h$ has factor $1_{(n,h)=1}/\varphi(h)$ (interpreted as $1$ when $h=1$), and the upper sieve sees probabilities $1/(q-1)$ outside $nPh$. Since all four source primes are polynomially large and $h$ is either 1 or polynomially large, the uniform principal upper is
$$
 \frac{1+o(1)}{\varphi(h)} \frac{2\mathfrak S(P)}{.499 L}.
$$
This uses $F(.499/.249)=2e^\gamma/(.499/.249)$ and weights independent of the source $n$. Target primes were omitted all along; possible nonunits $n$ in the upper majorant cannot increase the displayed bound. Physical $h$-multiplicity and the principal $1/\varphi(h)$ are thus accounted for at different stages.

For each selected $(\ell,I)$ the number of enlarged source tuples is at most $(I_*+o(1))|I|/\log A$, uniformly, with
$$
 I_*=\int_{.1}^{1/3}\frac{\log(2-3u)}{u(1-u)}\,du .
$$
Indeed sum over marked $r,s$ first; $s\le(1+o(1))\sqrt{\sup I/r}$ and the interval for the prime $t$ is the enlarged $I/(rs)$. Dropping $t\ge s$ when bounding the length gives the same upper integral over $.1\le u\le1/3$, $1/3\le v\le(1-u)/2$ with measure $du\,dv/[uv(1-u-v)]$, also on same-bin near-diagonals. The prime PNT with arbitrary log error on polynomially large endpoints gives the relative main on these log-fine ratio intervals; prime Mertens yields uniform $o(1)$ in the compact exponent region. The bounding product has remained within $1+o(1)$ of the true physical scale, uniformly in the interval. Consequently
$$
 T_2/2\le R\,(I_*/.499+o(1))\sum_{h\in\mathcal H}\frac1{\varphi(h)}
        +O_{B,E}(PL^{-E}).
$$
Since $\sum_h1/\varphi(h)\le(1+o(1))H$, the difference with the direct main, divided by $RH$, is at least the [previous certified lower constant](https://github.com/mxym/math/commit/5267e5b7) $4196921349/125000000000>.0335$, minus $o(1)$. For $h=1$ one has $H=1$; for the prime-tag band, $H\ge\log 2-o(1)>.69-o(1)$ by prime Mertens (the target primes remove $O(L/P^\kappa)$). Thus $.018$ is safe in both tests, proving (1). All additive errors can be made $O_{B,E}(PL^{-E})$ independently of the choice of cells; the sieve, geometric enlargement and Euler $o(1)$ multiply $R$, not full-rectangle volume.
