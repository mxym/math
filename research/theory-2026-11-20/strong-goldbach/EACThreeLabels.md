# Three-label closed factorization components: two free labels confined to 53

**All-height result.** In Bożek's Goldbach factorization graph at any even integer N there is no exceptional autonomous component with exactly three prime labels whose two smaller labels are both at most 53. Its third (largest) prime is **not bounded in the statement**. The proof is effective: it reduces an initially unbounded exponential system to 210 explicit pairs, 29,400 modular witnesses and 157,290 terminal cells. No factoring oracle or probabilistic primality call is needed.

**Unbounded-label companion.** More generally let the labels of any such three-vertex component be p,q,r with r the largest, and L=log N. For all sufficiently large N,
$$
 (\log p)(\log q)\gg \sqrt L/\log L.
$$
If the power f below is at least two, the right side may be replaced by $L/\log L$. The constants are absolute. For instance, with the smallest label fixed, its middle label in a three-vertex component must grow at least like $\exp(c\sqrt{\log N}/\log\log N)$, with c depending on that smallest label. This estimate by itself provides no all-height cutoff for the finite-alphabet result.

### 1. The three equations

Orient the edges from a prime x to every prime factor of N−x. An exceptional autonomous component, abbreviated EAC, is a nontrivial, non-Goldbach terminal SCC for this orientation: see [Bożek, §§2–3](https://arxiv.org/abs/1909.09900v1), whose edges point in the reverse direction. Its labels are odd, coprime to N, and all their complements are composite. In particular a label cannot divide its own complement. The prime r must occur in some other row by strong connectivity and cannot occur in both, since it would divide the nonzero difference p−q of absolute value <r. Exchange the names of the two smaller labels as needed. The row not using r has only the other small prime available, so the full equations become
$$
 N=p+q^d,\qquad N-q=p^e r^f,\qquad N-r=p^b q^c.                    \tag{1}
$$
Here d≥2, f≥1, e,b,c≥0, e+f≥2, b+c≥2 and c<d because r>p. All five exponents are <L since every base is at least 3. Every label is ≤(N−3)/3 since it divides an odd composite complement. In particular $q^d=N-p>N/2$.

We use the positive rational multiplicative form of [Matveev's theorem](https://doi.org/10.1070/IM2000v064n06ABEH000314), [explicit rational statement, Theorem 2.1](https://doi.org/10.1007/s12188-025-00293-9). For positive rationals $a_i$ and nonzero integer exponents with $B\ge\max(2,|b_i|)$, a product $\prod a_i^{b_i}\ne1$ satisfies
$$
 -\log\left|\prod a_i^{b_i}-1\right|
 <1.4\,30^{t+3}t^{4.5}(1+\log B)\prod_i\max(1,h(a_i)),
$$
where h is log max of coprime numerator and denominator. Omit a zero exponent or base 1. No linear independence of the remaining logarithms is required.

For the first use, $(r-p)/q^d=1-p^b q^{c-d}>0$. With $\lambda=1+\log(2L)$ and $A=(\log p)(\log q)$, this gives
$$
 r>\tfrac12 N\exp(-C A\lambda).                                       \tag{2}
$$
If f≥2 then $r^2<N$ and $L\ll A\lambda$. Otherwise f=1 and e≥1. Hence $e\log p\le\log(N/r)\ll A\lambda$. Eliminating r yields
$$
 (p^e-1)q^d+A_e=p^{e+b}q^c,\qquad A_e=p(p^e-1)+q>0.                   \tag{3}
$$
The associated nonzero three-base product minus one equals
$$
 p^{e+b}q^{c-d}/(p^e-1)-1=\frac{p+q/(p^e-1)}{q^d}.                    \tag{4}
$$
If $\max(p,q)>\sqrt N$, then $A\ge(\log 3)L/2$ already. Otherwise (4) is at most $4/\sqrt N$, while Matveev gives its negative log $\ll A\lambda\max(1,e\log p)\ll A^2\lambda^2$. This proves the unbounded-label companion.

### 2. Explicit archimedean reduction for the 210 ordered pairs

Now $3\le p,q\le53$, $p\ne q$. In (2) one can replace $CA$ by $10^{18}$ (the displayed t≤2 constant times $4^2$ is much smaller). For f≥2 this gives $L<2\log2+2\cdot10^{18}\lambda$. For f=1, $e\log p<2\cdot10^{18}\lambda$ and (4) is ≤160/N because $p+q/(p^e-1)<80$. The t≤3 constant times $4^2$ is < $10^{19}$. Its remaining height is bounded by $\max(1,e\log p)$; the exponent $e+b<2L$. Thus in either case $L<10^{38}\lambda^2$ (enlarging to this deliberately loose constant poses no loss). This implies $L<D=10^{50}$: the function $z/(1+\log(2z))^2$ increases for $z\ge D$ and exceeds $10^{38}$ at D (use $\log 10<3$). In particular $b,d<D$.

The first checker constructs an exact rational enclosure $[l,u]$ for $\theta=\log p/\log q$ and a coprime $A_0/H$ with
$$
 D<H\le10^{65},\qquad 2D\max(|Hl-A_0|,|Hu-A_0|)<1.                   \tag{5}
$$
It separately checks (5) for all 210 ordered pairs. For $1\le b<D$, $A_0b-H(d-c)$ is a nonzero integer, so $|b\theta-(d-c)|>1/(2H)$. For b=0 the left side is ≥1. Since $\log q>1$ and $p^bq^{c-d}<1$, the inequality $1-e^{-x}\ge\min(1/2,x/2)$ for $x\ge0$ gives $r>N/(8\cdot10^{65})$. The log enclosure uses $\log z=2\sum_{j\ge0}y^{2j+1}/(2j+1)$, $y=(z-1)/(z+1)$, on $1\le z\le2$, including the log 2 needed to rescale each integer. The geometric tail after 160 terms is at most $2y^{321}/(321(1-y^2))$. The continued fraction routine is only a witness finder; (5) is independently a sufficient rational inequality.

If f≥2, then $N<(8\cdot10^{65})^2<3^{500}$, so $d<500$. If f=1 then $3^e\le p^e<N/r<8\cdot10^{65}<3^{140}$, so it is safe to check every $1\le e\le140$.

### 3. Independently verified modular obstructions

If $e+b\ge200$, (3) modulo $p^{200}$ requires
$$
 q^d\equiv\tau=-p-q(p^e-1)^{-1}\pmod {p^{200}}.                       \tag{6}
$$
For every one of the 210·140 triples $(p,q,e)$ the modular checker exhibits a smaller modulus $h=p^a$ ($a\le114$) certifying (6) has no solution with $0\le d\le D$. Put $o=\mathrm{ord}_h(q)$; the verifier obtains o by removing prime factors from $p^{a-1}(p-1)$, then tests $q^o=1$ and $q^{o/\ell}\ne1$ for each $\ell\mid o$ prime. Each certificate is either
- $\tau^o\not\equiv1\pmod h$, inconsistent with any power of q (1,958 cases); or
- an integer $D<d_0<o$ with $q^{d_0}\equiv\tau\pmod h$, so all candidate exponents are $d_0\pmod o$ (27,442 cases).

The checker generates these witnesses by lifting a discrete log one digit at a time, starting from $\tau\equiv q\pmod p$. Its logically separate verifier uses only the indicated modular-power tests, not the generator's lift rules. Each of the 29,400 required keys is checked in order. Therefore $e+b<200$. Also (3) and $c<d$ imply $q^c\mid A_e$. In turn $q^d<p^{200} A_e/(p^e-1)<80\cdot53^{200}<3^{750}$; in both f cases $2\le d\le750$ suffices.

### 4. Exact terminal scan

For every $N=p+q^d$ in the 210·749 cells, strip **all** p factors from N−q, leaving $h$. The stripped exponent must be e, since $r\ne p$. For f=1 test r=h if e>0. For f≥2 use GMP's exact [perfect-power predicate and integer root extraction](https://gmplib.org/manual/Integer-Roots), checking *every* exponent from 2 to the bit length of h when h>1 is a perfect power. These cover every $h=r^f$ with $r\ge2$. Even a composite candidate r is allowed through the screen. Require $r>\max(p,q)$, composite-length index conditions in (1), and that stripping p,q from N−r leaves 1. For an SCC, r must be able to reach p, requiring $b>0$ or both $c>0$ and $e>0$. No candidate remains. All arithmetic is integer, with no upper cutoff imposed on the original N.

### Replay and scope

    python3 -O check_eac3_cf.py
    python3 -O check_eac3_lifts.py --write /tmp/eac3_modcert.tsv
    python3 -O check_eac3_lifts.py --verify /tmp/eac3_modcert.tsv
    c++ -O2 eac3_finite.cpp -lgmpxx -lgmp -o /tmp/eac3_finite
    /tmp/eac3_finite

Reference counters: 210 rational enclosures; 29,400 modular rejections and maximum a=114, canonical generated TSV SHA256 `40bafe8cb5fb8f33c6b8e4c621e9a8756241160c3b5c252e0b99d64540a7ee14`; terminal cells 157290, direct cases 30551, perfect powers 12, exact proper roots 12, survivors 0. The large TSV need not be redistributed: it can be regenerated by the second command and independently checked by the third. The result does not rule out three labels when the middle prime exceeds 53, larger components, or a hypothetical Goldbach exception. Bożek's previously known two-label result is not part of this three-label classification.

The finite-component claim concerns a stress-tested necessary structure for a Goldbach exception. It is unrelated to the analytic counts of exceptional targets in [Althöfer–Chen–Perelli–Pintz, November 2026](https://arxiv.org/abs/2611.09386v1), and no claim is made that larger components satisfy these three-vertex equations.
