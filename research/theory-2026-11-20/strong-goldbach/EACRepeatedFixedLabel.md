# Repeated largest factor: no unbounded centers with a bounded prime label

Write an actual three-label exceptional autonomous component in [Bożek's graph](https://arxiv.org/abs/1909.09900v1) as
$$N=p+q^d=q+p^e r^f=r+p^b q^c,\quad r>p,q.$$
The labels are distinct odd primes. The elementary derivation and inequalities $b\ge1$, $d\ge2$, $0\le c<d$, $cf<d$, $r>2q^c$, $r\le(N-3)/3$, $e+f,b+c\ge2$ are in [EACThreePrimeCurves.md](EACThreePrimeCurves.md). Here assume $f\ge2$.

**Theorem.** With absolute implied constant, $d\ll\log p$ and $\log N\ll(\log p)(\log q)$. For each fixed real $H$, only finitely many centers in this branch have $\min(p,q,r)\le H$. This does not give a list of the centers, an effective global bound, or exclude the case where all three labels grow.

### Two logarithms with normalized exponents

Put $D=d-c$, $L=\log N$. There is a nonzero archimedean form with genuinely small value:
$$0<\Lambda=D\log q-b\log p=\log\left(1+\frac{r-p}{N-r}\right)\ll N^{-1/2},$$
because $r^2\le p^e r^f<N$ and $N-r\ge2N/3$. We use [Laurent–Mignotte–Nesterenko, J. Number Theory 55 (1995), 285–321](https://doi.org/10.1006/jnth.1995.1141), Corollaire 2 (p. 288); a rational-number statement is also given in [Evertse, Exercise 5.1](https://pub.math.leidenuniv.nl/~evertsejh/dio14-5.pdf). For distinct primes $p,q\ge3$, their two-real-logarithm estimate gives
$$-\log|\Lambda|\ll\log p\log q\left[1+\log^+\!\left(\frac b{\log q}+\frac D{\log p}\right)\right]^2.$$
The logarithms are multiplicatively independent in the sense that their two bases are multiplicatively independent. Both integer coefficients are nonzero. Importantly this uses normalized exponents, not a bound in terms of $\log(\max(b,D))$. As $p<r\le N/3$, we have $d\log q\le L\le d\log q+\log(3/2)$ and $b\log p\le L$. Dividing by $\log p\log q$ shows
$$x=d/\log p\ll (1+\log^+x)^2.$$
Thus $x$ is absolutely bounded, proving both estimates.

### Bounded p

If $p$ is fixed then $d$ is bounded, and $f$ is bounded because $q^f<r^f<N\le(3/2)q^d$. In fact $d\ge3$ in this branch: if $d=2,e=0$ then $r^2-q^2\le p-q<r-q$ is impossible; if $e\ge1$, reduction of $p^e r^f=q^2-q+p$ modulo $p$ gives $p\mid q-1$, so $p<q$ and $r^2\le p^e r^f<q^2$, also impossible. Fix $d,f$ and $a=e\bmod f$. Setting $y=p^{(e-a)/f}r$ produces integral points on
$$q^d-q+p=p^a y^f.$$
The polynomial $X^d-X+p$ is squarefree: a multiple root $z$ would satisfy $z^{d-1}=1/d$ and $z=dp/(d-1)>1$, incompatible. The normalized cover of the $X$-line is geometrically integral (Eisenstein in the $y$-variable at a simple root). Its projection has degree $f$ and is fully ramified at each of the $d$ simple roots. Riemann–Hurwitz gives $2g-2\ge d(f-1)-2f\ge-1$, hence $g\ge1$. By Siegel's integral-point theorem there are only finitely many such $q$ (see [Alvanos–Bilu–Poulakis, Thm. 1.2](https://arxiv.org/abs/0907.2097)). There are only finitely many fixed triples $d,f,a$ to consider.

### Bounded q

If $q$ is fixed, the two-logarithm result gives $p\gg N^{\delta}$ for a positive $\delta$ depending on $q$ (shrinking $\delta$ absorbs constants). Thus $b$ is bounded. We first show $pr/N\ll N^{-\eta}$ for some $\eta>0$ depending at most on $q$. If $e\ge1$, $pr/N<1/r\le1/p$. If $e=0$, $f\ge3$, then $pr/N<r^2/N<N^{-1/3}$. It remains to discuss $e=0,f=2$; we prove that $b\ge3$ in this case.

If $b=1$ then $c\ge1$ and $p<r$, $r>2q^c$ imply $N-r=pq^c<r^2/2=(N-q)/2$, impossible since $r\le N/3$. If $b=2$ then $d$ must be odd (the nonzero gap $|r^2-q^d|=|p-q|<r$ cannot be a gap between squares), and $c$ must be odd for the same reason applied to $r^2-p^2q^c=r-q$. Then $w=q^{(d-c)/2}>p$ and
$$r=p+q^c(w^2-p^2)>2q^cw=2q^{(d+c)/2},$$
since $w,p$ differ by at least 2. This gives $r^2>4q^{d+c}>N$, impossible. Thus $p<N^{1/3}$ and $r<\sqrt N$ in the only remaining case, as required.

Now fix one of the finitely many exponents $b$ and one residue $j=D\bmod b$. The positive real gap obeys
$$0<q^{D/b}-p=p\left[\left(1+\frac{r-p}{N-r}\right)^{1/b}-1\right]\ll pr/N\ll N^{-\eta}.$$
Put $s=(D-j)/b$; then $q^s\to\infty$ on an unbounded sequence, since $q^{D/b}>p\gg N^\delta$, and $q^s\le N$. If $j=0$ the strictly positive gap between two integers cannot tend to zero. Otherwise $\alpha=q^{j/b}$ is a fixed algebraic irrational, and $p/q^s$ is reduced since $p\ne q$. For sufficiently large centers,
$$0<|\alpha-p/q^s|\ll(q^s)^{-1}N^{-\eta}<(q^s)^{-1-\eta/2}.$$
By [Ridout's theorem, *Rational approximations to algebraic numbers* (1957)](https://doi.org/10.1112/S0025579300001182) only finitely many such approximations with prime-power denominators supported on the fixed prime $q$ exist. This proves finiteness for each bounded $q$, completing the theorem.
