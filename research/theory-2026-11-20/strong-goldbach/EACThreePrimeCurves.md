# Primitive integral curves and repeated powers in three-label components

Take the exact normal form for a three-label exceptional autonomous component (EAC) at an even center N:
$$ N=p+q^d,\qquad N-q=p^e r^f,\qquad N-r=p^b q^c,\qquad r>p,q.       \tag{1} $$
Here $p,q,r$ are distinct odd primes; global hypotheses are those of [Bożek](https://arxiv.org/abs/1909.09900v1). **For each fixed $\epsilon>0$, only finitely many centers admit such a component with $\min(p,q,r)\ge N^\epsilon$ and either $f\ge2$ or $d=2$.** Thus, for polynomial-sized labels at sufficiently large height, the largest prime occurs only to the first power and the forced pure prime power has exponent at least three. This leaves the unrestricted $d\ge3,f=1$ regime and all cases with a subpolynomially small label. The proof gives no numerical center bound.

Equation (1) is not a special adjacency assumption: no prime divides its own row, r must occur by strong connectivity, and r cannot divide both smaller rows as their positive difference is <r. Name the small row not containing it p; that row can only be a power of q. Compositeness gives $d\ge2$, $e+f,b+c\ge2$, $f\ge1$. Each label is a factor of an odd composite <N, hence ≤$(N-3)/3$. Since $r>p$, $N-r<q^d$ forces $c<d$. In fact $b\ge1$: otherwise two distinct powers of q lie in $[2N/3,N]$. From $r-p=q^c(q^{d-c}-p^b)>0$ the positive difference in parentheses is even, so $r>2q^c$. Combined with $r^f<N<2q^d$, this gives $cf<d$.

Also **$b+c\ne d$ at every height**. Otherwise $q^c(q^b-p^b)>0$ forces $q>p$, and $r-p\ge(q-p)q^{d-1}$. But $pr\le p^e r^f=N-q<q^d$ (if e=0 then $f\ge2$), whereas $p(q-p)>q$ for odd primes $q\ge p+2$. This is impossible.

## 1. Primitive integral points, without an irreducibility assumption

If the minimum label is ≥$N^\epsilon$, all the exponents are at most $1/\epsilon$. An infinite sequence therefore admits an infinite subsequence with one fixed exponent pattern and all primes tending to infinity. Eliminate r using the last row; the plane polynomial is
$$ F(X,Y)=X^e(X+Y^d-X^bY^c)^f-Y^d-X+Y. $$
It is nonzero, and at $(0,0)$ its Y partial derivative equals 1 since the powered or multiplied term has no linear contribution under the stated exponents. Choose an irreducible component containing infinitely many of these prime points. It is defined over the rationals and geometrically irreducible: two distinct conjugate components can only share finitely many points, so a component with infinitely many rational points is fixed by Galois. Write $P,Q,R=P+Q^d-P^bQ^c$ for its coordinate functions; the chosen values of each tend to infinity, so none is constant.

**Lemma about the origin.** If this component contains $(0,0)$, its primitive integer points $(p,q)$ with positive distinct unbounded prime coordinates are finite. This is not an assertion that all of F is irreducible. On the component the origin is nonsingular and rational. Work on its smooth projective normalization, and use the affine normalization over the ordinary finite coordinate chart. By Siegel an infinite set of integer points requires genus zero and at most two geometric places at infinity; see the precise integral criterion of [Alvanos–Bilu–Poulakis, Theorem 1.2](https://arxiv.org/pdf/0907.2097).

If there are two places at infinity, remove also the one point O over the origin. The primitive integer points away from singularities are S-integral on this thrice-punctured curve for a *fixed* finite set S of bad places. Indeed for any regular function u on the punctured curve there is an m such that $P^m u,Q^m u$ are regular on the affine normalization (clear the pole at O). These functions are integral over $\mathbb Q[P,Q]$. Clearing constants in their monic integral equations makes their values integral away from fixed bad primes on every nonsingular integer point. At any good prime at least one of p,q is a unit since $\gcd(p,q)=1$, so u is integral there. Choose finitely many affine generators to fix S once. Siegel on the open smooth curve now gives finiteness. This step uses coprimality, not just that the real points are far from the origin.

If there is exactly one infinity place it is rational. Genus zero and the rational O give a parameter $t$ over $\mathbb Q$ with zero at O and only pole at infinity. Then $P(t),Q(t)$ are rational-coefficient polynomials, both divisible by t. If $t=a/b$ in lowest terms gives integer p,q, b divides the fixed leading coefficient of a cleared integer polynomial for $P(t)-p$ by the rational root theorem. After clearing a common coefficient denominator M, $a\mid M p$ and $a\mid M q$ by divisibility by t (and $\gcd(a,b)=1$). Thus $|a|\le M$ and only finitely many parameters occur. This proves the lemma; the finitely many singular points cause no issue.

## 2. A degree constraint on *every other* possible infinite component

Suppose the chosen component misses the origin. On it P and Q have no common finite zero; indeed such a zero would lie over $(0,0)$. By the integral-curve criterion just cited, the normalized component has genus zero and either one infinity place or two places conjugate over $\mathbb Q$ (two distinct rational infinity places cannot give infinitely many **integer** points over $\mathbb Q$). Write h(A) for the degree of the pole divisor of a rational function A on the normalization over $\overline{\mathbb Q}$. All of $P,Q,R,$ and $N=P+Q^d$ have poles at infinity, at each place with the same order if there are two since the functions are rational over $\mathbb Q$. Along an unbounded positive prime subsequence, pass to a fixed limiting infinity point. Orders, or equivalently leading Laurent terms there, determine the log-growth ratios; moreover $2N/3\le N-\text{label}<N$. Thus with $n=h(N)$ and $x=h(P)/n$, $y=h(Q)/n$, $z=h(R)/n$ one has
$$ dy=ex+fz=bx+cy=1,\qquad 0<x,y\le z.                               \tag{2} $$
This argument does not compare algebraic leading terms before choosing the actual positive subsequence.

There is a further unconditional restriction
$$                              x+y+z\ge1.                              \tag{3} $$
Indeed $E=Q^{d-c}-P^b=(R-P)/Q^c$ is regular at finite places, and at infinity the order bound on $R-P$ gives $h(E)\le h(R)-c h(Q)$. If the right side were negative, E would be a nonzero function regular everywhere vanishing at infinity, impossible. The finite zeros of P,Q,E are pairwise disjoint. The rational function $u=Q^{d-c}/P^b$ has degree $D=(d-c)h(Q)=b h(P)$, with no zeros/poles at infinity since the individual pole orders agree there by (2). It is nonconstant: on an infinite prime subsequence the constant $p^b/q^{d-c}$ would be in lowest terms with unbounded numerator and denominator, impossible for a fixed number. The preimages of $0,\infty,1$ among finite points lie among zeros of Q,P,E, respectively. On a genus-zero curve, Riemann–Hurwitz bounds their total number of distinct preimages including infinity by **at least** $D+2$: the total ramification is $2D-2$ whereas these three fibers have total multiplicity $3D$. Consequently
$$
 D+2\le h(Q)+h(P)+h(E)+2
 \le h(Q)+h(P)+h(R)-c h(Q)+2.
$$
Substitute $D=(d-c)h(Q)$ and $d h(Q)=n$ to obtain (3). This is the function-field abc step, proved here by ramification; it is not the integer abc conjecture.

## 3. All repeated-largest-factor signatures

If $f\ge3$, (2) gives $z\le1/3$; (3) and $x,y\le z$ force $x=y=z=1/3$, hence $d=b+c=3$, already excluded arithmetically. If $f=2$ and $e\ge1$, then $x+y+z\le x+2z\le ex+2z=1$. Equality throughout gives $e=1$, $y=z=1/d$ and $x=(d-2)/d\le1/d$. Thus d=3 and again $b+c=d$. Only $f=2,e=0$ remains. Here $N-q=r^2$. Even d is impossible since $r^2-(q^{d/2})^2=p-q$ is nonzero of absolute value <r, whereas the gap of the two distinct squares is >r. Similarly $b,c$ cannot both be even: $r^2-p^b q^c=r-q$ has magnitude <r. As $cf<d$, the choice $b=1$ would give $x=(d-c)/d>1/2=z$, impossible. Now (3) becomes
$$                         (b-2)(d-2)\le4-2c.                          \tag{4} $$
If $c\ge1$, $r\equiv p\pmod q$ and $r^2\equiv p\pmod q$, so $p\equiv1\pmod q$. This implies $x\ge y$, i.e. $b\le d-c$ in (2). When $b\ge3$, (4) forces $c=1$ and $d\le4$, whence $d=3$ by oddness, incompatible with $3\le b\le d-1$. When $b=2$, (4) forces $c\le2$; c=2 was excluded by parity of both exponents. For c=1 subtracting the two rows gives $r(r-1)=q(p^2-1)$, so the largest odd prime r must divide $p-1$ or $p+1$, impossible. This excludes all $c\ge1$.

For c=0, b,d are odd, ≥3, distinct, and satisfy $(b-2)(d-2)\le4$. They can only be 3 and 5, in either order. In each of these two actual residual cases F is monic in Y and irreducible over $\mathbb Q[X,Y]$: a nontrivial factorization would specialize into two positive-Y-degree monic factors, whereas the following degree-preserving finite-field specializations are irreducible.
- $(d,b)=(3,5)$: $X=2$ mod 3 gives $Y^6-Y^3+Y+1$.
- $(d,b)=(5,3)$: $X=6$ mod 11 gives $Y^{10}-3Y^5+Y-5$.

The origin is nonsingular rational, so this unique rational component is geometrically irreducible (otherwise every conjugate factor would contain the same rational origin, making it singular). The origin lemma closes both cases. Run `python3 -O check_eac3_fcurve.py` to recompute both specializations and the standard finite-field Rabin criterion via exact modular powers and polynomial gcds. No other multivariate irreducibility assumption or catalogue is used.

## 4. The entire quadratic pure-row branch

The case d=2 also admits a separate proof uniform in the *choice* of fixed e,b. If e=0 then $f\ge2$ and $r^f-q^2=p-q<r-q<r^2-q^2$, impossible. Thus $e\ge1$, and $p\mid q(q-1)$ forces $p<q$. Hence $p^e r^f=q^2+p-q<q^2$; since $r>q$, this forces $f=1$ and $p^e<q$. If $c=1$, $r\equiv p\pmod q$ and $p^er\equiv p\pmod q$ imply $q\mid p^e-1$, impossible. Since c<d, only c=0 remains; $b\ge2$ and b=2 was already excluded by $b+c\ne d$. Eliminating r produces a quadratic in q,
$$
 (p^e-1)q^2+q=p^{e+b}-p(p^e-1).
$$
Its discriminant at p is a square, where
$$
 \Delta(X)=4X^{2e+b}-4X^{e+b}-4X^{2e+1}+8X^{e+1}-4X+1.
$$
For **odd b**, $\Delta$ has odd degree and $\Delta(0)=\Delta(1)=1$. If its squarefree kernel had degree one, the rational factorization would have form $(X-a)G(X)^2$ over $\mathbb Q$ (its leading coefficient 4 is a square). The rational root theorem gives $a\in\{\pm1,\pm1/2,\pm1/4\}$. Both $-a$ and $1-a$ must be nonzero rational squares from the evaluations, yet none of these a qualifies. Thus there are at least three geometric roots of odd multiplicity. The hyperelliptic double cover $Z^2=\Delta(X)$ has normalized genus ≥1, and Siegel gives finitely many integral pairs.

For **even b≥4**, if $e\ge2$ then
$$
 \Delta(1/2)=1-4(1-X^e)\big[X^{e+b}+X(1-X^e)\big]\big|_{X=1/2}<0
$$
since $2(1-2^{-e})^2>1$. So it is not a rational polynomial square. If e=1, $\Delta=4X^{b+2}-4X^{b+1}-4X^3+8X^2-4X+1$. An exact square polynomial with positive leading coefficient would start $G=2X^m-X^{m-1}+gX^{m-2}+\cdots$, $m=b/2+1$. Comparison at degree $b=2m-2>3$ forces $g=-1/4$, impossible: any square root in $\mathbb Q[X]$ of this primitive integer polynomial lies in $\mathbb Z[X]$ by Gauss's lemma. In both cases $\Delta$ is nonsquare of even degree with rational-square leading coefficient. The expansion at $+\infty$ has a rational polynomial part H with $\sqrt{\Delta(x)}=H(x)+O(1/x)$. On integer x, $H(x)$ has bounded denominator; if the square root is integral for arbitrarily large x, it must equal $H(x)$ exactly at those x. This would force $\Delta=H^2$, contradiction. Hence only finitely many x occur at each fixed e,b.

Finite exponent selection now proves the two assertions in the stated polynomial-size regime. This conclusion does not exclude an unbounded d=2 family whose smaller label falls below every fixed power of N, and (3) on its own does not eliminate the remaining $d\ge3,f=1$ patterns.
