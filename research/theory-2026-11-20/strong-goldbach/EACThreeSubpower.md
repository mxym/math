# Every unbounded sequence of three-label components has a subpolynomial smallest prime

**Theorem.** For every fixed $\epsilon>0$, only finitely many even centers N have a three-label exceptional autonomous component (EAC) all of whose primes are $\ge N^\epsilon$. Equivalently, along any sequence of distinct such centers tending to infinity, $\log(\min C)/\log N\to0$. In the exact prime-factor normal form below **each fixed exponent signature has only finitely many centers**. This theorem is qualitative; it supplies no computed cutoff or uniform bound as the exponents grow. In particular it neither excludes all three-label components nor solves binary Goldbach.

We finish the [primitive integral-curve theorem](EACThreePrimeCurves.md). In a three-label EAC put
$$
 N=p+q^d,\quad N-q=p^e r^f,\quad N-r=p^b q^c,\qquad r>p,q.
$$
Its elementary derivation and $b\ge1$, $0\le c<d$, $b+c\ne d$, $d\ge2$, $e+f,b+c\ge2$ are in the linked proof. If all labels are $\ge N^\epsilon$, the exponents are bounded; assume infinitely many centers with one fixed signature. All labels tend to infinity. Conversely for a fixed signature, $q^d\ge 2N/3$ and $p^b=(N-r)/q^c\gg N^{1-c/d}$ automatically force polynomial growth of both p,q. The linked theorem excludes $f\ge2$ without assuming any general irreducibility. It suffices to take $f=1$, $e\ge1$. We give the full remaining proof for every $d\ge2$.

Let $P,Q$ denote coordinate functions for p,q, and set $R=P+Q^d-P^bQ^c$. Choose an irreducible curve component carrying infinitely many points of the positive prime sequence. As explained in the linked proof, this is geometrically irreducible over $\mathbb Q$; its primitive integral defining factor $H(X,Y)$ divides
$$
 G(X,Y)=(X^e-1)(Y^d+X)-X^{e+b}Y^c+Y.
$$
The component does not contain the origin by the primitive-point lemma. By [Alvanos–Bilu–Poulakis, Theorem 1.2, base $\mathbb Q$ and integer coordinates](https://arxiv.org/pdf/0907.2097), its normalization has genus zero and either one infinity place or two conjugate nonrational infinity places. In the notation of the linked proof the pole-height inequality is $h(P)+h(Q)+h(R)\ge h(N)$. It applies to *any* remaining component; the argument below identifies which infinity place the positive points actually approach. No irreducibility of the full polynomial G is required.

## 1. The physical infinity place is rational and therefore unique

Write $g=\gcd(d-c,b)$, $m=(d-c)/g$, $n=b/g$ so $\gcd(m,n)=1$. Since $r=(N-q)/p^e=o(N)$ and $p=o(N)$ (all labels are factors of composites with cofactor at least the growing smallest prime), $p^b/q^{d-c}=(N-r)/(N-p)\to1$. Introduce $X=t^{-m},Y=t^{-n}Z$. Multiplying G by $t^{em+dn}$ gives
$$
 (1-t^{em})Z^d-Z^c+t^{em+(d-1)n}Z+t^{dn-m}(1-t^{em})=0.             \tag{1}
$$
Here $dn>m$ since $db>d-c$ for $b+c\ge2$. At $t=0,Z=1$ the derivative in Z is $d-c\ne0$. Thus there is a unique convergent analytic power series $Z(t)$ near zero with $Z(0)=1$, and every coefficient is rational by the recursive implicit-function equations. On the positive integer sequence $t=p^{-1/m}\to0$ and $q t^n\to1$; by local uniqueness it lies on precisely this germ. Indeed evaluating any factor vanishing on infinitely many of these points gives a Laurent series with accumulating zeros and hence identically zero. The substitution into $\mathbb Q((t))$ therefore embeds the function field of this very component (the kernel in $\mathbb Q[X,Y]$ is a height-one prime since X is transcendental and (1) holds). The restricted t-adic place has residue field $\mathbb Q$ and value group $\mathbb Z$ since the orders of X,Y are $-m,-n$ with coprime m,n. It is a rational infinity place, ruling out the two-conjugate possibility. Hence it is the **only** infinity place. In particular $h(P)=m$, $h(Q)=n$.

It follows that Q is integral over $\mathbb Q[P]$ and P over $\mathbb Q[Q]$: both have poles only at this same place; over every finite value of P all places have Q regular, and conversely. Equivalently, the integral closures of the two polynomial rings in the curve's function field are the regular functions away from the single infinity pole. Thus the leading coefficients of primitive H in each variable are constants: the monic minimal polynomials over the corresponding rational function fields have polynomial coefficients, and primitivity clears no variable factor. Moreover the constant leading Y coefficient of $H\in\mathbb Z[X,Y]$ is $\pm1$ by Gauss's lemma since it divides $\operatorname{lc}_Y(G)=X^e-1$. The constant leading X coefficient likewise divides the primitive polynomial $-Y^c$ when $b\ge2$, or $1-Y^c$ when $b=1$ (then $c\ge1$), and is therefore $\pm1$. The degree–pole divisor formula gives
$$ \deg_Y H=[\mathbb Q(P,Q):\mathbb Q(P)]=m,\qquad \deg_X H=n. $$
For any use of an integral monic graph $Q=A(P)$ below, $m=1$ makes $A\in\mathbb Z[X]$ by that $\pm1$ leading Y coefficient; its leading term is $X^n$ from the positive germ. None of these conclusions requires the full affine curve to be nonsingular.

## 2. No such infinite component when $c\ge1$

Since $H(0,0)\ne0$ and
$$                         G(X,0)=X(X^e-1), $$
the polynomial $H(X,0)$ divides $X^e-1$ over $\mathbb Q[X]$, up to a nonzero scalar. Specialization preserves its X-degree because its leading X coefficient is constant; hence $n\le e$. Also $h(N)=e m+h(R)$ from the second row with $f=1$, the orders being compared on the positive physical branch as in the companion. The pole-height inequality $m+n+h(R)\ge h(N)$ now gives
$$                         (e-1)m\le n\le e.                            \tag{2}
$$

For $e\ge2$ this forces $m=1$: if $m\ge2$ then $e\le2$, and $e=m=n=2$ conflicts with coprimality. Thus $q=A(p)$ as above, and $n=e$ or $n=e-1$. If $n=1$ too then $b=d-c$, already impossible. So $n\ge2$. Since $m=1$, $b=n(d-c)$. At every prime point $q^{d-c}>p^b$, hence $q>p^n$. For $n=e$, the equality $H=\pm(Y-A(X))$ and the divisibility $A(X)\mid X^e-1$ force $A=X^e-1$, contradicting that strict inequality. For $n=e-1$, as $q\sim p^n$,
$$
 0<q-p^n\le \frac{q^{d-c}-p^{n(d-c)}}{p^{n(d-c-1)}}
   =\frac{r-p}{q^c p^{n(d-c-1)}}
   \ll\frac q{p^e}=o(1).
$$
Here $r=(N-q)/p^e\ll q^d/p^e$ and $q/p^n\to1$; the difference-of-powers inequality includes $d-c=1$. This is impossible for integers.

If $e=1$, (2) gives n=1; then $d-c=mb$. Put $z=q^m-p$, a positive even integer because $q^{d-c}>p^b$ and the primes are odd. As $q^m/p\to1$ and $r=(p+q^d-q)/p$,
$$
 2\le z\le \frac{q^{mb}-p^b}{q^{m(b-1)}}
        =\frac{r-p}{q^{d-m}}
        \le (1+o(1))\frac{q^m}{p}=1+o(1).
$$
This eliminates $e=1$ as well.

## 3. No such infinite component when $c=0$

In this case $G(1,Y)=Y-1$. Since $H$ is monic up to sign in Y, its specialization at X=1 retains degree m and divides this nonzero linear polynomial. Thus $m=1$ and $b=dn$. Again $q=A(p)$ for a monic integer polynomial A of degree n. We have $n\ge2$ since $b\ne d$. Also $h(R)=dn-e\ge n$ from $r>q$ on the physical branch, so $e\le b-n\le b-2$.

As a polynomial identity on the component,
$$
 A(X)^d=\frac{X^{e+b}-A(X)-X(X^e-1)}{X^e-1}.
$$
After factoring $X^{e+b}$ in the numerator, its two lower terms have relative sizes $O(X^{n-e-b})$ and $O(X^{1-b})$, both $o(X^{-e})$ because $n<b$, $e\le b-2$. Thus at positive infinity
$$
 A(X)=X^n\left(1+\frac1d X^{-e}+o(X^{-e})\right).
$$
If $e\le n$, the first lower coefficient of this integer polynomial would be $1/d\notin\mathbb Z$. If $e>n$, the difference from $X^n$ tends to zero and $A=X^n$ identically, contradicting both $q^d>p^b$ and primality for n≥2. This disposes of the last case.

Together with the repeated-largest branch, this proves the theorem. The argument uses the genuine coprimality and integrality of prime labels, positivity to select the rational branch, and finiteness (not an explicit height bound) from Siegel. No passage to variable exponents without the polynomial-size hypothesis is made.
