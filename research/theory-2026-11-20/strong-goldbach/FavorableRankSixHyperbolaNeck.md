# Actual fixed-target divisor necks in favorable rank-six rows

Use the genuine reflected profiles \(T_{6,i}\), \(i=1,2,3\), in
[FullFavorableRankSixAbsorption.md](FullFavorableRankSixAbsorption.md).
Thus \(N=2x\), \(L=\log x\), \(n=sq\in(x/2,x]\), \(m=N-n=pG\)
with the actual primes
\[
 G=A_1A_2A_3D E,\qquad
 p\text{ at exponent } .4305-\eta,\qquad
 \log_xG=.5695+\eta+O(\rho),\quad \rho=\eta/10^5,
\]
and \(0<\eta<.002\). All five true labels in \(G\) and the true
\(s\) are independently restricted to their stated bands. We
keep \((n,N)=1\), \(s\) at one of the three prescribed short
bands, and the positive weight
\[
             {\cal W}(s,q)=W_s(q)(-C^\dagger(m))=O(L)
\]
on the physical rank-six input. Fix any \(0<\delta\le.01\).
In the opened row \(q\) is an integer; require
\(P^-(q)>x^\delta\) and \(q\) composite.

For an interval \(I\) of log sizes within \([0,1]\), restrict further
to \(q\) with at least one **proper** divisor \(r>1\) satisfying
\(\log_xr\in I\) and \(q/r>1\). Then uniformly in the actual even
\(N\) and the interval,
\[
 \sum_{\substack{\mathrm{this\ actual\ row}\\
   P^-(q)>x^\delta,\ q=r t,\ r,t>1,\ \log_xr\in I
   \text{ for some }r,t}}
 {\cal W}(s,q)
 \ \ll_{\eta,\delta}\ 
      (|I|+L^{-1})\,\mathfrak S(N)x/L .
 \tag{1}
\]
The proof uses a true modular hyperbola and a three-condition sieve
on the variables \(r,t,p\). It does not use distribution of primes
\(q\) in an artificial model, nor any unproved cancellation on the
rough complement. It bounds both orientations whenever their
specified divisor lies in \(I\).

## 1. Literal switching and the incomplete count

Fix the five primes of \(G\) and the actual \(s\).
On the unit support \((sG,N)=1\) and \((s,G)=1\):
a prime common to \(s\) and \(G\) divides both \(n\)
and \(m\), hence \(N\), which is excluded.
The real structural equation on a pair of boxes is
\[
          r t\equiv c=N\overline s\pmod G,\qquad
          p=(N-s r t)/G .
 \tag{2}
\]
The class \(c\) is a unit. Use dyadic intervals with
\(r\asymp R_1,\ t\asymp R_2,\ R_1 R_2\asymp x/s\).
Their lower length is at least \(x^\delta/2\) in a box meeting
the actual rough support. For an upper bound one can drop the
central product inequality inside each such box and use all of
the rectangle. Only an \(O(1)\) number of \(R_2\)-dyads are
needed for each \(R_1\)-dyad that meets the central condition.

For a squarefree auxiliary modulus \(d\) coprime to \(G\), and
prescribed residue pair \(r=a,t=b\bmod d\), let \(H_{a,b}(d)\)
count solutions of the first part of (2) in the rectangle.
Writing \(\ell_j\asymp R_j\) for the two interval lengths,
completion gives uniformly
\[
 H_{a,b}(d)=\frac{\phi(G)}{G^2}\frac{\ell_1\ell_2}{d^2}
   +O\!\left(L^C\left[
     \sqrt G+\frac{R_1+R_2}{dG}+1\right]\right).
 \tag{3}
\]
Here \(G\) is the product of five distinct actual primes.
To check (3), set \(\widehat I_j(h)\) to be the exponential sum
of the corresponding restricted interval on frequency \(h\bmod G\).
The exact expansion has coefficient \(1/G^2\), and complete
Kloosterman sum \(S(h,k c;G)\) on the two frequencies.
The \((0,0)\) term is \(\phi(G)/G^2\) times the product
of the actual progression lengths \(\ell_j/d+O(1)\).
At nonzero frequencies the geometric series bound, since
\((d,G)=1\), gives the useful restricted sum
\[
 \sum_{\substack{h\ne0\bmod G\\b_0\mid h}}
           |\widehat I_j(h)|\ll (G/b_0)\log(2G)
                 \qquad (b_0\mid G).
\]
Indeed multiplication by \(d\) permutes the nonzero multiples
of \(b_0\) modulo \(G\), where the closest distance to zero
is a multiple of \(b_0\). This estimate does not require
\(R_j<G\). With both frequencies nonzero, the classical
[complete Weil bound](https://users.renyi.hu/~gharcos/weil.pdf)
and CRT give \(|S(h,kc;G)|\ll\sqrt G (h,k,G)^{1/2}\);
the divisor factor is bounded because \(G\) has five primes.
Expand the gcd majorant over \(b_0\mid G\) and use the
restricted Fourier bound twice. The sum of \(b_0^{-3/2}\)
is bounded, giving \(O(\sqrt G\log^2(2G))\).
With one frequency zero use the Ramanujan bound
\(|S(h,0;G)|\le(h,G)\), expand over \(b_0\) again,
and multiply by \(\widehat I_j(0)=O(R_j/d+1)\).
This gives the two axial terms in (3), with the same
harmless interval endpoint errors. The estimate also covers
rectangles in which one variable is longer than \(G\).

## 2. Three forbidden conditions on the true fibre

Sieve the positive box sequence of all pairs satisfying the first
condition of (2), with the exact integer \(p\) given by (2).
Actual \(r,t\) on the selected rough support and actual prime \(p\)
are free of prime factors below a sufficiently small fixed power.
For every small sieve prime \(\ell\), both \(s\) and \(G\) are units
at \(\ell\), because all their true prime labels have fixed larger
exponents. Among \((r,t)\bmod\ell\) the prohibited set for at least
one of \(\ell\mid r,t,p\) has size
\[
 \omega(\ell)=
 \begin{cases}
  3\ell-2,&\ell\nmid N,\\
  2\ell-1,&\ell\mid N.
 \end{cases}
\]
The two coordinate axes have union size \(2\ell-1\). If
\(\ell\nmid N\), the additional condition \(s r t=N\bmod\ell\)
is disjoint from them and has \(\ell-1\) points; otherwise it is
exactly the axes. In particular 2 is admissible here since \(N\)
is even. For squarefree \(d\) the prohibited residue pairs
combine by CRT. Sum (3) over at most \(d^2\) pairs to get main
\(g(d)\phi(G)\ell_1\ell_2/G^2\), where \(g\) is multiplicative
with \(g(\ell)=\omega(\ell)/\ell^2\). The error is
\[
                 O\big(L^C(d^2\sqrt G+d(R_1+R_2)/G)\big).
 \tag{4}
\]
The displayed error absorbs \(d^2\) since \(G>1\).

Apply the Selberg upper bound (e.g.
[Tao's statement, Theorem 30](https://terrytao.wordpress.com/2015/01/21/254a-notes-4-some-sieve-theory/))
with support level \(D_0=x^\epsilon\), where
\(\epsilon<\min(.0005,\delta/10)\) is fixed, and include all sieve
primes up to \(x^{\epsilon/2}\).
The remainder terms up to \(D_0\) have only a factor
\(3^{\omega(d)}\) more than (4), so their sums have costs
\(D_0^{3+o(1)}\sqrt G\) and \(D_0^{2+o(1)}(R_1+R_2)/G\).
The logarithmic sieve main has the uniform upper factor
\(O_\delta(\mathfrak S(N)/L^3)\).
Here is a direct way to see its exact singular comparison.
The Selberg denominator uses squarefree coefficients with
\(h(\ell)=g(\ell)/(1-g(\ell))\). Compare them to the fixed
\(h_*(\ell)=3/\ell\) for odd primes, and \(h_*(2)=1\).
Outside \(N\), \(h\ge h_*\); on \(\ell\mid N\) odd,
\(h\ge2/\ell\). Put
\(k(\ell)=(h_*(\ell)-h(\ell))_+\le1/\ell\) there, and zero
otherwise, extending all functions multiplicatively on squarefree
integers. Then \(h_*\le h*k\) on squarefree integers. The denominator
\(\sum_{d\le D_0^{1/2}}h(d)\) is at least
\(\gg(\log D_0)^3/\prod_{\ell\mid N}(1+k(\ell))
  \gg(\log D_0)^3/\mathfrak S(N)\).
In the first bound the fixed comparison sum of \(h_*\) has order
\((\log D_0)^3\) by its Euler product
\(\zeta(1+z)^3\) times an absolutely convergent product near zero,
or the elementary convolution with \(\tau_3(n)/n\).
All divisor prime factors in this denominator are in the chosen
sieve range, and the prime factors of \(Gs\) have been excluded
by size, not by an artificial degeneracy.

The margins in (4) are polynomial on the actual boxes.
Since \(\log_xs\le .139+\rho\) and
\(\log_xG=.5695+\eta+O(\rho)\),
\[
 \frac{R_1R_2}{G}\ \gg\ x^{.2915-\eta-O(\rho)},\qquad
 \sqrt G\ \ll\ x^{.28475+\eta/2+O(\rho)} .
\]
Their exponent difference exceeds .0037 throughout the stated
range. The extra \(D_0^3\) in the first error uses less than .0015.
Also
\((R_1+R_2)/(R_1R_2)\ll x^{-\delta}\), absorbing \(D_0^2\)
in the axes. Thus the error is power-small relative to
\(R_1 R_2/G\) for every outer \(s,G\), before dividing by log powers,
uniformly in the true residue (2).
We obtain the actual count bound
\[
                 \ll_{\eta,\delta}
               \frac{\mathfrak S(N)}{L^3}\frac{R_1R_2}{G}.
 \tag{5}
\]
This is an upper sieve on the true integer \(p\) derived in (2).
It does not assume independent primality of \(r,t,p\).
Dropping positivity of \(p\) in the ambient rectangle would
only enlarge the upper sieve sample; actual solutions
have \(p\asymp x^{.4305-\eta}\) up to the band.

## 3. Outer summation and use

There are \(O(1+|I|L)\) \(r\)-dyads meeting the requested
exponent interval; the number of corresponding \(t\)-dyads in
the central range is bounded. Majorize the desired count by
all pairs \(r,t\) in those boxes, even if a physical \(q\)
has multiple admissible splitting divisors. Such overcount
is allowed in this upper bound. Multiply (5) by the true
\(O(L)\) weight. Summing over independent actual primes of
\(G\) and over true \(s\) uses their bounded harmonic sums
\(\sum 1/(sG)\ll_\eta1\). Since \(R_1R_2\asymp x/s\), the
result is (1), with its endpoint \(L^{-1}\) cost.

For instance, for a polynomially rough (and squarefree)
even-rank \(q\), the exact half-centered identity (7) of
[BalancedSemiprimeEvenRankNeck.md](BalancedSemiprimeEvenRankNeck.md)
is supported on proper divisors in its near-half interval
\(U_q<d\le B_q\), provided \(V_q<P^-(q)\) and the other
stated cutoff conditions hold. There are only bounded many
prime labels on the polynomially rough support, so the
normalized centered coefficient is \(O_\delta(1)\).
Consequently (1) prices any such specified neck on this
genuine rank-six reflected profile at its actual logarithmic
width. The squareful portion with \(P^-(q)>x^\delta\) is
power-small by summing \(q\asymp x/s\) divisible by a prime
square with base \(>x^\delta\), then using divisor moments.
This is not a bound on the unrestricted outside-\(Q\)
divisor geometry, or a lower bound for true \(q\) primes.

**Dated comparison.** [Pham, October 30 v1](https://www.preprints.org/manuscript/202610.3061) proves a separate rough-pair benchmark. The estimate here conditions on the actual five-factor complementary modulus and uses a classical complete sum and Selberg upper sieve on the resulting modular hyperbola. It bounds a specified positive divisor window, not an arbitrary signed tail or a prime-pair lower bound.
