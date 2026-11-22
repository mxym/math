# A signed giant-factor cross term against genuine balanced semiprimes

Let \(N\) be a prescribed sufficiently large even integer, \(L=\log N\), and
\(I=N I_0\) for a fixed nondegenerate interval \(I_0\subset[1/3,2/3]\).
Write
\[
 \mathfrak S(N)=2\prod_{p>2}\left(1-\frac{1}{(p-1)^2}\right)
        \prod_{\substack{p\mid N\\p>2}}\frac{p-1}{p-2}
\]
for the ordered Goldbach singular series. All displayed finite decimals
are exact rational exponents. Define the actual prime-product source
\(B_N(y)=\log q\log r/L\) if
\[
 y=qr\in I,\qquad q,r\text{ prime},\qquad
 N^{.5058}\le r\le N^{.5062},\qquad (y,N)=1,
\]
and \(B_N(y)=0\) otherwise. The indicated orientation is unique:
\(q\) has exponent in \([.4938,.4942]+O(1/L)\).
Put \(T_N=\sum_y B_N(y)\).

Fix any nonincreasing \(g\in C^\infty([0,\infty))\) with \(g=1\)
on \([0,.5025]\) and \(g=0\) on \([.5045,\infty)\). Set
\[
 S_g(m)=\sum_{d\mid m}\mu(d)g(\log d/L),\qquad
 \kappa_g=\int_{.5025}^{.5045}\frac{-g'(t)}{t}\,dt
           \in(1/.5045,1/.5025).
\]
All scores use the displayed common denominator \(L\), not an
own-log normalization.

**Theorem.** Uniformly in the prescribed even \(N\),
\(T_N=(.0004+o(1))|I|\) and
\[
 \sum_{\substack{y:\ B_N(y)>0\\
 m=N-y\ {\rm composite},\ P^+(m)>\sqrt N}} B_N(y)L S_g(m)
 =-\kappa_g T_N\mathfrak S(N)+o(N\mathfrak S(N)).                      \tag{1}
\]
The same asymptotic holds with the strict condition \(P^+(m)>\sqrt m\).
In either convention let \(C_{\rm ng}\) be the actual signed
\(B_N(y)L S_g(N-y)\) sum over the complementary **composite** part,
and let \(G_B=L\sum_{N-y\ {\rm prime}}B_N(y)\). Then
\[
             G_B+C_{\rm ng}
      =\kappa_g T_N\mathfrak S(N)+o(N\mathfrak S(N)).                  \tag{2}
\]
No sign or upper bound for \(C_{\rm ng}\) at the margin of (2) is
asserted. The quantity \(G_B\) concerns a prime plus the specified
semiprime, not a pair of primes.

**Rough-partner corollary.** For either \(\alpha=1/4\) or
\(\alpha=.2525\), put \(s=.5054/\alpha\). The original weighted sum
of \(L B_N(y)\) over squarefree partners \(m=N-y\) whose prime
factors are all at least \(N^\alpha\) is at least
\[
      \left(\frac{2\log(s-1)}{\alpha s}-o(1)\right)
                  T_N\mathfrak S(N).                                \tag{3}
\]
In particular there are \(\gg N\mathfrak S(N)/L^2\) such distinct
actual \(y\) and the partners have at most three prime factors.
For \(\alpha=.2525\) every such squarefree rank-three partner is
nongiant even at its own strict square root, and has \(S_g(m)=-2\).
The lower bound does not separate this rank from ranks one and two.

## 1. Absolute progression estimate for the actual source

For every fixed \(A>0\),
\[
 \sum_{\substack{b\le N^{.5055}\\(b,N)=1}}\sup_{J\subset I}
 \left|
  \sum_{\substack{y\in J\\y\equiv N\ (b)}}B_N(y)
   -\frac1{\varphi(b)}\sum_{\substack{y\in J\\(b,y)=1}}B_N(y)
 \right|\ll_{A,I_0} N L^{-A}.                                        \tag{4}
\]
Here \(J\) is any interval (fixed half-open endpoint convention).
This is product distribution on two actual prime variables, not
Bombieri–Vinogradov for the opposing prime indicator.

First take \(J\) fixed. Split \(q,r\) into log-fine boxes of ratio
\(1+L^{-B}\), where \(B\) may be chosen arbitrarily large. Embed the
two intervals in \([M,2M],[T,2T]\) with their own lower endpoints.
Then \(X=MT\asymp_{I_0}N\); the exponent of \(T\) lies in
\([.5058,.5062]+O(1/L)\) and that of \(M\) in
\([.4938,.4942]+O(1/L)\). Keep \((y,N)=1\) by excluding the prime
divisors of \(N\) separately in each slot. The two sequence weights
\(\log p/L\) are bounded by one; restoring a factor \(L\) is harmless.
The longer prime sequence satisfies the Siegel–Walfisz condition
of [Fouvry–Radziwiłł, *Another application of Linnik's dispersion
method*, Definition 1 and Theorem 1.1](https://arxiv.org/abs/1812.00562v2).
For small log-power moduli this follows by prime Siegel–Walfisz at
the two endpoints and partial summation. An auxiliary coprimality
mask excludes at most the number of prime divisors of the auxiliary
integer, within its allowed divisor bound. Excluding prime factors
of \(N\) costs \(O(L)\). For larger moduli use the integer progression
bound \(O(T/b+1)\) and the trivial principal \(O(T/\varphi(b))\),
taking the splitting log power large enough.

There are only a fixed power of \(L\) boxes. Boundary boxes for
the product interval \(J\) have their ambiguous products within
\(O(NL^{-B})\) of an endpoint. In the summed actual progression
counts a source row in these strips is counted at most
\(\tau(N-y)\) times. Cauchy–Schwarz, the ordinary second divisor
moment bound, and \(B_N(y)\ll L\) give \(O(NL^{-B/2+O(1)})\).
The summed principal error costs only
\(\sum_{b\le N}1/\varphi(b)\ll L\) times the strip mass.
This justifies discarding the boundary boxes. No PNT in short
intervals of the mesh size is used.

For the high moduli use Fouvry–Radziwiłł's Theorem 1.1 from
\(Q=N^{.49355}\) to \(Q=N^{.5055}\). Its lower rail is
\(Q\ge T^{56/23}X^{-17/23+\eta}\) and the upper rail is
\(Q\le T X^{-\eta}\). At the worst source exponent the lower
exponent before \(\eta\) is
\((56\cdot .5062-17)/23=.4933565217\ldots<.49355\);
the upper margin is at least \(.5058-.5055=.0003\).
These strict margins absorb fixed factors in the box endpoints
and the small proof parameters. Its bound is already absolute in
the moduli, so restriction to the prescribed subsets costs nothing.

A fixed-factor residue extension is needed: the literal statement
prints \(1\le |a|\le X=MT\), whereas \(a=N\). Its proof extends to
\(1\le |a|\le C X\) for fixed \(C\), as follows. In §§3.1 and 4.1,
the divisor bounds for \(|mn-a|\) and the removal of \(n\mid a\)
use only \(|mn-a|\ll_C X\) and the ordinary polynomial-range divisor
bound. Reduced-class zero-frequency estimates require only
\((a,b)=1\). In §3.2, after additive reciprocity, the smooth
phase's logarithmic derivative is bounded by a constant times
\(|a|H/(TQ)\), where \(H\ll X^\eta Q/M\) as in (14);
this stays \(O_C(X^\eta)\). The incomplete Kloosterman gcd estimates
there use \(\tau(ah)\ll_{\eta,C} X^\eta\); no small residue
representative is required. In §4.4, after
\(q=(\nu_1-\nu_2)/r\), the analogous smooth phase has the same
size ratio, and the Bettin–Chandee prefactor is controlled by
\(|a|RH/T^2\ll_C X^\eta\), with \(R\ll T/Q\) as in (35).
These are the size uses for \(a\) in the nonzero terms leading to
(42)–(44). Thus replacing \(X\) by the fixed allowance \(CX\) in
the bound on \(|a|\) leaves the rails unchanged. Here \(C\) can
be fixed in terms of \(I_0\). No more recent dispersion preprint is
used.

For the low moduli \(b\le N^{.49355}\) both true prime slots
exceed \(b\). A character induced from conductor \(k\mid b\)
therefore agrees with its primitive ancestor at every source
variable. The principal character is already subtracted.
With \(A(\chi),D(\chi)\) denoting the short and long normalized
prime sums on the box, induction bounds the total nonprincipal
part by
\[
 \ll L\sum_{1<k\le N^{.49355}}\frac1{\varphi(k)}
                   \sum_{\chi\bmod k}^{*}|A(\chi)D(\chi)|.
\]
Indeed \(\sum_{b:\,k\mid b}1/\varphi(b)\ll L/\varphi(k)\)
in the given range by
\(\varphi(ks)\ge\varphi(k)\varphi(s)\). For \(k\le L^{C_1}\)
use prime Siegel–Walfisz to arbitrary log accuracy. On each
remaining dyadic conductor scale \(K\), Cauchy and the
multiplicative large sieve give, apart from fixed log powers,
\[
 \frac{\sqrt{MT}}K\sqrt{(M+K^2)(T+K^2)}
 \ll \frac XK+\sqrt{MX}+\sqrt{TX}+K\sqrt X .
\]
The first term saves arbitrary logarithms for sufficiently large
\(C_1\), and the other terms save a fixed power. This proves the
summed estimate at fixed endpoints. For the supremum in (4), use
an additive mesh of step \(NL^{-C_2}\). The uniform trivial
boundary cost per modulus is
\(O(L(NL^{-C_2}/b+1)+NL^{1-C_2}/\varphi(b))\).
Its sum is arbitrarily log-small with large \(C_2\). Sum the
fixed-endpoint estimates over the mesh with larger original
log accuracy. The result also permits any fixed divisor-power
multiplicity in \(b\): apply Cauchy with (4), the individual
\(O(NL^2/b)\) estimate, and fixed divisor moments.

Finally the ordinary PNT on \(I/r\), at a polynomial scale with
fixed endpoint ratio, gives
\(\sum_{q\in I/r,\ q\ {\rm prime}}\log q=(|I|/r)(1+o(1))\)
uniformly in the indicated \(r\). The outer reciprocal-log sum
over \(r\) is \((.0004+o(1))L\). Removing target-prime factors
in either slot costs \(N^{.5062+o(1)}\) in \(T_N\).
This proves its stated asymptotic.

## 2. Uniform signed harmonic calculation

For even \(N\) write
\[
 \sum_{(d,N)=1}\frac{\mu(d)d^{-s}}{\varphi(d)}
        =\frac{H_N(s)}{\zeta(1+s)}.
\]
The Euler factor of \(H_N\) is \((1-p^{-1-s})^{-1}\) at \(p\mid N\),
and \((1-p^{-s}/(p-1))/(1-p^{-1-s})\) otherwise. In particular
\(H_N(0)=\mathfrak S(N)\). If \(h_N(a)\) are its Dirichlet
coefficients, the factors at \(p\nmid N\) have absolute Euler norm
\(1+O(p^{-2})\) and first absolute log moment \(O(\log p/p^2)\).
The nonnegative factors at \(p\mid N\) therefore give
\[
 \sum_a|h_N(a)|\ll \mathfrak S(N),\qquad
 \sum_a|h_N(a)|\log a\ll \mathfrak S(N)(1+\log\log N).
\]
For the second bound, split
\(\sum_{p\mid N}\log p/(p-1)\) at \(p=L\); use the prime reciprocal-log
bound below \(L\) and \(\sum_{p\mid N}\log p\le L\) above it.

Let \(M_1(u)=\sum_{n\le e^u}\mu(n)/n\). The classical zero-free
region gives finite absolute log moments of every fixed order
for this function; see e.g. [Lee–Leong](https://arxiv.org/abs/2208.06141)
and partial summation. Its integral on \([0,\infty)\) equals 1:
for \(s>0\) its Laplace integral is \(1/[s\zeta(1+s)]\), and
integrability permits \(s\downarrow0\). Integration by parts
against \(g(t+u/L)\) gives uniformly for \(t\ge0\)
\[
 \sum_n\frac{\mu(n)}n g(t+\log n/L)=-g'(t)/L+O_g(L^{-2}).
\]
Convolving this with \(h_N\) and using the first log moment yields
\[
 \sum_{(d,N)=1}\frac{\mu(d)}{\varphi(d)}g(t+\log d/L)
 =-\frac{\mathfrak S(N)}L g'(t)
   +O_g\!\left(\frac{\mathfrak S(N)(1+\log\log N)}{L^2}\right).       \tag{5}
\]

## 3. Whole-score evaluation and complete giant summand

Expand \(S_g(m)\) on the complete source and apply (4) at
\(d\le N^{.5045}\). For each literal source row \(y=qr\) the
absolute harmonic error from replacing the reduced source mass
by the full one is negligible: the total \(1/\varphi(d)\) over
\(d\) divisible by either source prime is \(O(L/q+L/r)\), using
the same totient multiplicity bound as in §1. Also \((y,N)=1\)
implies \((m,N)=1\). Then (5) with \(t=0\) and \(g'(0)=0\) gives
\[
                 \sum_y B_N(y)L S_g(N-y)=o(N\mathfrak S(N)).        \tag{6}
\]

On the literal giant composite branch write \(m=pv\), with
\(p>\sqrt N\) prime. This factor is unique, \(p\nmid v\), and
\(1<v<\sqrt N\). All divisors of \(v\) lie on the flat part of \(g\).
The finite Möbius sum on \(v>1\) is zero, so
\[
                    S_g(pv)=-\sum_{d\mid v}\mu(d)g(\log(pd)/L).
\]
There is no squarefreeness restriction on \(v\). Only \(p<N^{.5045}\)
contributes. The moduli \(pd\le N^{.5045}\) have \(d\le N^{.0045}\)
and \(p\nmid d\); neither genuine source prime divides \(pd\)
by the respective exponent ranges. Conversely a contributing
modulus \(pd\mid m\) has \(m/p>1\) automatically because \(m\asymp N\).
Thus the giant contribution equals
\[
 -L T_N\sum_{\substack{\sqrt N<p<N^{.5045}\\p\nmid N}}\frac1{p-1}
       \sum_{(d,N)=1}\frac{\mu(d)}{\varphi(d)}
                     g(\log p/L+\log d/L)+O_{A,g}(N L^{-A}).       \tag{7}
\]
This uses (4) on the original residue and the unique giant factor
in every contributing modulus. Substituting (5) and using prime
Mertens gives
\(\sum_p g'(\log p/L)/(p-1)
=\int_{.5025}^{.5045}g'(t)\,dt/t+o(1)\).
Omitted primes dividing \(N\) cost a power, and the harmonic sum
against the uniform error in (5) is bounded. This proves (1).

For the strict own-root cutoff, the extra possible giant primes
lie in \([\sqrt{N/3},\sqrt N]\) and satisfy \(p>\sqrt m\);
they remain unique, with \(p\nmid v\) and all divisors of \(v\)
on the flat part. For fixed extra \(p\), restrict the source
interval to \(y>N-p^2\) inside \(I\). The maximal estimate (4)
permits precisely this moving interval. The same expansion as
(7) has its actual restricted mass, at most \(T_N\), in place
of \(T_N\). Since \(g'(\log p/L)=0\) on this extra band, (5) bounds
its **signed** contribution by \(o(N\mathfrak S(N))\).
This does not identify the two unsigned branch counts; equality
\(p=\sqrt m\) is not included by the strict cutoff. Prime rows
have \(S_g(m)=1\) exactly. Subtracting (1) from (6) proves (2).

## 4. True rough partners

Apply the classical dimension-one lower linear sieve to the
nonnegative source \(B_N(y)\) with partner \(m=N-y\), at level
\(N^{.5054}\) and threshold \(N^\alpha\). Its density is
\(1/(p-1)\) at \(p\nmid N\), zero at \(p\mid N\), with remainder
(4) and the power-small replacement by the full mass from §3.
Omitting target primes only decreases the upper dimension
product. The Mertens factor is
\[
 V_N(N^\alpha)=(1+o(1))e^{-\gamma}\mathfrak S(N)/(\alpha L);
\]
after division by the usual Mertens product the local factors
are \(1-1/(p-1)^2\) at \(p\nmid N\) and \((1-1/p)^{-1}\) at
\(p\mid N\); the target-prime tail is \(O(L/N^\alpha)\).
For both specified exponents \(2<s<3\), so the exact lower
linear-sieve function is \(f(s)=2e^\gamma\log(s-1)/s>0\).
See the classical [Iwaniec linear sieve](https://doi.org/10.4064/aa-36-2-155-172).
Multiplying by \(L\) gives (3) before the squarefree restriction.
Discarding \(p^2\mid m\) with \(p\ge N^\alpha\) costs
\(O(L^2(N^{1-\alpha}+\sqrt N))=o(N\mathfrak S(N))\).
Since \(m<N\) and \(4\alpha\ge1\), at most three factors remain.
For \(\alpha=.2525\) and rank three, every pair has log exponent
at least \(.505\), above the cutoff, and the largest factor is
at most \(N^{.495}<\sqrt m\) for large \(N\); all individual
factors lie on the plateau. Thus \(S_g(m)=1-3=-2\) exactly.
Lastly \(L B_N(y)\le L^2\), proving the claimed unweighted count.

Fouvry–Radziwiłł apply their dispersion estimate to a Titchmarsh-type
divisor problem on a multiplicative convolution. Here the output
is an exact signed reflected composite score against two specified
genuine prime slots, including a complete giant summand and the
same normalization of its ungated counterpart. The lower-sieve
corollary uses their established dispersion input, not a replacement
for Chen's prime-source theorem. For a different recent prime-source
approach, compare [Lichtman's Goldbach application](https://arxiv.org/abs/2309.08522).
No priority claim or conclusion about binary Goldbach is made.
