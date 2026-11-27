# A localized lower bound for sets without an equal-LCM triple

Let \(F(N)\) be the largest cardinality of a set \(A\subseteq[1,N]\cap\mathbb Z\) containing no distinct \(a,b,c\) for which
\(\operatorname{lcm}(a,b)=\operatorname{lcm}(a,c)=\operatorname{lcm}(b,c)\).
Define
\[
\beta=1-\frac{1+\log\log 3}{\log 3}=0.00415475149\ldots .
\]

**Theorem.** For each fixed \(0<\epsilon<19/40\), uniformly for
\[
N^{21/40+\epsilon}\le H\le N/2,
\]
there is such a set contained entirely in \((N-H,N]\), of size at least
\[
\frac{H}{(\log N)^{\beta+o(1)}}. \tag{1}
\]
In particular \(F(N)\ge N/(\log N)^{\beta+o(1)}\). The lower bound uses an existing divisor-spacing theorem of Stef and a transfer to one short interval; the exponent \(\beta\) is Stef's, not a new exponent for his divisor-spacing problem. This does not determine \(F(N)\) or decide whether \(F(N)=o(N)\).

## The analytic input

Let \(E\) be the positive integers \(m\) such that no two distinct divisors of \(m\) have ratio strictly between \(1\) and \(2\) (larger over smaller); include \(1\). Stef's 1992 lower bound for the exceptional set for close divisors is
\[
E(Y):=\#(E\cap[1,Y])\ \ge\ \frac{Y}{(\log Y)^{\beta+o(1)}}. \tag{2}
\]
This is stated in [Stef and Tenenbaum, *Entiers lexicographiques*, equations (1.5)–(1.6), printed p. 170](https://tenenb.perso.math.cnrs.fr/PPP/NbsLexicographiques.pdf), and [Tenenbaum's survey, equation (8)](https://tenenb.perso.math.cnrs.fr/PPP/Erdos-100.pdf). A version with a strictly larger minimal ratio also implies (2) for our convention. Partial summation gives
\[
\sum_{\substack{m\le Y\\m\in E}}\frac1m
=\frac{E(Y)}Y+\int_1^Y \frac{E(v)}{v^2}\,dv
\ \ge\ (\log Y)^{1-\beta-o(1)}. \tag{3}
\]
Indeed, for every fixed \(\delta>0\) the integrand is bounded below, for large \(v\), by a constant times \(1/(v(\log v)^{\beta+\delta})\); integrate just from \(\sqrt Y\) to \(Y\).

The other input is the short-interval prime lower bound of [Baker, Harman and Pintz, *The difference between consecutive primes, II*, final display on p. 562](https://www.cs.umd.edu/~gasarch/BLOGPAPERS/BakerHarmanPintz.pdf): with \(\theta=21/40\) there are \(\gg x^\theta/\log x\) primes in \((x,x+x^\theta]\) for all sufficiently large \(x\). We use its elementary consequence that an interval \((X-\Delta,X]\), \(X/2\le X-\Delta\) and \(\Delta\ge 2X^\theta\), contains \(\gg\Delta/\log X\) primes. To see this, start at the left endpoint and take adjoining intervals of the form \((x,x+x^\theta]\) while they fit. The discarded remainder has length at most \(X^\theta\), so the total length of the fitted pieces is at least \(\Delta/2\).

## Moving the exceptional set to a specified top interval

Multiplication by a prime \(p>2m\) preserves \(m\in E\). Indeed \(p\nmid m\), and the divisors of \(mp\) form two disjoint copies of the divisor list of \(m\), one scaled by \(p\). In each copy the ratios are unchanged, and any member of the second copy divided by any member of the first is at least \(p/m>2\).

Fix \(0<\eta<\min(1/3,\epsilon/(2(1-\theta)))\), depending only on \(\epsilon\). For every \(m\in E\) with \(m\le N^\eta\), take all primes
\[
\frac{N-H}{m}<p\le\frac Nm .
\]
These satisfy \(p>N/(2m)>2m\) for large \(N\), and their interval length satisfies, uniformly over \(m,H\),
\[
\frac{H/m}{(N/m)^\theta}
=\frac{H}{N^\theta m^{1-\theta}}
\ \ge\ N^{\epsilon-\eta(1-\theta)}
\ \ge\ N^{\epsilon/2}.
\]
Hence there are \(\gg H/(m\log N)\) choices. All products \(mp\) lie in \(E\cap(N-H,N]\); different choices give different products, because \(p\) is the unique largest prime factor of \(mp\) and then \(m\) is determined. By (3),
\[
\#\big(E\cap(N-H,N]\big)
\ \gg\ \frac H{\log N}\sum_{\substack{m\le N^\eta\\m\in E}}\frac1m
\ \ge\ \frac{H}{(\log N)^{\beta+o(1)}}. \tag{4}
\]
The large-prime step is what localizes the global bound (2): it does not require Stef's exceptional integers themselves to have been distributed evenly among the short intervals of interest.

## Equal-LCM triples force a close divisor pair

Suppose that distinct \(a,b,c\) in \((N-H,N]\) all have the same pairwise least common multiple \(M\). Set \(x=M/a,\ y=M/b,\ z=M/c\). Then
\[
\gcd(x,y)=M/\operatorname{lcm}(a,b)=1,
\quad
\gcd(x,z)=1.
\]
Because \(y,z\mid M\) and they are each coprime to \(x\), both divide \(a=M/x\). They are distinct and their ratio (larger over smaller) is the corresponding ratio between \(b,c\), in increasing order. This ratio is strictly less than two since \(b,c\) are in \((N/2,N]\). Therefore \(a\notin E\). In fact the same argument excludes the other two vertices from \(E\) as well. Thus \(A=E\cap(N-H,N]\) is a permissible choice in (1), by (4).

## Context and checks

[Abbott and Gardner (1967), display (11)](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/AE504749C4EC2CAAA0AD6561BCA7E22A/S0008439500067138a.pdf/div-class-title-an-extremal-problem-in-number-theory-div.pdf) give the classical \(N\log\log N/\log N\) construction using products of two primes. The [discussion of problem 536](https://www.erdosproblems.com/forum/thread/536?order=oldest) records a \(1-1/e\) exponent from rainbow prime-factor selection and announces a \(0.059\ldots\) exponent. The bound here follows by transferring the stronger already-known exceptional-set bound (2), with explicit short-interval localization. It neither claims priority for (2) nor depends on any proposed upper bound for the LCM problem.

The [companion exact checks](verify_erdos536_localized_divisor_spacing.js) test the complement-divisor reduction and the preservation and uniqueness of the large-prime transfer on finite inputs. The asymptotic count follows from the cited analytic inputs and the proof above, not from the tests.
