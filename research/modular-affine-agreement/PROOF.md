# Weighted affine agreement under prime reduction

## 1. Definitions and the two signs

Fix an integer \(n\ge1\), write \(G_n=\{0,\ldots,n\}^2\), and let
\(\mu\) be a probability measure on \(G_n\). An affine line always means
a graph \(y=ax+b\), not a vertical line. For
\(K\in\{\mathbb Z_{\ge0},\mathbb Z,\mathbb Q\}\) put
\[
 A_K=\max_{a,b\in K}\ \mu\{(x,y):y=ax+b\},\qquad
 B_p=\max_{a,b\in\mathbb F_p}\ \mu\{(x,y):y\equiv ax+b\pmod p\}.
\]
The maxima exist: only finitely many subsets of \(G_n\) occur as
agreement sets. Let \(\mathcal P\) be a nonempty finite set of primes
and let \(p\) be uniform on it.

Given the source's nonempty \(S\subseteq\{0,\ldots,n\}\) and randomized
\(f:\{0,\ldots,n\}\to\{0,\ldots,n\}\), define
\(\mu(x,y)=|S|^{-1}\Pr[f(x)=y]\) for \(x\in S\) and zero otherwise.
The objective \(1-\alpha\) in Definition 5.36 is then \(A_{\mathbb N}\);
\(1-\widehat\alpha\) is \(\mathbb E_p B_p\). No independence between
the values of \(f\) at different \(x\)'s is needed: the expected
relative Hamming distance uses only these one-coordinate probabilities.
The maximum modulo \(p\) is taken separately for each prime; all
elements of \(\mathbb F_p\) arise as residues of natural numbers under
either convention for \(\mathbb N\).

A line of integral coefficients reduces to a field line at every
prime, so \(B_p\ge A_{\mathbb N}\). Consequently the *printed*
difference \(\widehat\alpha-\alpha=A_{\mathbb N}-\mathbb E_p B_p\)
is nonpositive for every input. The maximum in the definition is zero,
as witnessed by \(S=\{0\}\), \(f(0)=1\), with other values arbitrary.
The nonnegative direction instead considered by AICR c/0074 is
\(\mathbb E_p B_p-A_{\mathbb N}\).

For \(n=2\), take \(S=\{0,2\}\), \(f(0)=1\), \(f(2)=2\), and for
example \(f(1)=0\). The line through those two points has slope 1/2
and intercept 1. The integral score is exactly 1/2: both points
cannot be matched, and \(y=x+1\) matches the first. Over any odd prime
both match. Thus the reversed-direction gap equals 1/2 for every
bit length \(k\ge3\); the domain size \(n=2\) qualifies for every
positive exponential size exponent once \(k\) is large enough.
This refutes that direction with natural, or even arbitrary signed
integer, coefficients. It works whether or not 0 is natural. For the
signed convention and odd primes it is minimal in \(n\): in the
\(n=1\) box each field line hits at most one point per input, and
any such singleton or pair through the two inputs is contained in
an integral affine graph.

## 2. Sharp gaps in the stated large-prime regimes

**Nonnegative coefficients.** For a prime \(p>n\), a modular line hits
at most one integer \(y\in[0,n]\) at each integer \(x\). Each such
point has weight at most \(A_{\mathbb Z_{\ge0}}\), by the constant
line through it. Hence \(B_p\le(n+1)A_{\mathbb Z_{\ge0}}\), and
\[
 B_p-A_{\mathbb Z_{\ge0}} \le \frac{n}{n+1}B_p\le \frac{n}{n+1}.
\]
With uniform \(x\in\{0,\ldots,n\}\) and deterministic \(f(x)=n-x\),
every nonnegative-slope graph hits at most one point, and the descending
line fits all the points modulo every prime. It attains the displayed
bound simultaneously for every \(p>n\). Thus this is the exact maximum
of the average gap when all primes in \(\mathcal P\) exceed \(n\),
even under the source's restricted \(\mu\). If \(\mathbb N\) is instead
strictly positive and both coefficients are required to lie in it, the
maximum is 1 even without the large-prime condition: take \(f\equiv0\),
which no such integer line meets on nonnegative inputs, but whose
residues are matched by the field zero line.

**Signed coefficients.** Suppose \(p>n^2\). Three integer points of the
box whose reductions are on one field line have zero integer determinant.
Indeed, for three points ordered by \(x_1\le x_2\le x_3\), the determinant
\[
 D=(x_2-x_1)y_3+(x_3-x_2)y_1-(x_3-x_1)y_2
\]
has absolute value at most \(n(x_3-x_1)\le n^2\). If zero, any two of the
points of distinct \(x\) determine their nonvertical rational line. Since
here \(p>n\), the points on the field line have distinct integer \(x\)
except when the points are identical. In particular, when at least two
points have positive weight, all its positive-weight points lie on a
rational line. If the rational slope and intercept are integral, its
entire mass is at most \(A_{\mathbb Z}\). Otherwise the slope is
\(u/v\) with coprime integers \(u,v\), \(v\ge2\): an integer slope
through an integer point would give an integer intercept. All integer
points on the line have \(x\) in one residue class modulo \(v\).
Thus at most \(m=\lfloor n/2\rfloor+1\) points contribute, and each
weighs at most \(A_{\mathbb Z}\). The same bound holds with a singleton
or no point. It follows that
\[
 B_p-A_{\mathbb Z}\ \le\ (1-1/m)B_p\le 1-1/m.
\]
Equality for every \(p>n^2\) is attained with uniform even \(x\) in the
box and \(f(x)=x/2\) there. A signed integral line agrees with at most
one of these points when \(m>1\), while \(y=x/2\) is a valid field
line at the odd primes. If \(m=1\) the upper bound is zero, attained
by any singleton on an integral line. The result is therefore also
sharp after averaging over any nonempty set of primes exceeding
\(n^2\).

## 3. Positive result with rational comparison

Set \(a=A_{\mathbb Q}\), \(b_p=B_p\), and
\(\delta_p=(b_p-a)_+=\max\{b_p-a,0\}\). For each positive real \(M\)
write
\[
 J_{\mathcal P}(M)=
 \max_{d\in\mathbb Z,\ 1\le |d|\le M}\#\{p\in\mathcal P:p\mid d\},
\]
with value 0 if there is no such \(d\). We claim
\[
\begin{split}
 p>n^2&\implies b_p=a;\\
 \frac1{|\mathcal P|}\sum_{p\in\mathcal P} b_p\delta_p^2
   &\le \frac{J_{\mathcal P}(n)+J_{\mathcal P}(n^2)}{|\mathcal P|};\\
 \Pr_p[b_p<a]&\le \frac{J_{\mathcal P}(n)}{|\mathcal P|}.
\end{split} \tag{1}
\]
These assertions hold for arbitrary \(\mu\), not just a uniform first
coordinate on its support.

For the last assertion, choose an optimal rational line. If only
one positive-weight point lies on it, its mass is available in every
field via a constant line. Otherwise write the reduced slope as
\(u/v\) with \(v\ge1\). Two points of distinct \(x\) show that \(v\)
divides a nonzero difference of size at most \(n\), so \(v\le n\).
Writing the equation around one of its integer points shows that the
intercept also has denominator dividing \(v\). For every \(p\nmid v\),
the line reduces, giving \(b_p\ge a\); only primes dividing \(v\)
can decrease agreement. The same argument gives \(b_p\ge a\) for every
\(p>n^2\), and the determinant argument in §2 gives \(b_p\le a\)
there.

For the middle assertion, sample three independent integer points
\(P,Q,R\) with law \(\mu\). Independence here is of the auxiliary
points, not of the outputs of the source's randomized function.
For a fixed prime define the following two events:
* \(P\ne Q\), and the reductions of \(P,Q\) agree as points;
* the integer determinant of \(P,Q,R\) is nonzero and divisible by \(p\).

Let \(E_p\) be their union. When \(b_p\le a\), the desired lower
bound on \(\Pr[E_p]\) is zero. Otherwise choose a field line of mass
\(b_p\) and let \(T\) be the integer points reducing onto this line.
A single atom of \(\mu\) has mass at most \(a\), by a rational
constant line. The first draw lies in \(T\) with probability \(b_p\).
Conditional on such a first draw, \(Q\in T\setminus\{P\}\) has
mass at least \(\delta_p\). For each such pair:
1. If \(P,Q\) collapse modulo \(p\), the first event already occurs,
   so allowing every \(R\in T\) gives probability \(b_p\ge\delta_p\).
2. Otherwise the field line is a graph, so the two reduced points
   have different first coordinates. Then the integer points also
   have distinct first coordinates. Their rational graph has mass at
   most \(a\), so \(R\in T\) off that graph has mass at least
   \(\delta_p\). Its determinant is nonzero over the integers and
   zero modulo \(p\), giving the second event.

Therefore \(\Pr[E_p]\ge b_p\delta_p^2\ge\delta_p^3\).
For a fixed distinct pair to collapse, \(p\) must divide a fixed
nonzero coordinate difference of size at most \(n\). A fixed nonzero
determinant has size at most \(n^2\), as shown above. Thus the
probabilities over \(p\) for these events are bounded by
\(J_{\mathcal P}(n)/|\mathcal P|\) and
\(J_{\mathcal P}(n^2)/|\mathcal P|\), respectively.
Average first over the integer points and use a union bound; this
proves (1).

For \(\mathcal P=\mathcal P_k=\{p:2^{k-1}\le p<2^k\}\), \(k\ge2\),
the product of \(j\) distinct prime divisors from this set is at least
\(2^{(k-1)j}\). Applying this to (1) and Jensen's inequality gives
\[
 \mathbb E_p\delta_p\ \le
 \left(\frac{\left\lfloor\log_2 n/(k-1)\right\rfloor+
              \left\lfloor 2\log_2 n/(k-1)\right\rfloor}
             {|\mathcal P_k|}\right)^{1/3}.\tag{2}
\]
For a fully explicit estimate when \(k\ge6\), the standard
Rosser–Schoenfeld inequalities (with natural logarithms) give
\[
 |\mathcal P_k|\ge
 \frac{2^k}{k\ln 2}
 \left(1-\frac{1.25506}{2}\frac{k}{k-1}\right)
 >0.24\frac{2^k}{k}.
\]
The numerator of (2) is at most \(3ck/(k-1)\) when \(1\le n\le2^{ck}\).
Thus in that regime (2) is at most \((15 c k\,2^{-k})^{1/3}\) for
\(k\ge6\), using \(k/(k-1)\le6/5\).
This is an upper bound for the reversed-direction gap with a rational
comparator; there is no claim that its exponent is optimal.
The deterministic equality in (1) gives a stronger zero-error
regime (for instance \(n\le2^{k/5}\) for every \(k\ge2\)).
For small primes the inequality \(b_p\ge a\) need not hold:
\((0,0),(2,1)\) of equal mass at \(p=2\) give \(a=1\), \(b_p=1/2\).
Conversely, \((0,0),(1,2),(2,1)\) of equal mass at \(p=3\)
give \(b_p=1\), \(a=2/3\), with no point collision but
integer determinant \(-3\).
