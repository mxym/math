# True shared-cofactor forks at every prescribed even target

Fix \(J=[a,b]\subset (0,1)\), \(a<b\). For an even integer \(N\), put
\(I=NJ\), \(I^*=N-I\), \(X=|I|\), \(L=\log N\), and
\[
 \mathfrak S(N)=2\prod_{\ell>2}\left(1-\frac1{(\ell-1)^2}\right)
     \prod_{\substack{\ell\mid N\\ \ell>2}}\frac{\ell-1}{\ell-2}.
\]
All labels \(\ell,r,s,P,P'\) below denote actual rational primes.

**Theorem.** There are fixed \(\eta_0,\beta,c>0\) such that for every
sufficiently large even \(N\), uniformly for \(L^4\le W\le N^{\eta_0}\),
there are at least \(cX\mathfrak S(N)/(L\log W)\) distinct primes
\(P\in I^*\), coprime to \(N\), with
\[
 y=N-P=mr,\quad y\ {\rm squarefree},\quad P^-(y)>W,\qquad
 r>N^{.60},\qquad N^\beta<m\le N^{.40}.                         \tag{1}
\]
For each such \(m\) there is a set \(\mathcal T_m\) of prime tags with
\[
 N^{.009}<s\le N^{.010},\qquad (s,mN)=1,\qquad
 \sum_{s\in\mathcal T_m}\frac1s\ge\tfrac12\log(10/9).             \tag{2}
\]
For **each** \(s\in\mathcal T_m\) there are at least \(cX/(msL^2)\)
distinct primes \(P'\in I^*\), coprime to \(N\), with
\[
 y'=N-P'=m s u,\qquad
 u\ {\rm squarefree},\quad P^-(u)>N^{.020},\quad (u,m)=1.        \tag{3}
\]
All these \(y'\) are squarefree and \(W\)-rough, distinct from (1);
the collections for different \(s\) of the same \(m\) are disjoint.
Their rank jump is \(\omega(y')-\omega(y)=\omega(u)\in[1,49]\).

The choice \(W=N^{1/\log\log N}\) is allowed eventually, giving
\(\gg_J N\mathfrak S(N)\log\log N/L^2\) first rows. Fixed
\(W=N^\eta\), \(0<\eta\le\eta_0\), is allowed as well, bounding both
full ranks. No parity of \(\omega(u)\) or genuine binary prime pair is
asserted.

## 1. Inputs and normalization

Use the [ordinary Bombieri–Vinogradov theorem](https://doi.org/10.1112/S0025579300005313),
the fundamental lemma in dimensions at most two
([Friedlander–Iwaniec, *Opera de Cribro*, Theorem 6.9](https://doi.org/10.1090/coll/057)),
and the linear sieve in the normalization \(F(v)=2e^\gamma/v\)
for \(1\le v\le3\) and \(f(4)>0\)
([Iwaniec, *A new form of the error term in the linear sieve*,
Theorem 1 and (27)–(28)](https://bibliotekanauki.pl/articles/1393119.pdf)).
The fundamental lemma supplies bounded, pointwise upper and lower
divisor sums of level \(D\), for a prime cutoff \(z\), whose model sums
are \(\prod_\ell(1-g(\ell))(1+O_{\kappa}(\Phi(v)))\) with
\(v=\log D/\log z\) and \(\Phi(v)\to0\) as \(v\to\infty\).
Only arbitrarily small *fixed* relative error is needed here.
The linear sieve analogue has the factors \(F(v)+o(1)\) or
\(f(v)-o(1)\). Upper divisor sums are pointwise nonnegative.
The local product hypotheses are uniform below: at 2 the forbidden
density is at most \(1/2\), and at odd primes it is bounded by
\(2/\ell\) in dimension two and by \(1/(\ell-1)\) in dimension one.
The dimension bounds follow by comparison with the relevant power of
the Mertens product, using a factor \(1+O(\ell^{-2})\) at every
odd prime. Restricting the bank cannot worsen those bounds.

Let \(E_M(q)\) be the maximum over reduced residue classes of the error
in a \(\log P\)-weighted sum of genuine primes in an interval with
endpoints bounded by a fixed multiple of \(M\), relative to its length
divided by \(\varphi(q)\); one can take the maximum over endpoints too.
For fixed \(j,A,\epsilon>0\),
\[
 \sum_{q\le M^{1/2-\epsilon}}\tau(q)^j E_M(q)
       \ll_{j,A,\epsilon} M(\log M)^{-A}.                        \tag{4}
\]
The prime form of Bombieri–Vinogradov gives the unweighted estimate.
Cauchy–Schwarz supplies the stated weights because \(E_M(q)\ll
M\log(2M)/q\), and \(\sum_{q\le M}\tau(q)^{2j}/q\) is bounded
by a fixed power of \(\log(2M)\). All uses are in a strict
power-subroot range, so even trivial deletion of proper prime powers
from the usual Mangoldt version has a power saving. In particular
no fixed or small residue assumption applies to \(N\).

Define
\[
 V_W(N)=\prod_{\substack{\ell\le W\\\ell\nmid N}}
              \left(1-\frac1{\ell-1}\right)
        =(1+o(1))\, e^{-\gamma}\frac{\mathfrak S(N)}{\log W},
                                                                  \tag{5}
\]
uniformly for \(W\ge L^4\). Relative to the ordinary Mertens product,
the factors are 2 at 2, \(1-1/(\ell-1)^2\) at odd \(\ell\nmid N\),
and \(\ell/(\ell-1)\) at odd \(\ell\mid N\). The convergent baseline
tail costs \(1+O(1/W)\), and the omitted target factors cost
\(1+O(L/W)\).

## 2. A genuine giant source with the same roughness factor

Discard the \(P\mid N\), of total logarithmic weight at most \(L\).
In the sequence \(y=N-P\), the local density is \(1/(\ell-1)\)
for \(\ell\nmid N\) and zero at \(\ell\mid N\).
The dimension-one fundamental lemma with level \(N^{.001}\) and (4)
evaluate the total \(\log P\)-weight surviving \(P^-(y)>W\)
as
\[
 X V_W(N)(1+e_N)+O_A(NL^{-A}),\qquad |e_N|\le\varepsilon_0,                       \tag{6}
\]
where the model relative tolerance can be taken \(\varepsilon_0=10^{-3}\)
by fixing \(\eta_0\) sufficiently small before \(N\).
Deleting \(P\mid N\) from the progression sums has power-saving cost
even over all these moduli. There are \(O(N/W)\) nonsquarefree
\(W\)-rough integers \(y\le N\), by summing \(N/\ell^2\) over
\(\ell>W\). Their contribution to a \(\log P\log y\) sum is
\(o(XL V_W(N))\). On the surviving squarefree integers
\(\log y=\sum_{r\mid y}\log r=L+O_J(1)\).

For \(W<r\le N^{.498}\), \(r\nmid N\), repeat the fundamental-lemma
*upper* estimate with the prime factor \(r\) marked. A small-bank
divisor \(d\) is coprime to \(r\), and the modulus \(rd\)
is at most \(N^{.499}\). Its density factors as
\(1/(\varphi(d)(r-1))\). A modulus has at most \(\tau(rd)\)
representations as such a product, so (4) absorbs this and
the factor \(\log r\). Removing the upper-bound restriction
\(P\nmid N\) is harmless here since we use only unit moduli.
The total \(\log P\log r\) contribution is therefore at most
\[
 (1+\varepsilon_0)X V_W(N)
       \sum_{W<r\le N^{.498}}\frac{\log r}{r-1}
 +O_A(NL^{-A})
 \le \bigl(.498(1+\varepsilon_0)+o(1)\bigr)XL V_W(N).            \tag{7}
\]
Mertens' prime sum gives the last inequality. No \(r\le W\)
occurs on the selected rows.

Now fix a prime \(N^{.498}<r\le N^{.60}\) with \(r\nmid N\),
put \(y=rm\), and consider \(m\in I/r\), of length \(Y=X/r\).
Sieve the raw integers in two disjoint banks:
\[
\begin{array}{c|c|c}
 \text{primes} &\text{forbidden on }m&\text{upper level}\\ \hline
 \ell\le W & m=0\ \text{or}\ rm=N\pmod{\ell} &Y^{.002}\\
 W<\ell\le Y^{1/2}& rm=N\pmod{\ell}&Y^{.996}.
\end{array}                                                       \tag{8}
\]
Here \(r>Y^{1/2}\) for large \(N\), and \(P=N-rm\asymp_J N\)
lies above all sieved primes. All actual rows with \(m\) rough
and \(P\) prime survive. In the first bank there are two roots
except at \(\ell\mid N\), where the roots coincide; in particular
the root at 2 is 0. The first-bank survival factor is exactly
\((1-1/\ell)\) times the \(\ell\)-factor of \(V_W(N)\).
The second bank has one root per prime. The joint Euler product
is therefore \(V_W(N)\prod_{\ell\le Y^{1/2}}(1-1/\ell)\).

Multiply the pointwise nonnegative fundamental-lemma upper sum
for the first bank by the upper linear-sieve sum for the second.
Since \(\log Y\ge(.40-o(1))L\), by shrinking \(\eta_0\) the
first-bank relative model error is at most \(\varepsilon_0\).
The second-bank parameter is 1.992. The total level is
\(Y^{.998}\). For squarefree \(d_0,d_1\) from the two banks,
the integer CRT remainder is \(O(2^{\omega(d_0)})\), since
each \(\ell\mid d_1\) has a single root. Summing the bounded
weights over \(d_0,d_1\) gives \(O(Y^{.998}(\log Y)^{O(1)})\),
negligible relative to \(YV_W(N)/\log Y\) uniformly.
Thus the two-bank classical upper-sieve calculation gives
\[
 \#\{m\in I/r:\ P^-(m)>W,\ N-rm\ {\rm prime}\}
 \le \left(\frac{2(1+\varepsilon_0)}{.996}+o(1)\right)
            \frac{Y V_W(N)}{\log Y}.                            \tag{9}
\]
This is Brun–Titchmarsh with the shared small-prime exclusion,
not an assertion of equidistribution for large prime moduli.

Multiply (9) by \(L\log r\) and sum the strip. With \(Y=X/r\),
partial summation from \(\sum_{r\le t}\log r/r=\log t+O(1)\)
shows that its \(\log P\log r\) mass divided by \(XL V_W(N)\)
is bounded by
\[
  \frac{2(1+\varepsilon_0)}{.996}\log\left(\frac{.502}{.400}\right)
       +o(1).                                                   \tag{10}
\]
The logarithm is strictly below .23, since
\(1+.23+.23^2/2>251/200=.502/.400\). Equations (7) and
(10) add to less than .962 after normalization for large \(N\),
whereas (6) gives at least \(1-\varepsilon_0-o(1)\) for
the normalized total \(\log P\log y\) mass of squarefree
\(W\)-rough rows. This forces positive logarithmic mass beyond .60.
There is at most one such factor in each \(y\), and each weighted
row costs at most \(L^2\). Thus at least \(c_0XV_W(N)/L\)
distinct primes have that giant, initially allowing \(m=1\).

## 3. Removing tiny and exceptional cofactors

For \(W\)-rough \(m\le N^{.40}\) coprime to \(N\), bound the
number of simultaneous actual primes \(r,N-mr\) in \(r\in I/m\).
Take the true \(r\)-prime source of scale \(R=N/m\ge N^{.60}\),
with upper linear sieve at level \(R^{.49}\) and cutoff \(R^{.20}\)
on \(N-mr\). The local density at \(\ell\) is \(1/(\ell-1)\)
if \(\ell\nmid Nm\), zero otherwise. At \(\ell\mid m\) the
sieved expression is nonzero; at \(\ell\mid N\) its only root
on \(r\) is zero, and \(r\asymp_J R\) exceeds all sieve primes.
At the other moduli the actual residue is \(Nm^{-1}\).
Equation (4) is uniform in that residue. The usual upper sieve
and Mertens, with the same local comparison as in (5), give
\[
 \#\{ r\in I/m:\ r,N-mr\ {\rm prime}\}
 \ll_J \frac{X\mathfrak S(Nm)}{mL^2}
 \ll_J \frac{X\mathfrak S(N)}{mL^2},                              \tag{11}
\]
uniformly in \(N,m\). The last inequality uses
\(\mathfrak S(Nm)/\mathfrak S(N)=1+o(1)\), since the extra
prime divisors of \(m\) are \(>W\), and
\(\sum_{\ell\mid m}1/(\ell-2)=O(L/W)\).
This argument includes \(m=1\).

With \(P^-(1)=\infty\), one has
\[
 \sum_{\substack{m\le Z\\P^-(m)>W}}\frac1m
       \ll 1+\frac{\log Z}{\log W}.                             \tag{12}
\]
Below \(W^2\) only 1 and primes \(>W\) occur.
For \(t\ge W^2\), the ordinary integer upper linear sieve with
level \(W^{3/2}\) gives a rough count
\(\ll t/\log W+W^{3/2}\ll t/\log W\).
Partial summation proves (12). Thus (11) summed over
\(m\le N^\beta\) costs
\[
 O_J\left(\frac{X\mathfrak S(N)}{L\log W}
                         \left(\beta+\frac{\log W}{L}\right)\right).
\]
First fix \(\beta>0\) sufficiently small in terms of the preceding
positive constant and (11)–(12), then shrink \(\eta_0\)
so this deletion costs at most one quarter of the first count.
No Goldbach-failure assumption is used when removing \(m=1\).

## 4. True second rows at the same physical cofactor

Take \(m\le N^{.40}\), \((m,N)=1\), and a prime tag \(s\)
in the band of (2) with \((s,mN)=1\). Start with genuine primes
\(P'\in I^*\) in class \(N\bmod ms\). In the sequence
\(u=(N-P')/(ms)\) use the lower linear sieve at level
\(D=N^{.08}\) and cutoff \(z=N^{.020}\). The principal mass
is \(X/\varphi(ms)\). For a sieve prime \(\ell\) its conditional
density is exactly
\[
 g_{m,s}(\ell)=
 \begin{cases}
 0 &\ell\mid N,\\
 1/\ell &\ell\mid ms,\\
 1/(\ell-1)&\ell\nmid Nms .
 \end{cases}                                                    \tag{13}
\]
For unit moduli this follows by taking
\(\varphi(ms)/\varphi(ms\ell)\). In particular when
\(\ell\mid m\) or \(\ell=s\), sieving \(u\) increases the
modulus exponent by one. Multiplicativity over squarefree \(d\)
also follows from this ratio. A nonunit \(d\) could have an
occurrence only if \(P'\) is a prime dividing \(d\), impossible
since \(d\le D\) and \(P'\asymp_J N\).
We may remove \(P'\mid N\) after sifting at cost at most
\(L\) per \((m,s)\).

The sieve parameter is 4, with \(f(4)>0\), and (13) gives a
uniform Euler lower bound \(\gg 1/L\) and the dimension-one
upper product bound. Thus the \(\log P'\)-weighted rough count
is \(\gg_J X/(msL)\) apart from an error bounded by a fixed
constant times
\[
 \mathcal E_{m,s}
   =\sum_{\substack{d\le D\\(d,N)=1}}\tau(d)^C E_N(msd).           \tag{14}
\]
Bounded sieve weights allow \(C=0\); any fixed divisor-power
loss is harmless. The moduli \(msd\le N^{.49}\) lie in (4).
For one modulus \(q=msd\), the number of ordered representations
is at most \(\tau(q)^2\) by choosing \(m\) and \(s\) as divisors.
This does not require \((d,ms)=1\), and \(\tau(d)^C\le\tau(q)^C\).
Thus
\[
 \sum_{m,s}\mathcal E_{m,s}\ll_{A,J} N L^{-A}\qquad(A>0).         \tag{15}
\]

Call a pair deficient if \(\mathcal E_{m,s}>\kappa X/(msL)\)
with a sufficiently small fixed \(\kappa>0\).
Equation (15) gives
\(\sum_{\rm deficient}1/(ms)\ll_{A,J}L^{-A}\) for every fixed \(A\),
by choosing the input power larger. The full tag harmonic mass is
\(\log(10/9)+o(1)\) by Mertens. Excluding primes dividing \(mN\)
costs \(O(LN^{-.009})\) uniformly. Outside a set of \(m\) with
reciprocal sum \(O_{A,J}(L^{-A})\), nondeficient allowed tags
therefore have reciprocal mass at least \(\tfrac12\log(10/9)\).
For each such tag, the selected rough \(u\) that are not squarefree
number \(O(N/(ms z))\), by summing \(N/(ms\ell^2)\) at \(\ell>z\).
Those with \((u,m)>1\) number \(O(N\omega(m)/(ms z))\), since
a common prime exceeds \(z\). Multiplying either bound by
\(L\) leaves \(o(X/(msL))\); these subtractions and the
\(P'\mid N\) removal preserve the lower bound. Hence (3)
counts at least \(cX/(msL^2)\) distinct literal primes.

The first-source rows on exceptional \(m\) are negligible:
dropping the condition that \(N-mr\) is prime, the prime number
theorem at scale \(N/m\ge N^{.60}\) gives
\(O_J(N/(mL))\) possible \(r\) per \(m\).
Multiplying by the exceptional reciprocal sum saves arbitrary
log powers compared to \(c_0XV_W(N)/L\).

Finally \(m\) is squarefree and rough from the first row,
\(s\nmid m\) by the explicit unit filter \((s,mN)=1\), and
\(s>W\) by choosing \(\eta_0<.009\).
No prime in the entire tag bank can divide \(u\) because \(z>N^{.010}\).
Thus the designated tag is the only new tag-bank prime outside \(m\),
so different \(s\) give disjoint sets of \(P'\).
The quotient \(su\) is composite since \(u\asymp_J N/(ms)>1\);
it cannot be the original prime \(r\).
All \(y'\) are squarefree and rough. Finally \(u<N\) and
\(P^-(u)>N^{.020}\) imply \(1\le\omega(u)<50\).

## Comparison and scope

The logarithmic balance is classical: see [Goldfeld, *On the number of primes \(p\) for which \(p+a\)
has a large prime factor*, Theorem 1 and §§2–3](https://www.math.columbia.edu/~goldfeld/PrimeShifts.pdf)
and the independent work of Motohashi. Combining that balance with
the classical constant \(2\) of the
[Montgomery–Vaughan Brun–Titchmarsh inequality](https://doi.org/10.1112/S0025579300004708)
gives the familiar \(1-\tfrac12e^{-1/4}=.6105\ldots\) exponent.
The original shifted-prime theorem fixes the additive shift. The result here uses a moving reflection
\(N-P\), a macroscopic interval, and the same *actual roughness*
factor in the log balance and strip cap, then couples the large
prime factor row to new actual prime rows at its physically attained
cofactor. No novelty is claimed for the classical exponent or sieves.
For a modern fixed-shift comparison
[Li, arXiv:2508.18285v3](https://arxiv.org/abs/2508.18285v3)
states a stronger exponent for infinitely many \(p\) on \(p-1\);
it is not substituted for a uniform moving-target result.
The [balanced rough reservoir](../balanced_rough_reservoir/Proof.md)
gives different physical rows with all factors below the square-root
rail. Neither result supplies the parity of the residual in (3).

The optional exact arithmetic controls replay with
`python3 -O -B check.py`; they verify local formulas and the
strict rational parameter margins, not the analytic theorem.
