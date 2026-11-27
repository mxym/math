# Near-logarithmic runs with distinct divisor counts (Erdős #945)

Let \(F(X)\) be the longest run of consecutive positive integers at most \(X\) whose divisor counts are pairwise distinct. This note proves the explicit lower bound
\[
 F(X)\gg \frac{\log X}{(\log_2 X)^3\log_3 X},
 \tag{1}
\]
where \(\log_j\) is the \(j\)-fold natural logarithm. The bound is unconditional and holds for all large \(X\). It does not settle the polylogarithmic upper-bound question in [Erdős #945](https://www.erdosproblems.com/945).

In fact, write \(d_\ell(m)\) for the number of ordered \(\ell\)-tuples of positive integers with product \(m\), so \(d_2=\tau\). Fix an integer \(D\ge2\) and \(0<\eta<1/2\). There is a \(c=c(D,\eta)>0\) such that for all sufficiently large \(X\) and every interval \(I\subseteq[X,2X]\) of length \(H\ge X^{1/2+\eta}\), at least \(\gg_{D,\eta}H X^{-\eta/2}\) distinct starts give a block of
\[
 k=\left\lfloor c\,\frac{\log X}{(\log_2 X)^3\log_3 X}\right\rfloor
\]
consecutive integers contained in \(I\), with pairwise distinct \(d_\ell\)-values **simultaneously for each** \(2\le\ell\le D\). Using a macroscopic interval below \(X\) proves (1) and the same order lower bound for each fixed \(d_\ell\).

## 1. Multiplicative labels

For an integer \(a\) and \(2\le\ell\le D\), let \(P_\ell(a)\) mean the part of \(a\) coprime to \(\ell\), found by deleting all powers of primes dividing \(\ell\). This map is multiplicative. A prime occurring to the first power in an integer contributes \(d_\ell(p)=\ell\), so its contribution disappears under \(P_\ell\).

Choose \(r=\lceil\log(kD)/\log 2\rceil\) tag primes \(q_1<\dots<q_r\), each greater than \(D\), with successive gaps greater than \(D\). They may be chosen with \(q_r\ll_D r\log(2r)\), by taking \(O_D(r)\) initial primes and retaining greedily, discarding at most \(D\) others per retained prime. For each \(\ell\), the multiplicative label of a subset \(A\subseteq\{1,\dots,r\}\) is
\[
 \mathcal L_\ell(A)
  =P_\ell\left(\prod_{j\in A}\binom{q_j+\ell-2}{\ell-1}\right).
\]
This is injective in \(A\). Indeed, after canceling common indices, the largest differing tag prime \(q_j\) occurs to the first power in its binomial factor: its numerator is the product of the integers from \(q_j\) to \(q_j+\ell-2\) and its denominator is \((\ell-1)!\). It cannot divide any factor from a smaller index, whose numerator entries are below \(q_j\). It also survives \(P_\ell\) since \(q_j>D\).

For each position \(1\le i\le k\) we will retain the small-prime factorisation of \(i\) as a known offset pattern. Choose subsets \(A_i\) greedily so that for every \(2\le\ell\le D\) the values
\[
 P_\ell(d_\ell(i))\,\mathcal L_\ell(A_i)\qquad(1\le i\le k)
 \tag{2}
\]
are pairwise distinct. For a fixed \(i\), each previous index and each \(\ell\) excludes at most one of the \(2^r\) subsets, by injectivity. There are at most \((D-1)(i-1)<kD\le2^r\) exclusions, so the greedy choice always succeeds. This avoids requiring the small-prime patterns of different offsets to match.

## 2. Set the tags using coprime congruences

Put
\[
 V=\prod_{p\le k}p^{\,1+\lfloor \log k/\log p\rfloor}.
\]
On \(n\equiv0\bmod V\), for every \(p\le k\) and \(1\le i\le k\) one has \(v_p(n+i)=v_p(i)\), since the forced exponent of \(p\mid n\) is strictly larger than \(v_p(i)\). Also \(\log V=O(k)\) by the Chebyshev estimates.

Choose distinct base primes \(p_{i,j}>k\) for each \(i\) and each \(j\in A_i\). There are at most \(kr\) of them; they can all be chosen \(\ll k(\log k)^2\) by the prime number theorem. Impose
\[
 n+i\equiv p_{i,j}^{\,q_j-1}\pmod {p_{i,j}^{\,q_j}}
 \qquad(j\in A_i).
\]
These moduli and \(V\) are pairwise coprime, so all constraints give one progression modulo
\[
 M=V\prod_{i=1}^k\prod_{j\in A_i}p_{i,j}^{\,q_j}.
\]
A tagged prime dividing \(n+i\) cannot divide \(n+i'\) for \(i'\ne i\), since it is larger than \(|i-i'|\). The cost is
\[
 \log M\ll_D k\,r\,q_r\log k
           \ll_D k(\log k)^3\log_2 k.
 \tag{3}
\]
By choosing \(c(D,\eta)\) small enough, (3) gives \(M\le X^{\eta/2}\) for all sufficiently large \(X\).

## 3. Only squarefree cofactors remain for most starts in the progression

Take the starts \(n\) in this progression for which \(n,n+k\in I\); there are \(H/M+O(1+k/M)\) of them. For a prime \(p>k\) not used for a tag, and any \(i\le k\), the additional condition \(p^2\mid n+i\) selects one residue class modulo \(Mp^2\), since \((p,M)=1\). The number of bad starts is therefore at most
\[
 \frac{kH}{M}\sum_{p>k}\frac1{p^2}
   +O(k\sqrt{2X}).
\]
Here \(p>\sqrt{2X}\) cannot divide a term to the second power. The prime tail is \(O(1/(k\log k))\), by a dyadic decomposition and \(\pi(t)\ll t/\log t\). Thus the first term is \(o(H/M)\); for the second, \(kM\sqrt{2X}/H\ll kX^{-\eta/2}=o(1)\). Uniformly for every such interval, \((1-o(1))H/M\) starts survive.

For each survivor the small-prime part of \(n+i\) is exactly \(i\), the tagged factors are exactly the specified powers at their assigned positions, and the remaining factor is squarefree and coprime to them. Since \(d_\ell(p^e)=\binom{e+\ell-1}{\ell-1}\), the prime-to-\(\ell\) part of \(d_\ell(n+i)\) is (2). These parts are distinct for every \(\ell\), so the full values are too. This proves both the local claim and (1).

## Prior work and limits

* P. Erdős and L. Mirsky, [*The distribution of values of the divisor function \(d(n)\)*](https://www.renyi.hu/~p_erdos/1952-12.pdf), Proc. London Math. Soc. **2** (1952), 257–271, Theorem V and Section 11, prescribe a large prime tag at each single position and obtain \(F(X)\gg(\log X)^{1/2}/\log_2 X\). Erdős later stated that with additional work this approach could reach \((\log X)^{1-\varepsilon}\) for any fixed \(\varepsilon>0\); see [his 1985 survey, p. 66](https://www.renyi.hu/~p_erdos/1985-32.pdf). Equation (1) gives an explicit fixed loss in iterated logarithms, stronger than those stated lower bounds, but does not reach \(\log X/\log_2 X\).
* P. Erdős and A. Ivić, [*The distribution of values of a certain class of arithmetic functions at consecutive integers*](https://combinatorica.hu/~p_erdos/1987-32b.pdf), Section 5, already use prescribed prime-power patterns, and use squarefree cofactors for related arithmetic functions. Their stated distinct-value bound for \(d_\ell\) in that section still has the square-root logarithmic scale. The new ingredient here is a family of many distinct multiplicative subset labels with small exponent cost, surviving all squarefree-cofactor contributions and working simultaneously for several \(\ell\).
* Neither (1) nor the localized abundance of blocks gives a polylogarithmic upper bound for \(F(X)\), or suggests that this lower bound is optimal.

The exact-arithmetic companion checks the tag injectivity, offset compensation, and all CRT valuations for small parameter choices. The analytic counting of admissible starts is proved above, not inferred from the finite tests.
