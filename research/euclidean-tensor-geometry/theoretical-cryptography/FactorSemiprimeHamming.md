# Uniform shifted correlations and Hamming neighbors of balanced semiprimes

Put $\mathcal S_X=\{pq:X<p<q\le2X,\ p,q\text{ prime}\}$. For a nonzero integer $d$ define
$$
R_X(d)=\#\{(N,N')\in\mathcal S_X^2:N-N'=d\},\qquad
\mathfrak S(d)=\prod_{\substack{\ell\mid d\\ \ell\ge5,\ \ell\ \mathrm{prime}}}
                    \left(1+\frac1{\ell-2}\right).
$$
**Theorem.** Uniformly in $0<|d|\le8X^2$,
$$
R_X(d)\ll \frac{X^2}{(\log X)^4}\mathfrak S(d)+\frac{X}{\log X}. \tag{1}
$$
If $N$ is uniform on $\mathcal S_X$ and the integers are padded to a common binary width $B=\lceil\log_2(4X^2+1)\rceil$, then for each fixed $h\ge1$,
$$
\mathbb E\,\#\{N'\in\mathcal S_X:\operatorname{dist}_{\rm Ham}(N,N')=h\}
    \ll_h B^{h-2}. \tag{2}
$$
In particular, the probability of any other balanced semiprime exactly one bit away is $O(1/B)$. This is a counting bound, not an existence theorem at a fixed shift or a procedure for recognizing or recovering factors of an input.

## Fixing one prime reduces the estimate to a modular hyperbola

For an upper bound on $R_X(d)$ count quadruples $p,q,r,s$ of primes in $(X,2X]$ with $pq-rs=d$, dropping both order constraints. If the fixed prime $r$ divides $d$, then $r=p$ or $r=q$, so the other prime in the first product determines $s=(pq-d)/r$. There are $O(1)$ eligible $r\mid d$ since $|d|\le8X^2$, giving the second term of (1) by the prime number theorem. Otherwise $r\nmid d$ and we work with integer pairs $x,y\in(X,2X]$ satisfying $xy\equiv d\bmod r$. For an actual quadruple $x=p$, $y=q$ and $s=(xy-d)/r$ is an integer.

For a squarefree modulus $m$ coprime to $r$, prescribe a pair of residue classes $x\equiv u,y\equiv v\bmod m$. Each prescribed progression in $(X,2X]$ has $X/m+O(1)$ terms. Its indicator with multiplicities can be viewed on $\mathbb Z/r\mathbb Z$, with additive Fourier coefficients normalized by $1/r$. The sum of absolute values of those coefficients is $O(\log(2r))$: the progression has step coprime to $r$ and length $O(r)$, so the geometric series and a harmonic sum give this after permuting the nonzero frequencies. Completion over the modular hyperbola uses
$$
\sum_{w\in(\mathbb Z/r\mathbb Z)^\times}e_r(a w+b d w^{-1}),
\qquad e_r(z)=\exp(2\pi i z/r).
$$
The $(a,b)=(0,0)$ sum is $r-1$. If exactly one frequency is zero the sum is $-1$, and if both are nonzero its absolute value is at most $2\sqrt r$ by [Weil's Kloosterman bound](https://doi.org/10.1073/pnas.34.5.204). Thus the number in this residue pair is
$$
\frac{\mathcal X_r}{m^2}+O\big(\sqrt X(\log X)^2\big),
\qquad \mathcal X_r=(r-1)X^2/r^2\asymp X. \tag{3}
$$
Here the $O(1)$ endpoint errors in each progression make an additional error $O(X/(r m)+1/r)$, absorbed in (3). This bound is uniform in the prescribed pair and in $d$ with $r\nmid d$.

## Sifting the other three entries

For a prime $\ell\ne r$, $\ell$ divides at least one of $x,y,s$ exactly when $x=0$, $y=0$ or $xy=d$ in $\mathbb F_\ell$; the equivalence for $s$ holds since $rs=xy-d$. The number $\rho_\ell$ of such residue pairs is
$$
\rho_\ell =
\begin{cases}
3\ell-2&\ell\nmid d,\\
2\ell-1&\ell\mid d.
\end{cases} \tag{4}
$$
The union of the two axes has $2\ell-1$ pairs. Off the axes there are $\ell-1$ additional pairs on $xy=d$ when $d$ is nonzero, and none when it is zero. For squarefree $m$ supported on the sifting primes, set $\rho(m)=\prod_{\ell\mid m}\rho_\ell$ and $g(m)=\rho(m)/m^2$. The CRT and (3) give the sequence count $\mathcal X_rg(m)+O(\rho(m)\sqrt X(\log X)^2)$ for pairs lying in the bad classes at every prime dividing $m$.

Use primes $5\le\ell\le z$, with $Z=\lfloor X^{1/32}\rfloor$ and $z=Z^c$ for a sufficiently small absolute constant $c>0$. In particular $z<r$ and all sifting primes are below every prime entry of a counted quadruple. The Selberg upper-bound square with weights supported on squarefree $j\le Z$ gives a main coefficient $1/H$, where
$$
H=\sum_{\substack{j\le Z\\j\mid\prod_{5\le\ell\le z}\ell}}
        \prod_{\ell\mid j}\frac{g(\ell)}{1-g(\ell)}.
$$
Its normalized weights have modulus at most $\prod_{\ell\mid j}(1-g(\ell))^{-1}\le j$ because $g(\ell)\le3/\ell$ and $\ell\ge5$. These facts follow by diagonalizing the Selberg quadratic form, as detailed in [the previous common-continuation sieve](FactorRoughAutomaticity.md); they hold for varying $g(\ell)$ as well. In using that form here the CRT error is $\rho([i,j])\sqrt X(\log X)^2$, and $\rho([i,j])\le [i,j]^2\le i^2j^2$. Therefore the total error is
$$
O\left(\sqrt X(\log X)^2\sum_{i,j\le Z}i^3j^3\right)
=O(X^{3/4}(\log X)^2).
$$

For the main coefficient, select each sifting prime $\ell$ independently with probability $g(\ell)$. The product of the selected primes has expected logarithm at most $3\sum_{\ell\le z}\log\ell/\ell\ll\log z$. Taking $c$ small gives probability at least $1/2$ that the product is at most $Z$, by Markov. Its unnormalized masses are the local weights in $H$, so $1/H\le2\prod_{5\le\ell\le z}(1-g(\ell))$.

For $\ell\nmid d$ the factor is $(1-1/\ell)(1-2/\ell)$, and for $\ell\mid d$ it is $(1-1/\ell)^2$. The ratio of the latter to the former is $1+1/(\ell-2)$. By Mertens the product of the first kind of factor over all these primes is $O((\log X)^{-3})$ since $\log z\asymp\log X$. Thus for the fixed $r\nmid d$ the number of candidate quadruples is at most
$$
O\big(X(\log X)^{-3}\mathfrak S(d)+X^{3/4}(\log X)^2\big).
$$
It is legitimate that the sieve counts some pairs for which $(xy-d)/r$ is not in $(X,2X]$: it is only used as an upper bound. Finally there are $O(X/\log X)$ possible primes $r$ and $\mathfrak S(d)\ge1$, so the error is swallowed by $X^2(\log X)^{-4}\mathfrak S(d)$. This proves (1).

## Averaging the singular factor over binary differences

For odd squarefree $m$ supported on primes at least $5$, set $f(m)=\prod_{\ell\mid m}(\ell-2)^{-1}$ and $f(1)=1$, and set $f$ to zero elsewhere. Then $\mathfrak S(d)=\sum_{m\mid |d|}f(m)$. We use
$$
\sum_m \frac{f(m)}{\operatorname{ord}_m(2)}<\infty, \tag{5}
$$
where $\operatorname{ord}_1(2)=1$ and terms with $f(m)=0$ are omitted. For order at most $T$ every prime dividing $m$ divides $A_T=\prod_{j=1}^{\lfloor T\rfloor}(2^j-1)$. We have
$$
\sum_{m:\operatorname{ord}_m(2)\le T} f(m)
\le \prod_{\substack{\ell\mid A_T\\\ell\ge5}}\left(1+\frac1{\ell-2}\right)
 \ll A_T/\varphi(A_T)
 \ll \log\log(3A_T)\ll\log(2T).
$$
The first absorbed product is bounded because dividing each local factor by $(1-1/\ell)^{-1}$ gives $1+O(\ell^{-2})$. The totient bound follows from Mertens by splitting prime divisors at $\log(3A_T)$, and $\log A_T=O(T^2)$. Summing dyadically in the order gives (5).

Fix a signed sum $a$ of $h-1$ selected powers of $2$ with exponents below $B$, and fix the sign $\varepsilon\in\{-1,1\}$. Vary the last exponent $j$, omitting it if it repeats a selected position or makes $a+\varepsilon 2^j=0$. For any $m$ of positive weight, the congruence $a+\varepsilon2^j=0\bmod m$ has either no solutions or one periodic class of $j$ modulo $\operatorname{ord}_m(2)$. Thus it has at most $B/\operatorname{ord}_m(2)+1$ solutions in the allowed range. The extra $1$ need only be counted for $m\mid D=\prod_j|a+\varepsilon2^j|$. Since $\log D=O_h(B^2)$, the sum of its $f(m)$ weights is $O_h(\log(2B))$ by the same totient estimate. Consequently
$$
\sum_j\mathfrak S(a+\varepsilon2^j)\ll_h B
$$
by (5). Fixing the other $h-1$ positions and signs and summing proves $O_h(B^h)$ for the weight of all signed differences of $h$ distinct bits, counted with multiplicity.

Every pair at Hamming distance $h$ has such a nonzero difference. Sum (1) over those binary differences; any beyond the stated shift range simply correspond to no pairs in $\mathcal S_X$. The average after division by $|\mathcal S_X|\asymp X^2/(\log X)^2$ is $O_h(B^h/(\log X)^2+B^h\log X/X)$, giving (2).

## Relation to the literature

[Nevo–Sarnak, *Prime and almost prime integral points on principal homogeneous spaces*, Theorem 1.1](https://arxiv.org/abs/0902.0692) gives a corresponding order of upper bound for prime-entry matrices of a fixed determinant, with constants depending on that determinant and the orbit. For the binary-difference application the determinant varies with $X$. The argument above obtains an explicit uniform loss for the $2$ by $2$ case by fixing one prime, applying modular-hyperbola completion, and sifting the other entries. [Shparlinski's *Primitive points on a modular hyperbola*](https://doi.org/10.4064/ba54-3-1) provides related completion context. Equation (1) gives no lower bound on the number of prime matrices of any fixed determinant.

The [small exact checker](verify_factor_semiprime_hamming.js) verifies the local residue counts, CRT structure and binary-difference identities on predetermined finite data. It does not check an asymptotic estimate or process arbitrary inputs.
