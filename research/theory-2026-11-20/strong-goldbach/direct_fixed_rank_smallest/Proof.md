# A smallest genuine factor bounds the fixed-rank many-small debit

Use the literal true-prime composite proxy of the
[direct fixed-target identity](../direct_goldbach_composite_gap/Proof.md)
and the notation of the [many-small gate](../direct_many_small_gate/Proof.md).
Thus $N=2x$ is even, $L=\log x$, $\ell=\log L$,
$z=\exp(L/\ell^2)$, $y\in J=xJ_0\subseteq[x,3x/2]$,
$P=N-y$ is an ordinary prime, and $C_y=y/x^{1-\epsilon}$.
An actual prime factor of $y$ is small if it is below $C_y$.
Use the real cuts $R_-=x^{1/2-3\log\ell/\ell}$,
$R_+=x^{1/2+3\log\ell/\ell}$, or use the own-root cut
$R_-=R_+=\sqrt y$ throughout. The correction coefficients on either
version are those of the direct identity, without recalibration.

**Theorem.** Fix an integer $r_0\ge5$, then an odd integer $m>r_0$,
then $0<\epsilon<\min(.005,.04/m,1/(20r_0))$, before $x\to\infty$.
Uniformly in the even target, the complete sum of the absolute negative
part of the calibrated score on genuine squarefree $z$-rough $y=N-P$
with at least three actual small factors and rank $\omega(y)\le r_0$
satisfies
\[
 \sum_y \log P\,[-\mathcal R(y)]_+
 \ll_{r_0}
 x\mathfrak S(N)(1+\log(1/\epsilon))^{r_0-4}.
 \tag{1}
\]
The implied constant in (1) is independent of the fixed $\epsilon$ and
$m$; the sufficiently large threshold for $x$ may depend on them.
In particular, for rank five the upper is
$O(x\mathfrak S(N)(1+\log(1/\epsilon)))$, of smaller order in
$\epsilon\to0$ than the protected $\epsilon^{-2}$ reservoir.
The result bounds both choices of cuts directly, without an
unbounded-rank gap transfer.

After applying the many-small gate, one may replace the remaining signed
sum there by the sum over ranks $>r_0$, reducing the constant in front
of $\epsilon^{-2}x\mathfrak S(N)$ by an absolute factor, provided
$\epsilon$ was first chosen sufficiently small in terms of $r_0,J_0$.
The full original payer remains in that remaining sum. Neither the
many-small signed sum to all ranks nor positivity at the original target
is established.

## 1. Exact three-way allocation of one true label

We work only on squarefree $z$-rough rows. Remove the actual opposite
primes $P\mid N$: since $P\in[x/2,x]$, there are $O(1)$, and on the
finite ranks considered their total weighted contribution is $O_{r_0}(L^2)$.
All other physical factors are units modulo $N$.

Write the score as $\mathcal R=\mathcal B+A_+-A_-$.
Here $A_+\ge0$ is the **literal** missing-pair completion and $A_-$
has the odd $m$-factor actual payer. Since we fix ranks at most $r_0<m$,
the payer is absent on every row of (1). It therefore suffices to bound
$|\mathcal B|$. We do not drop the payer on any other rows, and we do not
invoke a compensated subtraction such as (9) in the many-small gate.

In a given row, let $t$ be its smallest small factor and $Y=y/t$.
All cuts below are evaluated at the **same original** $y$.
The baseline is
\[
 \mathcal B(y)
 =\sum_{d\mid y,\ d>R_-}\mu(d)\log(y/d)
   +\sum_{cas=y,\ c<C_y,\ a>R_+}\mu_2(c)\log s,
 \qquad \mu_2=\mu*\mu .
\]
In the first sum, for $d\mid Y$, group the two allocations of $t$
to the divisor versus its complementary factor. Their combined weight is
\[
 \mu(d)\{\mathbf1_{d>R_-}\log t
             -\mathbf1_{R_-/t<d\le R_-}\log(Y/d)\}.
 \tag{2}
\]
In the second sum, for $cas=Y$, the assignments of $t$ to $a,c,s$
have coefficients $1,-2,1$, respectively, before the factor
$\mu_2(c)$. Their combined term is
\[
 \mu_2(c)\left\{
    \mathbf1_{a>R_+,c<C_y}\log t
   +\log s\big[
       \mathbf1_{R_+/t<a\le R_+,\ c<C_y}
      +2\mathbf1_{a>R_+,\ C_y/t\le c<C_y}
      \big]
             \right\}.
 \tag{3}
\]
The strict and non-strict endpoints here follow from the original
$d,a>R_\pm$ and $c<C_y$. Squarefreeness justifies
$\mu(td)=-\mu(d)$ and $\mu_2(tc)=-2\mu_2(c)$.
There are $2^{r-1}$ ordered divisor choices in (2) for $r=\omega(y)$,
and the absolute coefficient sum over all $cas=Y$ in (3) is
$(2+1+1)^{r-1}=4^{r-1}$. Since $\log y\ll L$, it follows that
\[
 |\mathcal B(y)|\ll_{r_0}\log t+
                  L(\mathbf1_{E_-}+\mathbf1_{E_+}+\mathbf1_{E_c}),
 \tag{4}
\]
where $E_\pm$ asks whether a divisor of $Y$ lies in
$(R_\pm/t,R_\pm]$, and $E_c$ asks whether a divisor of $Y$ lies
in $[C_y/t,C_y)$. No sign from a model factor is used.

## 2. True prime bound after fixing the other prime labels

Write the small factors in increasing order
$t=p_1<p_2<\cdots<p_k<C_y$, and the other $j=r-k$ factors in
increasing order $A_1<\cdots<A_j=B$, with $A_i\ge C_y$.
There is no case $j=0$ for sufficiently large $x$, since then
$y\le(1.5x^\epsilon)^{r_0}<x$.
Fix every actual factor but the largest macro factor $B$, and write
$H=y/B$. In any nonempty box,
$B\ge [x/(1.5x^\epsilon)^k]^{1/j}\ge x^{1/(2j)}$ for large $x$.
Thus $X_H=x/(2H)\gg x^{1/(2j)}$, the length of the relaxed
interval $[x/H,1.5x/H]$ for $B$.

The classical two-linear-form upper sieve for $B$ and $N-HB$ gives
\[
 \#\{B\in[x/H,1.5x/H]: B,\ N-HB\text{ prime}\}
 \ll_{r_0}\frac{x\mathfrak S(N)}{H L^2}.
 \tag{5}
\]
For explicit uniformity, the local number of excluded residues is two
at primes outside $NH$, one at primes of $NH$, since $(H,N)=1$;
it is one at 2. Use dimension-two upper beta-sieve weights at sifting limit
$X_H^{1/100}$, level $X_H^{1/4}$, say. The level parameter 25
gives an absolute upper factor, and the floor errors are
$O(X_H^{1/4}(\log X_H)^{O(1)})$ since a squarefree divisor $d$
has at most $2^{\omega(d)}$ excluded-root residue classes.
Neither of the two actual prime values is below the sieve cutoff.
The Euler product contributes $\ll \mathfrak S(N)(\log X_H)^{-2}$
times at most $\prod_{p\mid H}(p-1)/(p-2)=O(1)$, because $H$
has at most $r_0$ factors all exceeding $z$.
Here $\log X_H\gg_{r_0}L$, which gives (5).
It is harmless that a fringe restricts $B$ further: at most the
whole interval bound (5) is used. We only use a necessary interval
for a different fixed prime label before summing that label.

Let $M=1+\log(1/\epsilon)$. The unrestricted harmonic mass for
each other macro factor $A_i\in[x^\epsilon,1.5x]$ is $O(M)$.
We use two elementary prime bounds: harmonic mass over a multiplicative
interval $[U,V]$ is $\ll (1+\log(V/U))/\log U$ for $U\ge3$;
it is also $\ll 1+\log(\log V/\log U)$.
The first follows by covering by intervals of ratio at most $e$
and applying the ordinary Chebyshev prime upper bound; the second
follows from partial summation.

One vanishing small-label logarithm absorbs the whole rough-bank
divergence at every fixed number of labels:
\[
 \sum_{z<t=p_1<p_2<\cdots<p_k\le1.5x^\epsilon}
       \frac{\log t}{t p_2\cdots p_k}
 \ll_k \epsilon L.
 \tag{6}
\]
For example put $U_0=\log(1.5x^\epsilon)$, group
$U_0 2^{-b-1}<\log t\le U_0 2^{-b}$, and bound the
$\log t/t$ sum in that group by $O(U_0 2^{-b})$ using
$\sum_{p\le u}\log p/p\ll\log u$. Each other prime has
harmonic mass $O(1+b)$. The resulting
$U_0\sum_{b\ge0}2^{-b}(1+b)^{k-1}$ is $O_k(\epsilon L)$;
the finitely many allowed groups stop once $t\le z$.
The exact logarithmic model integral is
\[
 \int_{(0,\epsilon)^k}\min(u_1,\ldots,u_k)
                \prod_{i=1}^k\frac{du_i}{u_i}
 = k\int_0^\epsilon (\log(\epsilon/u))^{k-1}\,du
 = k!\epsilon.
\]
Inserting (5), (6) into the first term of (4), and using
$\log P\ll L$, costs
$O_{r_0}(\epsilon M^{j-1}x\mathfrak S(N))$.

## 3. The physical fringe bounds

**Root.** Consider one of $E_\pm$. For large $x$, the root cut
$R$ has size between $x^{.45}$ and $2x^{.55}$.
Every product of small primes in the row is $\le x^{.06}$,
including $t$. If a divisor $d\mid Y$ is in $(R/t,R]$,
it cannot contain no macro factors (too small) or all of them
(too large). In particular the root fringe is absent for $j=1$.
The two divisor sides have magnitude $\gg x^{.38}$:
for the side $d$ use $d>R/t$; for the side $Y/d$
use $Y/d\ge x/(tR)$. Each side therefore has a macro prime
at least $x^{.25/j}$. Choose one such $A_i$ in the side
*not containing* $B$. There are at most $j-1$ index choices
and at most $2^{r_0-1}$ divisor masks.

Fix the remaining macro labels and the small primes.
For the side $d$ not containing $B$, the selected $A_i$
is constrained to a multiplicative interval of ratio $O(t)$
by $R/t<d\le R$.
For the other side, use
$x/(tR)\le Y/d<1.5x/R$.
For an own-root cut use the fixed relaxations
$\sqrt x\le R\le\sqrt{1.5x}$ in each case, preserving ratio
$O(t)$. Thus the selected $A_i$'s harmonic mass is
$O_{r_0}((1+\log t)/L)=O_{r_0}(\log t/L)$;
the remaining $j-2$ macro harmonic sums cost $O_{r_0}(M^{j-2})$.
With (5), (6), $L\log P\ll L^2$, the cost for both root events is
$O_{r_0}(\epsilon M^{j-2}x\mathfrak S(N))$.

**Cofactor cap.** Every qualifying $c\mid Y$ with $c<C_y$
is a product of a subset of the $k-1$ other true small labels,
since no macro factor is below $C_y$. We use the fixed necessary
interval
\[
                    x^\epsilon/t\le c<1.5x^\epsilon .       \tag{7}
\]
It follows from $C_y\in[x^\epsilon,1.5x^\epsilon]$; no cap
endpoint is held fixed while $y$ varies. If $t>x^{\epsilon/4}$,
all $k$ small labels have bounded harmonic mass and the cap
debit is $O_{r_0}(M^{j-1}x\mathfrak S(N))$.
Otherwise $c\ge x^{3\epsilon/4}$, so $c$ is nonempty and
has some prime label at least $x^{3\epsilon/(4r_0)}$.
Fix every other small label; (7) puts the chosen label in an interval
of ratio at most $1.5t$.
Its harmonic mass is $O_{r_0}(\log t/(\epsilon L))$.
We sum over its index and the at most $2^{r_0-1}$ allowed masks.
The $k-2$ other small harmonic factors and the $t$-sum now use
(6) with $k-1$ in place of $k$, so the small-label cost including
$1/(\epsilon L)$ is $O_{r_0}(1)$. This proves the same cap debit
$O_{r_0}(M^{j-1}x\mathfrak S(N))$ even when $j=1$.

Since $j-1=r-k-1\le r_0-4$, (4) gives (1) after summing over
the finitely many $k,j$. The proof never crosses the prime term to
another target and uses no estimates for signed distribution in a
balanced prime-product box. Its tradeoff holds with $r_0,m,\epsilon$
fixed in that order; none may be sent to infinity in $x$.

In comparison, the [exactly-two-small pairing](../direct_two_small_pairing/Proof.md)
controls a different parity-specific strip and the many-small gate
controls all exactly-two-small ranks. The small-window bounds here
are instead for the exact smallest actual label among at least
three. They do not price the high-rank payer, whose negative effect
is intentionally not included in (1).

[Arneth's September 2026 five-factor preprint](https://zenodo.org/records/23016346) gives a different finite balancing calculation, including a single same-target compensation example, and leaves its uniform capacity criterion open. The bound here is uniform over actual prime-opposite rows but only at a predefined finite rank and with the calibrated score defined above.
