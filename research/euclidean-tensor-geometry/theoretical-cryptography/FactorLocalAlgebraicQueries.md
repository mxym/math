# Barriers to changing a semiprime modulus by local algebraic rules

A randomization of an auxiliary challenge at a **fixed modulus** is different from a randomization of the modulus itself. This note gives two finite bounds for the latter in an explicitly restricted model. If each new prime is obtained locally from one of the old primes and the two products satisfy a low-degree algebraic relation, almost every covered query is either the original product or is in a small list depending only on the seed. If the relation has integer coefficients, locality of **just one** new prime suffices for a different, stronger counting bound: outside a small exceptional set of inputs, the query shares an input prime or contains a prime from the coefficient content of a fixed polynomial slice. No general reduction or factoring algorithm is given.

## Setup

Let $\mathcal P$ be a set of $M\ge 2$ distinct primes, $\mathcal S=\{pq:p,q\in\mathcal P,\ p<q\}$, and $K=|\mathcal S|=\binom M2$. We choose $(p,q)$ uniformly from the $M(M-1)$ *ordered* distinct pairs, so $N=pq$ is uniform on $\mathcal S$. A query $Y$ must be a product of two distinct primes. In the statistical corollaries $Y$ must belong to $\mathcal S$, or may take a separate failure value; Theorem 1's counting part does not require the output primes to belong to $\mathcal P$.

An independent random seed specifies a finite menu of charts. In a **two-local chart**, a nonzero polynomial $P(X,Y)\in\mathbb C[X,Y]$ and arbitrary prime-valued functions $A,B$ on $\mathcal P$ are fixed. The chart covers $(p,q,Y)$ when $Y=A(p)B(q)$, $A(p)\ne B(q)$, and $P(pq,Y)=0$. In a **one-local chart**, $P\in\mathbb Z[X,Y]$ and only $A$ is fixed; the conditions are $A(p)\mid Y$ and $P(pq,Y)=0$. We may include either orientation of a chart in the menu. The maps need not be efficiently computable, and the choice of chart may depend arbitrarily on the input, on its presentation order, and on the candidate query. No claim of locality is made for reductions that do not satisfy these conditions. A menu of total degree $D$ means the sum of the degrees of its nonzero polynomials is at most $D$; nonzero constant polynomials cover nothing.

## Theorem 1: two local factors, arbitrary coefficients

For each seed $r$, there is a set $H_r$ of at most $D$ positive numbers determined by its chart polynomials alone. Excluding cases where $Y=N$ or $Y\in H_r$, the fraction of ordered input pairs covered by **any** chart, for **any** output, is at most
$$
\varepsilon_2(M,D)=\min\!\left(1,\frac{DM(\sqrt M+1)+2D\max(M-1,6)}{M(M-1)}\right).
\tag{1}
$$
In particular, the fraction is $O(D/\sqrt M)$ uniformly in the coefficient sizes. If the degrees are fixed, the square-root saving can also be replaced by $O_D(M^{-2/3})$.

**Proof.** Work seed by seed. Factor each $P$ into irreducible complex factors $F$, omitting the coordinate factors $X,Y$, which have no zeros on positive pairs. The sum of the degrees of all the remaining factors, with multiplicities if retained, is at most $D$. Let $H_r$ consist of the positive constants $c$ of the horizontal factors $Y-c$. For a factor of degree $d$, classify its support by the dimension of the real span of differences of its exponent pairs. A monomial contributes no incidences.

*Dimension two.* For each $p$, consider the plane curve given by $F(pX,A(p)Y)=0$. Two distinct $p,p'$ give nonproportional equations. Otherwise, comparing coefficients at any two support exponents would show that $(\ln(p'/p),\ln(A(p')/A(p)))$ is perpendicular to every support difference. The span is two-dimensional and $p'/p\ne1$, a contradiction. Each equation is irreducible, since it is obtained by an invertible diagonal change of variables. Bézout bounds the number of common points of two curves by $d^2$. In particular, at most $d^2$ distinct $q$'s can be neighbors of any two distinct $p$'s in the coverage graph: the witness points are $(q,B(q))$, which are distinct.

If $e$ is the number of edges of the graph and $b_q$ its right degrees, then
$$
\frac{e^2/M-e}{2}
 \le \sum_q\binom{b_q}{2}
 \le d^2\binom M2.
$$
Thus $e\le M(1+\sqrt{1+4d^2(M-1)})/2\le dM^{3/2}+M$. This estimate even counts outputs that are unchanged or horizontal on a different chart. Summing over the dimension-two factors gives at most $DM(\sqrt M+1)$ ordered pairs.

For fixed $d$, the same reasoning with the two roles reversed shows that at most $d^2$ curves pass through two distinct points of the witness set. Pach–Sharir's two-degrees-of-freedom incidence bound for real algebraic curves therefore gives $O_d(M^{4/3})$ incidences. A complex factor not proportional to its coefficientwise conjugate has at most $d^2$ real points by Bézout with that conjugate, contributing only $O_d(M)$. A factor proportional to its conjugate can be normalized to real coefficients. If its real zero set is finite, every real zero is singular (a nonsingular real zero has a real arc by the implicit function theorem), and there are at most $d(d-1)$ such points by Bézout with a nonzero partial derivative. Otherwise the real curve version applies. This proves the fixed-degree alternative after summing the factors.

*Dimension one.* In the Laurent polynomial ring, the support is contained in a coset of the lattice generated by a primitive vector. The polynomial is a monomial times a univariate Laurent polynomial in the corresponding monomial. Factor the latter over $\mathbb C$. Irreducibility remains on inverting $X,Y$ for every factor under consideration, so there is only one nonunit binomial factor. The positive solution locus is thus either a vertical line $X=c$, a horizontal line $Y=c$, or
$$
Y^b=cX^a,\qquad a\in\mathbb Z\setminus\{0\},\quad b\ge1,\quad \gcd(|a|,b)=1,
\quad c>0.
$$
The first allows at most one input product, and the second is already in $H_r$. For the third, one positive integral solution makes $c$ rational. If there are two distinct input products $N_1,N_2$ with outputs $Y_1,Y_2$, choose a prime whose valuations in $N_1,N_2$ differ. Their difference is $\pm1$, since the inputs are products of distinct primes. The valuation identity
$$
b\bigl(v_\ell(Y_1)-v_\ell(Y_2)\bigr)
   =a\bigl(v_\ell(N_1)-v_\ell(N_2)\bigr)
$$
and the squarefree output condition force $b=1$ and $a=\pm1$. If $a=1$, then $Y=cN$. A denominator $>1$ in reduced $c$ forces every input to contain a common fixed prime, hence at most $M-1$ unordered inputs. If $c$ is integral, the number of prime factors with multiplicity in both products is two, so $c=1$ and all solutions are unchanged. If $a=-1$, then $NY=c$. A solution makes $c$ a positive integer with four prime factors counted with multiplicity. There are at most six possible unordered input pairs, by choosing two of those four factors. Thus dimension-one factors other than the ignored horizontal and unchanged cases contribute at most $2D\max(M-1,6)$ ordered pairs. This proves (1).

**Meaning for a randomized query.** Suppose the proposed query $Q$ lies in $\mathcal S\cup\{\bot\}$, is covered with probability at least $\gamma$, and has mean conditional total variation $\delta=\mathbb E_N\,d_{\rm TV}(\mathcal L(Q\mid N),U_{\mathcal S})$, where $\bot$ has zero uniform mass. The independence of the initial seed from the input is what allows (1) to be averaged. For each $N$, its uniform singleton probability is $1/K$, so $\Pr(Q=N)\le\delta+1/K$. Consequently
$$
\Pr(Q\in H_R)\ge \gamma-\delta-1/K-\varepsilon_2(M,D).
\tag{2}
$$
Thus, in this model, a query that is usually covered and conditionally close to fresh uniform semiprimes must usually come from a short list fixed by the seed. Equation (2) makes no assumption that the factorization of a number in this list is known, and gives no generic simulation of oracle responses. Nor does it assert that the distribution conditional on the seed is uniform.

## Theorem 2: one local factor and an integral slice

Assume now $\mathcal P\subset[L,2L)$ for $L>1$ and $Y\in\mathcal S$. In each one-local chart delete the maximal power of $Y$ dividing $P$, without changing the relation at $Y>0$. For the resulting polynomial, put
$$
G(X)=P(X,0)\ne0,\qquad c=\gcd\{\,|g_i|:g_i\ne0,\ G(X)=\textstyle\sum_i g_iX^i\,\}.
$$
For each seed let $C_r\subseteq\mathcal P$ consist of the primes that divide at least one such $c$. If the sum of $\ln c$ over the charts is at most $H$, then $|C_r|\le H/\ln L$.

For every fixed seed, the fraction of ordered input pairs covered by any chart with some output $Y$ satisfying both $\gcd(Y,N)=1$ and $Y$ having no factor in $C_r$ is at most
$$
\varepsilon_1(M,D)=\min(1,D/(M-1)).
\tag{3}
$$
In fact the sum of the slice degrees $\deg G$ can replace $D$.

**Proof.** Fix the chart and $p$, and write $a=A(p)$. On a counted input, $a$ belongs to $\mathcal P$, $a\ne p$, and $a\nmid c$. Reduction of $P(pq,Y)=0$ modulo $a$ gives $G(pq)=0\bmod a$. The polynomial $G(pT)\bmod a$ is not the zero polynomial: multiplication by $p$ is invertible modulo $a$, and at least one coefficient survives. It has at most $\deg G$ roots in $\mathbb F_a$. The $q$'s in $[L,2L)$ are distinct modulo $a$, since $a\ge L$. This gives at most $\deg G$ choices of $q$, independently of how $Y/a$ is selected. Summation over $p$ and the charts proves (3). Each distinct prime counted in $C_r$ contributes at least $\ln L$ to $\sum\ln c$, giving the size claim.

With the same $\gamma,\delta$ as in (2) but for one-local charts, a uniform output shares a prime with a fixed $N$ on exactly $2M-3$ of the $K$ possibilities. Hence
$$
\Pr(Q\text{ has a prime factor in }C_R)
 \ge \gamma-\delta-\frac{2M-3}{K}-\varepsilon_1(M,D).
\tag{4}
$$
If the slices are primitive or have no coefficient-content primes in $\mathcal P$, the left side vanishes. More generally, the exceptions cannot be discarded solely from their set sizes: take a random seed consisting of two distinct uniformly sampled primes $a,b$ and the chart $P(X,Y)=Y-ab$, $A(p)=a$ for every $p$, $Q=ab$. Here $\delta=0$ but $\Pr(Q\in H_R)=1$ and the left side of (4) is one. The coefficient set depends on the same seed that controls the query. Independent-seeming marginals do not justify conditioning on that seed.

In the full $n$-bit prime pool, the prime number theorem gives $M=\Theta(2^n/n)$. For degree budgets polynomial in $n$, (1) and (3) give exponentially small exceptional fractions. This is a statement about the chart contract, not that generic bit-level, adaptive oracles, or nonlocal algebraic maps satisfy that contract. In particular it does not rule out modulus-changing random self-reductions outside the model or infer any lower bound for ordinary integer factorization.

## Related literature and checks

- [Angluin and Lichtenstein, *Provable Security of Cryptosystems: A Survey*, §2.3](https://www.cs.yale.edu/publications/techreports/tr288.pdf) reviews the fixed-modulus square-root reduction due to Rabin; it changes the challenge, not the modulus.
- [Feigenbaum and Fortnow, *On the Random-Self-Reducibility of Complete Sets*](https://cs-www.cs.yale.edu/homes/jf/FF.pdf) and [Bogdanov and Trevisan, *On Worst-Case to Average-Case Reductions for NP Problems*](https://theory.stanford.edu/~trevisan/pubs/redux-sicomp.pdf) study broader complexity restrictions with different hypotheses. Their NP-completeness consequences are not applied to factoring here.
- [Aggarwal and Maurer, *Breaking RSA Generically is Equivalent to Factoring*](https://crypto.ethz.ch/publications/AggMau09.html) uses a generic-ring model and addresses a different question. This note does not impose a generic ring encoding.
- The geometric and counting ingredients are classical: [Fulton, *Algebraic Curves*, §5.3](https://dept.math.lsa.umich.edu/~wfulton/CurveBook.pdf), [Kővári, Sós and Turán](https://doi.org/10.4064/cm-3-1-50-57), and [Pach and Sharir](https://doi.org/10.1017/S0963548397003192) (the real algebraic curve version is stated as Theorem 2.4 by [Pach and de Zeeuw](https://arxiv.org/abs/1308.0177)). The two-local application identifies which low-rank components can have many distinct-prime inputs.
- Run the companion [exact finite checks](verify_factor_local_algebraic_queries.js) with Node.js. They use a hard-coded toy pool and test the counting inequalities and both degeneracies. The proofs above do not depend on the tests.
