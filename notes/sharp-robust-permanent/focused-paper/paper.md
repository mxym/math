---
title: 'Sharp Chebyshev Atom Moduli for Fixed-Rank Subset Actions'
subtitle: 'An all-rank asymptotic theorem and exact finite orbital certificates'
author: 'mxym/math research project (AI-assisted)'
date: 'October 8, 2026'
fontsize: 11pt
geometry:
  - margin=27mm
abstract: |
  Let S_n act on the k-subsets of [n], and constrain a probability law
  on S_n to have uniform subset-image marginals. We prove for every fixed
  k that the best coefficient comparing any single atom's deviation from
  uniform with total variation equals 1 - 2k^2/n + O_k(n^-2).
  A corrected Chebyshev dual gives the uniform upper bound, and exactly
  moment-matched positive conjugation-invariant measures give the lower
  bound. We also prove an exact all-rank transfer-matrix cycle-compression
  theorem and provide independent exact finite certificates for all
  four-subset actions through degree 64.
---

## Problem and main results

For the natural action of the symmetric group $S_n$ on
$\Omega_{n,k}=\binom{[n]}k$, write $u_n$ for uniform probability
on $S_n$. A probability measure $\nu$ is admissible if
$$\nu\{\pi:\pi(A)=B\}=\binom nk^{-1}
\quad\text{for all } A,B\in\Omega_{n,k}.$$
The sharp atom-vs-total-variation coefficient is
$$C_n^{(k)}=\sup_{\nu\ne u_n\text{ admissible}}
 \frac{|\nu(\mathrm{id})-1/n!|}{\|\nu-u_n\|_{\mathrm{TV}}}.$$
Left translation gives the same coefficient at every other permutation.

**Main theorem.** For every fixed $k\ge1$,
$$\boxed{C_n^{(k)}=1-\frac{2k^2}{n}+O_k(n^{-2}).}$$
The proof below also gives the exact leading masses of the primal
extremizing class mixtures and an orbital dual with a matching
oscillation bound. This statement is a complete fixed-rank asymptotic
theorem, not a formula for every finite $(n,k)$.

The finite companion determines the exact $k=4$ coefficient
for every $4\le n\le64$ with fixed rational primal-dual certificates;
the separate all-rank transfer formula allows finite exact searches
using only short-cycle counts.

**Verification status.** The full all-rank proof is analytic.
Symbolic and integer checkers replay selected identities and fixed
finite certificate ranges, not the universal quantified theorem.
External human peer review and systematic novelty certification
remain pending. The companion public proof dossier is at
https://github.com/mxym/math/tree/main/notes/sharp-robust-permanent.

---

## 18. Universal orbital primal-dual theorem for finite permutation actions

Theorems 15–17 are instances of a general exact principle: **the sharp single-atom response to marginal-preserving perturbations is determined by a finite rational linear program on the conjugacy classes and the orbitals of the permutation representation**. In a doubly transitive action there are only two orbitals; in the two-subset action there are three. This explains the difference between the minimal-degree formula and the exact edge-action law.

Let $G$ be a finite group acting (not necessarily transitively or faithfully) on a finite nonempty set $\Omega$, with $e\in G$ its identity. Write $u_G$ for the uniform law on $G$, and let $\mathcal V$ be the real vector space of signed functions $v:G\to\mathbb R$ satisfying

$$\sum_{g\in G}v(g)=0,\qquad
\sum_{\substack{g\in G\\g(x)=y}}v(g)=0
\quad\text{for all }x,y\in\Omega. $$

Let $\mathcal O_1,\ldots,\mathcal O_r$ be the orbitals of the action, i.e. the orbits of $G$ on $\Omega\times\Omega$ under simultaneous relabeling. Define their *orbital displacement counts*

$$F_j(g)=\#\{x\in\Omega:(x,g(x))\in\mathcal O_j\}. $$

Each $F_j$ is constant on conjugacy classes of $G$. Let $C_1,\ldots,C_s$ be those conjugacy classes, with $C_1=\{e\}$, and put

$$M_{ji}=\frac1{|C_i|}\sum_{g\in C_i}F_j(g),\qquad
M\in\mathbb Q^{r\times s}. $$

For $\mathcal V\ne\{0\}$, define

$$\mathcal C(G,\Omega)=\sup_{\substack{v\in\mathcal V\\v\ne0}}
\frac{|v(e)|}{\tfrac12\sum_g|v(g)|}. $$

For $\mathcal V=\{0\}$, set $\mathcal C(G,\Omega)=0$. The supremum is finite and $0\le\mathcal C(G,\Omega)\le1$.

**Theorem 18 (exact orbital primal-dual characterization).** The following four quantities are all equal:

$$\begin{aligned}
\mathcal C(G,\Omega)
&=\max_{\substack{P,Q\text{ probability laws on }G\\
P\{g:gx=y\}=Q\{g:gx=y\}\ \forall x,y}}
\big(P(e)-Q(e)\big)\\
&=\max_{\substack{p,q\in\mathbb R_{\ge0}^{s}\\
\mathbf1^Tp=\mathbf1^Tq=1,\ Mp=Mq}}
(p_1-q_1)\\
&=\min_{\lambda\in\mathbb R^r}
\left[
\max_{1\le i\le s}\big(\mathbf1_{\{i=1\}}-\lambda^TM_{\cdot i}\big)
-\min_{1\le i\le s}\big(\mathbf1_{\{i=1\}}-\lambda^TM_{\cdot i}\big)
\right]\\
&=\min_{\varphi\in\mathrm{span}_{\mathbb R}\{F_1,\ldots,F_r\}}
\operatorname{osc}_{g\in G}\big(\mathbf1_{\{g=e\}}-\varphi(g)\big).
\end{aligned}$$

Both finite LPs in the middle have **rational optimal solutions**, so $\mathcal C(G,\Omega)\in\mathbb Q$. If $\mathcal C(G,\Omega)>0$, there exist two **conjugation-invariant, disjointly supported** probability laws $P,Q$ with identical one-point marginals and $P(e)-Q(e)=\mathcal C(G,\Omega)$. Hence for all sufficiently small $\delta\ge0$,

$$\nu_\delta=u_G+\delta(P-Q) $$

is a probability law with exactly the same one-point marginals as $u_G$ and

$$\|\nu_\delta-u_G\|_{\mathrm{TV}}=\delta,\qquad
\nu_\delta(e)-u_G(e)=\mathcal C(G,\Omega)\delta. $$

For an arbitrary probability law $\nu$ whose marginals match $u_G$, and any $\sigma\in G$,

$$\left|\nu(\sigma)-\frac1{|G|}\right|
\le\mathcal C(G,\Omega)\|\nu-u_G\|_{\mathrm{TV}}, $$

with this constant optimal whenever it is positive. Left translation moves the sharp construction from $e$ to any prescribed $\sigma$.

**Proof.** First formulate a finite **unreduced** LP. Choose $P,Q$ as nonnegative probability vectors indexed by $G$, impose their equality of all one-point marginals, and maximize $P(e)-Q(e)$. Call its optimum $\gamma$.

For any feasible pair, $v=P-Q\in\mathcal V$, $\|v\|_{\mathrm{TV}}\le1$, so $P(e)-Q(e)\le\mathcal C(G,\Omega)$. Conversely, for any nonzero $v\in\mathcal V$, its Jordan parts $v_+,v_-$ each have mass $d=\|v\|_{\mathrm{TV}}>0$, and the probability measures $P=v_+/d,\ Q=v_-/d$ have identical marginals. Exchanging them if necessary, they give objective $|v(e)|/d$. Hence $\gamma=\mathcal C(G,\Omega)$. If $\mathcal V=\{0\}$, the two quantities are both zero.

The unreduced primal is a rational finite LP. Its dual has one unrestricted multiplier $\lambda_{xy}$ for each marginal equality and two normalization multipliers $a,b$. Write

$$\phi(g)=\sum_{x,y\in\Omega}\lambda_{xy}\,\mathbf1_{\{g(x)=y\}}.$$

Dual feasibility is exactly

$$a\ge\mathbf1_{\{g=e\}}-\phi(g),\qquad
b\ge-\mathbf1_{\{g=e\}}+\phi(g)
\quad\text{for all }g\in G.$$

Minimizing $a+b$ for fixed $\phi$ gives
$\max_g(\mathbf1_{\{g=e\}}-\phi(g))-
\min_g(\mathbf1_{\{g=e\}}-\phi(g))$, its oscillation. The primal is feasible (take $P=Q=u_G$) and bounded, so **finite-dimensional LP strong duality** gives equality with the minimum oscillation. The LP has rational coefficients and a finite attained optimum; standard rational Gaussian elimination at a basic feasible optimum gives rational primal and dual certificates.

Next average an optimal primal pair under simultaneous conjugation by $h\in G$: replace $P,Q$ by the averages of their pushforwards under $g\mapsto hgh^{-1}$. Equal one-point marginals remain equal because conjugating both pairs of image coordinates by $h$ permutes the constraints. The identity atom and the objective are unchanged. Thus a conjugation-invariant optimal pair exists. Such pairs assign a constant probability density to each conjugacy class, and their equality of one-point marginals is equivalent to the reduced moment equation $Mp=Mq$: for a central law, each entry $\Pr(gx=y)$ is constant on the orbital containing $(x,y)$, and its orbital average is $\mathbb EF_j/|\mathcal O_j|$. This proves the second line of (91).

Similarly, average any dual function $\phi$ over conjugations. The indicator $\mathbf1_{\{g=e\}}$ is conjugacy invariant, while oscillation is convex and invariant under conjugation; the average cannot increase oscillation. A conjugation-averaged linear combination of the image indicators has coefficients constant on their simultaneous $G$-orbits in $\Omega\times\Omega$. Therefore it lies in $\mathrm{span}\{F_j\}$. This proves the fourth line of (91). Evaluating the same oscillation on conjugacy classes gives the third line, whose entries are precisely (89).

When the optimum $\gamma>0$, an optimal reduced pair $P,Q$ must be **mutually singular**. Otherwise $d=\|P-Q\|_{\mathrm{TV}}<1$, and its Jordan parts normalized by $d$ would form an admissible pair with strictly larger objective $\gamma/d>\gamma$, contradiction. Thus the supports of an optimal central $P,Q$ are disjoint and (92) is a probability measure for every
$0\le\delta\le(|G|\max_gQ(g))^{-1}$, with all the stated identities.

Finally, for any law $\nu$ with the uniform law's one-point marginals, $v=\nu-u_G\in\mathcal V$ and the defining norm bound gives (94) at the identity. Replacing $\nu$ by its left translate by $\sigma^{-1}$ preserves marginal equality with $u_G$, total variation and atom excess, proving (94) for every $\sigma$. The same translation transports the attained equality. QED.

**Consequences and scope.** Theorem 18 gives a fully finite **exact certificate interface** for *every* finite permutation group action: exhibit a central primal pair of matching orbital moments and a dual orbital linear combination whose oscillation equals the primal atom excess. It also explains Theorem 15 (rank-two orbital geometry and a single fixed-point statistic), Theorem 16 (rank-three geometry in degree ten), and Theorem 17 (a full parity-dependent family of exact rank-three optima). The theorem does **not** assert a similarly explicit symbolic formula for arbitrary higher-rank actions. Determining a closed analytic optimum for $S_n$ acting on $k$-subsets with $k\ge3$ is a natural next target; numerical LP output there must be converted to rational primal-dual certificates before any theorem claim.



## 23. General $k$-subset orbital Bernstein limits and a Chebyshev research direction

The first-order constants $2,8,18$ in the one-, two-, and three-subset actions have a common structure. The orbital basis of **every fixed subset rank** converges to the Bernstein polynomial basis, while the explicit duals in ranks $1,2,3$ converge to *shifted Chebyshev polynomials*. The first observation is a rigorously proved general theorem. Its extension to a sharp all-$k$ atom-TV asymptotic remains a conjecture.

Let $1\le k\le n$, let $\Omega_{n,k}=\binom{[n]}k$, and define

$$F_j^{(k)}(g)
=\#\{E\in\Omega_{n,k}:|E\cap g(E)|=j\}
\quad(0\le j\le k).$$

Write $x(g)$ for the number of fixed vertices and $a(g)=x(g)/n$. Define the Bernstein basis
$B_{j,k}(a)=\binom kj a^j(1-a)^{k-j}$.

**Theorem 23 (uniform Bernstein orbital approximation).** For every $n\ge\max(k,2)$, every permutation $g\in S_n$, and every $0\le j\le k$,

$$\boxed{
\left|\frac{F_j^{(k)}(g)}{\binom nk}
       -B_{j,k}(a(g))\right|
\le\frac{k(k-1)}{n-1}+\frac{k(k-1)}{2n}.
} $$

Indeed the **total variation distance between the entire two distributions** on $j=0,\ldots,k$ satisfies the same bound. Consequently for every fixed $k$, the $k+1$ normalized orbital statistics converge uniformly over $g\in S_n$, at rate $O_k(n^{-1})$, to the Bernstein basis of polynomials of degree at most $k$.

**Proof.** Choose a uniformly random $k$-subset $E$, and let $X=|E\cap g(E)|$. Let $S$ be the fixed-vertex set of $g$, with $|S|=x$, and put $Y=|E\cap S|$. Every fixed vertex in $E$ also belongs to $g(E)$, hence $X\ge Y$. Any extra element $v\in E\cap g(E)\setminus S$ requires the two **distinct** vertices $v$ and $g^{-1}(v)$ both to belong to $E$. For each moved vertex $v$, the probability of this pair event is exactly $k(k-1)/(n(n-1))$. By the union bound,

$$\mathbb P(X\ne Y)
\le (n-x)\frac{k(k-1)}{n(n-1)}
\le\frac{k(k-1)}{n-1}. $$

The variable $Y$ has the hypergeometric distribution of the number of successes in $k$ draws without replacement from a population of $n$ with $x$ successes. Draw instead $k$ vertices independently and uniformly with replacement, and let $Z\sim\operatorname{Binomial}(k,x/n)$ count successes. The distribution of the ordered independent sample **conditioned on distinctness** is exactly that of ordered sampling without replacement. The probability of a collision is at most $\binom k2/n=k(k-1)/(2n)$; thus the total variation distance between $Y$ and $Z$ is at most this probability. By the coupling characterization and the triangle inequality,

$$d_{\mathrm{TV}}\bigl(\mathcal L(X),\mathcal L(Z)\bigr)
\le\mathbb P(X\ne Y)+
d_{\mathrm{TV}}\bigl(\mathcal L(Y),\mathcal L(Z)\bigr),$$

which is (123) for the full distributions and hence for each coordinate. QED.

**Proposition 24 (Chebyshev limiting duals in ranks $1,2,3$).** Let $T_k$ denote the Chebyshev polynomial of the first kind, $T_k(\cos\theta)=\cos(k\theta)$. In each of the already proved ranks $k=1,2,3$, the leading nonidentity orbital dual polynomial of the sharp or sharp-order certificates is

$$\boxed{H_k(a)=\frac{1-T_k(2a-1)}2,}$$

namely

$$H_1(a)=1-a,\qquad
H_2(a)=4a(1-a),\qquad
H_3(a)=(1-a)(4a-1)^2.$$

All satisfy $0\le H_k(a)\le1$ for $0\le a\le1$, $H_k(1)=0$, and the endpoint derivative identity

$$-H_k'(1)=k^2. $$

**Proof.** The polynomial identities follow by substituting $T_1(t)=t$, $T_2(t)=2t^2-1$, and $T_3(t)=4t^3-3t$. For $k=1$, the fixed-point dual $h(g)=\mathbf1_{\{g=e\}}+(n-x(g))/n$ has nonidentity profile $H_1(x/n)$ exactly. For $k=2$, the exact duals (76) and (81) have the common leading nonidentity profile $4a(1-a)$: substitute the leading terms of (68) with $x=an$ and $y=O(n)$. For $k=3$, equation (113) provides the exact leading polynomial $H_3$. The range and derivative statements follow from $|T_k(t)|\le1$ on $[-1,1]$ and $T_k'(1)=k^2$. QED.

This exhibits why the exact first-order constants are

$$\begin{array}{c|c}
k & \displaystyle\lim_{n\to\infty}n(1-C_n^{(k)})\\ \hline
1&2\quad\text{(Theorem 15)},\\
2&8\quad\text{(Theorem 17)},\\
3&18\quad\text{(Theorem 22)}.
\end{array}$$

A nonidentity vertex permutation must move at least two vertices, so the closest possible fixed-point fraction to $1$ is $1-2/n$. For a shifted Chebyshev dual, the endpoint loss is therefore $2k^2/n+O_k(n^{-2})$. This interpretation is exact for the three established ranks; it motivates but **does not prove** the following general question.

**Historical conjecture (now proved in Theorem 25).** For every fixed $k\ge4$, the optimal coefficient for $S_n$ acting on its $k$-subsets satisfies

$$C_n^{(k)}=1-\frac{2k^2}{n}+O_k(n^{-2})
\qquad(n\to\infty). $$

A viable proof must address **both sides**: construct a uniformly valid orbital dual with the appropriate subleading corrections, and match it by genuine nonnegative class measures with exactly equal $k$-subset image marginals. Theorem 23 alone proves only Bernstein convergence; it does not control the $1/n$ coefficient or justify a Chebyshev optimizer. Numerical LP output at fixed degrees also cannot establish (128). **Status update:** this was the research conjecture at the time of Section 23; the full fixed-rank statement is now **proved** in Theorem 25, Section 24. The finite-n exact classification remains open.



## 24. Resolution of the fixed-rank Chebyshev atom-modulus conjecture

The conjecture in Section 23 admits a **complete affirmative proof for every fixed subset rank**. The argument has three independent parts: a uniform first-order orbital expansion, a corrected Chebyshev dual giving an upper bound, and genuine positive probability measures at Chebyshev–Lobatto nodes giving the matching lower bound. None of these uses the finite LP computations as a proof premise.

For fixed $k\ge1$, denote by $C_n^{(k)}$ the optimal single-atom versus total-variation coefficient for the natural $S_n$-action on $\binom{[n]}k$, under preservation of every one-point subset-image marginal, as defined by Theorem 18.

**Theorem 25 (sharp universal fixed-rank law).** For **every fixed integer $k\ge1$**,

$$\boxed{ C_n^{(k)}=1-\frac{2k^2}{n}+O_k(n^{-2})\qquad(n\to\infty). } $$

In particular,

$$\boxed{\lim_{n\to\infty}n(1-C_n^{(k)})=2k^2.} $$

Both sides of the asymptotic bound follow from independently specified, rigorous constructions. The primal measures have **exactly** matching subset-image marginals, not merely asymptotically matching ones.

### 24.1. A uniform first-order orbital expansion

For $n\ge2k$, $g\in S_n$, let $x$ and $y$ be its numbers of 1-cycles and 2-cycles, and set $a=x/n$, $b=y/n$. Necessarily $0\le a\le1$ and $0\le b\le(1-a)/2$. Choose uniformly $E\in\binom{[n]}k$, put $X=|E\cap g(E)|$, and write

$$G_{n,g}(t)=\mathbb E[t^X],\qquad B(t)=1-a+at.$$

**Lemma 26 (uniform orbital generating expansion).** For each fixed $k\ge2$,

$$\begin{aligned}
G_{n,g}(t)
={}&B(t)^k+\frac{k(k-1)}{n}B(t)^{k-2}
\Big[(1-a)(t-1)\\
&\hspace{56pt}+\big(b-\tfrac12a(1-a)\big)(t-1)^2\Big]
+O_k(n^{-2}). 
\end{aligned}$$

The remainder is **uniform in every permutation** $g\in S_n$, and is bounded coefficientwise as a polynomial in $t$, with a constant depending only on fixed $k$. For $k=1$, $G_{n,g}(t)=1-a+at$ exactly.

**Proof.** Let $S$ be the fixed-vertex set, and put $Y=|E\cap S|$. This is hypergeometric, and

$$\mathbb E(1+u)^Y
=\sum_{j=0}^k\binom kj\frac{(x)_j}{(n)_j}u^j.$$

For fixed $j\le k$ and all integers $0\le x\le n$, the falling-factorial ratio has the uniform expansion

$$\frac{(x)_j}{(n)_j}
=a^j-\frac{\binom j2}{n}a^{j-1}(1-a)+O_k(n^{-2});$$

the apparent $a^{-1}$ singularity does not occur because $j\ge2$ in the correction. This follows by multiplying out the fixed-degree falling factorial polynomials and using $(n)_j=n^j(1-\binom j2/n+O_k(n^{-2}))$ for $n\ge2k$. Summing over $j$ gives

$$\mathbb E[t^Y]
=B(t)^k-\frac{k(k-1)}{2n}a(1-a)(t-1)^2B(t)^{k-2}
+O_k(n^{-2}). $$

Now $X-Y$ counts moved vertices $v\in E$ for which $g^{-1}(v)\in E$. In cycles of length at least three, the directed edges $g^{-1}v\to v$ give $L=n-x-2y$ *distinct unordered selected-pair events*, each of which adds **one** to $X-Y$. A transposition gives only one unordered pair event, but when selected, contributes **two** to $X-Y$. There are $y$ such events. Each individual pair is contained in $E$ with probability

$$\frac{k(k-1)}{n(n-1)}=\frac{k(k-1)}{n^2}+O_k(n^{-3}).$$

Distinct event edges form a graph of maximum vertex degree two. There are $O(n)$ pairs of event edges that share a vertex; selecting their three distinct endpoints has probability $O_k(n^{-3})$. There are $O(n^2)$ disjoint event-edge pairs; selecting their four endpoints has probability $O_k(n^{-4})$. Therefore the probability of **two or more distinct pair events** is $O_k(n^{-2})$, uniformly in $g$.

Conditioned on a particular selected pair, both its vertices are moved, and the remaining $k-2$ chosen vertices form a uniform $(k-2)$-subset of the other $n-2$ vertices. Their fixed-point count has generating polynomial $B(t)^{k-2}+O_k(n^{-1})$ coefficientwise, by the same finite hypergeometric approximation. Discarding the multiple-event configurations, whose contribution is coefficientwise $O_k(n^{-2})$, gives

$$\begin{aligned}
\mathbb E[t^X]-\mathbb E[t^Y]
={}&\frac{k(k-1)}{n}B(t)^{k-2}
\big[(1-a-2b)(t-1)+b(t^2-1)\big]\\
&+O_k(n^{-2})\\
={}&\frac{k(k-1)}{n}B(t)^{k-2}
\big[(1-a)(t-1)+b(t-1)^2\big]+O_k(n^{-2}). 
\end{aligned}$$

The coefficientwise estimates are legitimate because $k$ is fixed, $X\le k$, and any sum of selected-edge indicators on a $k$-set is bounded by $k$. Combining (132) and (133) proves (131). QED.

Every polynomial $P(a)$ of degree at most $k$ has a unique Bernstein representation

$$P(a)=\sum_{j=0}^k\beta_j\binom kj a^j(1-a)^{k-j}.$$

Define

$$\mathcal L_{n,g}(P)=
\sum_{j=0}^k\beta_j\frac{F_j^{(k)}(g)}{\binom nk}.$$

**Corollary 27 (universal first correction).** For each fixed $k\ge2$,

$$\mathcal L_{n,g}(P)=P(a)+\frac{J_P(a,b)}n+O_{k,P}(n^{-2}), $$

uniformly in $g$, where

$$\boxed{J_P(a,b)=(k-1)(1-a)P'(a)
+\left(b-\frac32a(1-a)\right)P''(a).} $$

**Proof.** Apply the coefficient functional $t^j\mapsto\beta_j$ to (131). The Bernstein differentiation identities give

$$\sum_j\beta_j[t^j]\big((t-1)^2B(t)^{k-2}\big)
=\frac{P''(a)}{k(k-1)}$$

and

$$\sum_j\beta_j[t^j]\big((t-1)B(t)^{k-2}\big)
=\frac{P'(a)}k-\frac{aP''(a)}{k(k-1)}.$$

The asserted expression (135) follows directly, retaining the uniform coefficientwise error. QED.


### 24.2. An explicitly corrected Chebyshev dual for every rank

For each integer $k\ge2$, let

$$H(a)=\frac{1-T_k(2a-1)}2,\qquad
a_j=\frac{1+\cos(j\pi/k)}2\quad(j=0,\ldots,k), $$

where $T_k$ is the first Chebyshev polynomial. Then

$$1=a_0>a_1>\cdots>a_k=0,\qquad
H(a_j)=\begin{cases}0,&j\text{ even},\\1,&j\text{ odd},\end{cases}
\qquad H'(1)=-k^2. $$

All interior nodes $a_1,\ldots,a_{k-1}$ are nondegenerate extrema: $H''(a_j)<0$ at odd $j$ and $H''(a_j)>0$ at even $j$. At the left endpoint,

$$H'(0)=(-1)^k k^2,\qquad
\operatorname{sgn}H''(0)=(-1)^{k+1} \quad(k\ge2). $$

Put $\rho=2k^2$. Let $J_H$ be the correction (135) with $P=H$. Prescribe

$$b_j=0\quad(1\le j<k),\qquad
b_k=\tfrac12,\qquad
\tau_j=\begin{cases}0,&j\text{ odd},\\\rho,&j\text{ even}.\end{cases} $$

There is a **unique polynomial $R$ of degree at most $k$** satisfying

$$R(1)=0,\qquad
R(a_j)=\tau_j-J_H(a_j,b_j)
\quad(1\le j\le k), $$

because these specify its values at $k+1$ distinct nodes. Define

$$J(a,b)=J_H(a,b)+R(a).$$

The first-correction contacts are therefore

$$J(a_j,0)=\tau_j\ (1\le j<k),\quad
J(0,\tfrac12)=\tau_k,\quad
J(1,0)=0,\quad
\partial_bJ(a,b)=H''(a). $$

Write the degree-$k$ Bernstein coefficients of $H,R$ as $\beta_0,\ldots,\beta_k$ and $\gamma_0,\ldots,\gamma_k$. Since $H(1)=R(1)=0$, one has $\beta_k=\gamma_k=0$. Define the **finite, explicit orbital dual function**

$$h_{n,k}(g)=\mathbf1_{\{g=e\}}
+\sum_{j=0}^{k-1}
\left(\beta_j+\frac{\gamma_j}{n}\right)
\frac{F_j^{(k)}(g)}{\binom nk}. $$

At the identity $h_{n,k}(e)=1$ **exactly**. By Corollary 27, for every nonidentity permutation, with $a=x(g)/n$, $b=y(g)/n$,

$$h_{n,k}(g)=H(a)+\frac{J(a,b)}n+O_k(n^{-2})$$

uniformly over the entire feasible region $0\le a\le1-2/n$, $0\le b\le(1-a)/2$.

**Lemma 28 (uniform corrected-dual bound).** For each fixed $k\ge2$, there is $D_k<\infty$ such that for all sufficiently large $n$ and all nonidentity $g\in S_n$,

$$\boxed{
\frac{\rho}{n}-\frac{D_k}{n^2}
\le h_{n,k}(g)\le
1+\frac{D_k}{n^2}.} $$

**Proof.** By (144), it suffices to prove the claim for $H(a)+J(a,b)/n$; the uniform remainder can be absorbed into $D_k$. We cover the compact feasible parameter region by neighborhoods of the finitely many extrema of $H$ and their complement. Every constant below may depend on fixed $k$, but not on $n,a,b$.

**Interior maxima.** For odd $1\le j<k$, choose a neighborhood of $a_j$ on which $H''<0$ and $H(a)\le1-c(a-a_j)^2$ for some $c>0$. By (142), $J(a,b)\le J(a,0)$ for $b\ge0$. Since $J(a_j,0)=0$, smoothness gives $J(a,0)\le M|a-a_j|$. Completing the square,

$$H(a)+J(a,b)/n
\le1-c(a-a_j)^2+\frac{M|a-a_j|}{n}
\le1+\frac{M^2}{4cn^2}.$$

The lower bound is automatic nearby because $H$ stays bounded above zero.

**Interior minima.** For even $1\le j<k$, choose a neighborhood on which $H''>0$ and $H(a)\ge c(a-a_j)^2$. Then $J(a,b)\ge J(a,0)\ge\rho-M|a-a_j|$, by (142) and the contact $J(a_j,0)=\rho$. Thus

$$H(a)+J(a,b)/n
\ge c(a-a_j)^2+\frac{\rho-M|a-a_j|}{n}
\ge\frac{\rho}{n}-\frac{M^2}{4cn^2}.$$

The upper bound is automatic because $H$ stays away from one.

**Endpoint $a=0$.** If $k$ is odd, $H(0)=1$, $H'(0)=-k^2$, $H''(0)>0$. Near zero, $J(a,b)\le J(a,(1-a)/2)$, because $b\le(1-a)/2$ and the slope in $b$ is positive. The latter function vanishes at $a=0$ by (142), so is at most $Ma$; meanwhile $H(a)\le1-ca$. Hence the upper bound holds for large $n$, with the lower bound automatic.

If $k$ is even, $H(0)=0$, $H'(0)=k^2$, $H''(0)<0$. Then $J(a,b)\ge J(a,(1-a)/2)\ge\rho-Ma$ near zero. Since $H(a)\ge ca$, the lower bound holds for large $n$, while the upper bound is automatic.

**Endpoint $a=1$.** Here $H(1)=0$, $H'(1)=-k^2$, and $J(1,0)=0$. Put $s=1-a$, so $b\le s/2$, and choose $M$ large enough that for all sufficiently small $s\ge0$,

$$H(1-s)\ge k^2s-Ms^2,\qquad
J(1-s,b)\ge-Ms.$$

For nonidentity permutations $s\ge2/n$. Choose a fixed small neighborhood and then $n$ large enough that $f_n(s)=k^2s-Ms^2-Ms/n$ is **increasing** there. Thus

$$H(a)+J(a,b)/n\ge f_n(2/n)
=\frac{2k^2}{n}+O_k(n^{-2}).$$

The upper bound is automatic near this zero of $H$.

**Compact complement.** Away from all these finitely many nodes, continuity gives a constant $\eta>0$ with $\eta\le H(a)\le1-\eta$. The polynomial $J$ is bounded uniformly on the compact feasible triangle. Both desired inequalities hold with fixed slack for all large $n$.

Together these neighborhoods cover all $g\ne e$, proving (145). QED.

By Theorem 18, the sharp coefficient is no greater than the **oscillation** of any dual function consisting of the identity indicator plus a linear combination of orbital statistics. Since $h_{n,k}(e)=1$, (145) implies

$$\boxed{C_n^{(k)}\le1-\frac{2k^2}{n}+O_k(n^{-2}).} $$

The case $k=1$ is already given exactly by Theorem 15: $C_n^{(1)}=(n-2)/n$.


### 24.3. Matching exact positive probability measures

We now obtain the reverse inequality in (129), for **every sufficiently large $n$** and fixed $k$. Crucially, this constructs genuinely nonnegative probability measures whose subset-image marginals agree **exactly**, not just in an asymptotic expansion.

Let $a_0=1>a_1>\cdots>a_k=0$ be the nodes (136). For each $1\le j\le k$, choose an integer $x_j(n)$ with

$$|x_j(n)-na_j|\le1.$$

Let $g_{j,n}\in S_n$ have exactly $x_j(n)$ fixed vertices and one additional cycle of length $n-x_j(n)$. Because $k$ is fixed and every $a_j<1$, for sufficiently large $n$ all these long cycles have length at least $k+1$. The $k$ cycle types are mutually distinct, nonidentity and not transpositions. Let $I_n$ denote the identity, and $T_n$ a transposition.

Define the **rational orbital vector** in $k$ coordinates

$$V_n(g)=
\left(
\frac{F_0^{(k)}(g)}{\binom nk},\ldots,
\frac{F_{k-1}^{(k)}(g)}{\binom nk}
\right). $$

Thus $V_n(I_n)=0$. Form the $k\times k$ matrix $D_n$ with columns

$$D_{n,j}=
\begin{cases}
V_n(g_{j,n})-V_n(I_n),&j\text{ odd},\\
V_n(T_n)-V_n(g_{j,n}),&j\text{ even},
\end{cases}
\quad(1\le j\le k), $$

and consider the **specified rational linear system**

$$D_n w_n=V_n(T_n)-V_n(I_n),\qquad
w_n=(w_{1,n},\ldots,w_{k,n})^T. $$

We prove that $D_n$ is invertible, that **all** weights $w_{j,n}$ are strictly positive, and that

$$\sum_{j\ \mathrm{odd}}w_{j,n}
=\frac{2k^2}{n}+O_k(n^{-2}) $$

for all sufficiently large $n$.

Write $B_j(a)=\binom kj a^j(1-a)^{k-j}$ and
$\mathbf B(a)=(B_0(a),\ldots,B_{k-1}(a))$. The uniform Bernstein approximation in Theorem 23, together with the rounding of $x_j(n)$, gives

$$V_n(g_{j,n})=\mathbf B(a_j)+O_k(n^{-1}).$$

The exact transposition count is

$$\Pr_{E\in\binom{[n]}k}(|E\cap T_n(E)|=k-1)
=\frac{2\binom{n-2}{k-1}}{\binom nk}
=\frac{2k(n-k)}{n(n-1)}
=\frac{2k}{n}+O_k(n^{-2}),$$

and every other changed-image orbital has probability zero. Equivalently,

$$V_n(T_n)-V_n(I_n)
=-\frac2n\mathbf B'(1)+O_k(n^{-2}). $$

The limiting matrix $D_\infty$ has columns $+\mathbf B(a_j)$ at odd $j$ and $-\mathbf B(a_j)$ at even $j$. It is invertible: every $B_i(a)$ with $0\le i<k$ contains the factor $(1-a)$. Dividing the evaluation matrix at the $k$ distinct points $a_1,\ldots,a_k<1$ by these nonzero row factors leaves an evaluation matrix for a basis of polynomials of degree at most $k-1$, which is invertible by the Vandermonde theorem. Therefore $D_n$ is invertible for all large $n$, and its inverses are uniformly bounded in $n$.

For each $j=0,\ldots,k$, let $\ell_j(a)$ be the degree-$k$ **Lagrange cardinal polynomial** for the nodes $a_0,\ldots,a_k$. Thus for every polynomial $P$ of degree at most $k$,

$$P'(1)=\sum_{j=0}^k\ell_j'(1)P(a_j). $$

For $j\ge1$ the sign of $\ell_j'(1)$ is $(-1)^j$: indeed

$$\ell_j'(1)=
\frac{\prod_{i\notin\{0,j\}}(1-a_i)}
{\prod_{i\ne j}(a_j-a_i)},$$

and exactly $j$ denominator factors are negative, since the nodes are strictly decreasing. Put

$$u_j=2|\ell_j'(1)|>0,\qquad1\le j\le k. $$

Applying (153) to $B_0,\ldots,B_{k-1}$, all of which vanish at $a_0=1$, shows that $u$ solves the **limiting** equation

$$D_\infty u=-2\mathbf B'(1).$$

Now $D_n=D_\infty+O_k(n^{-1})$ from (151) and $n[V_n(T_n)-V_n(I_n)]=-2\mathbf B'(1)+O_k(n^{-1})$ from (152). Uniform boundedness of $D_n^{-1}$ therefore gives

$$\boxed{
w_{j,n}=\frac{u_j}{n}+O_k(n^{-2})\quad(1\le j\le k).}$$

Since every $u_j>0$, this proves **strict positivity of the exact rational solution** $w_{j,n}$ for sufficiently large $n$.

Finally, the Chebyshev polynomial $H$ has $H(a_j)=1$ for odd $j$ and $0$ for even $j$, while $H(1)=0$. Applying (153) to $H$ and using $H'(1)=-k^2$,

$$\sum_{j\ \mathrm{odd}}u_j
=-2\sum_{j\ \mathrm{odd}}\ell_j'(1)
=-2H'(1)=2k^2. $$

Equation (150) follows.

Now define actual **central probability laws**

$$\begin{aligned}
P_n={}&
\left(1-\sum_{j\ \mathrm{odd}}w_{j,n}\right)U_{\{I_n\}}
+\sum_{j\ \mathrm{odd}}w_{j,n}U_{[g_{j,n}]},\\
Q_n={}&
\left(1-\sum_{j\ \mathrm{even}}w_{j,n}\right)U_{[T_n]}
+\sum_{j\ \mathrm{even}}w_{j,n}U_{[g_{j,n}]},
\end{aligned}$$

where $U_{[g]}$ is uniform probability on the conjugacy class of $g$. By (155), every coefficient is positive for sufficiently large $n$; the two supports are disjoint.

Equation (149) is **exact** and says that all $k$ orbital coordinates of $P_n$ and $Q_n$ match. The final orbital coordinate matches automatically because the $k+1$ normalized coordinates sum to one. Since the measures are conjugation-invariant, equality of all orbital moments is equivalent to equality of **every** $k$-subset one-point image marginal (Theorem 18).

For every sufficiently small rational $\delta>0$, the signed perturbation
$\nu_\delta=u_{S_n}+\delta(P_n-Q_n)$ is therefore a nonnegative probability measure with **exact uniform subset-image marginals**, total variation exactly $\delta$, and

$$\nu_\delta(I_n)-\frac1{n!}
=\delta P_n(I_n)
=\delta\left(1-\frac{2k^2}{n}+O_k(n^{-2})\right).$$

Consequently Theorem 18 supplies the reverse estimate

$$\boxed{C_n^{(k)}\ge1-\frac{2k^2}{n}+O_k(n^{-2}).} $$

Together with the matching dual bound (146), this proves Theorem 25 for every fixed $k\ge2$. For $k=1$, the already proved exact identity $C_n^{(1)}=(n-2)/n$ finishes the statement. **Theorem 25 is completely proved.** QED.

### 24.4. Exact four-subset example and the remaining finite-degree problem

In the first previously unresolved rank $k=4$,

$$H(a)=16a(1-a)(2a-1)^2,$$

and the interpolation system (140) yields the explicitly checkable **integer-coefficient correction**

$$R(a)=16(a-1)(200a^3-232a^2+63a-4). $$

Their degree-four Bernstein coefficient vectors are

$$(\beta_0,\ldots,\beta_4)=(0,4,-16/3,4,0),$$

$$(\gamma_0,\ldots,\gamma_4)=(64,-204,944/3,-108,0).$$

The published exact checker in code/check_k4_chebyshev_dual.py independently verifies the first-order orbital expansion, every Chebyshev contact, and the Bernstein coefficients using algebraic arithmetic in $\mathbb Q(\sqrt2)$; it additionally constructs **strictly positive rational primal weights** at several larger finite degrees and checks the moment equations exactly.

**Precisely what is now closed.** Equation (129) settles the sharp first-order asymptotic coefficient for **every fixed $k$**, not merely $k=1,2,3$, and proves the higher-rank conjecture previously stated in Section 23. It does **not** determine the individual exact value of $C_n^{(k)}$ for arbitrary finite $n,k$; nor does the qualitative proof specify a common explicit threshold in $n$ beyond which all primal weights are positive. Those stronger effective/finite problems remain open, and no novelty or external-peer-review claim is implied.


### 24.5. Explicit asymptotic masses at every Chebyshev node

The construction in (149)–(157) admits closed, positive leading weights, not merely an existence argument.

**Corollary 29 (universal Chebyshev–Lobatto mass formula).** In Theorem 25, define
$c_j=1$ for $1\le j<k$ and $c_k=2$. For the nodes
$a_j=(1+\cos(j\pi/k))/2$, the unique asymptotic solution to (149) has

$$\boxed{
w_{j,n}=\frac{1}{n}
\frac{4}{c_j(1-a_j)}+O_k(n^{-2})
=\frac1n\frac{8}{c_j[1-\cos(j\pi/k)]}
+O_k(n^{-2})
\quad(1\le j\le k).} $$

Consequently the constructed central primal measures satisfy

$$\boxed{
P_n(I_n)=1-\frac{2k^2}{n}+O_k(n^{-2}),\qquad
Q_n([T_n])=1-\frac{2(k^2-1)}{3n}+O_k(n^{-2}),}$$

where $Q_n([T_n])$ denotes the total mass of the transposition conjugacy class. In particular, $w_{k,n}=2/n+O_k(n^{-2})$ for every $k$, and the entire leading mass profile is **explicit**.

**Proof.** For Chebyshev–Lobatto nodes in decreasing order, the Lagrange barycentric weights are proportional to $(-1)^j/c_j$, with both endpoint denominators equal to $2$ and all interior denominators equal to $1$. The derivative formula for a Lagrange cardinal polynomial at $a_0=1$ is therefore

$$\ell_j'(1)=\frac{(-1)^j\,2}{c_j(1-a_j)},\qquad j\ge1.$$

Combining with (154)–(155) gives (161), including the endpoint mass $w_{k,n}=2/n+O_k(n^{-2})$.

The odd-weight identity is already (156). For the even weights, interpolation of the complementary polynomial $1-H$ gives

$$\sum_{\substack{j\ge2\\j\ \mathrm{even}}}\ell_j'(1)
=(1-H)'(1)-\ell_0'(1)=k^2-\ell_0'(1).$$

But
$\ell_0'(1)=\sum_{j=1}^k(1-a_j)^{-1}=(2k^2+1)/3$.
For completeness, the node polynomial for $a_1,\ldots,a_k$, under $t=2a-1$, is proportional to $(t+1)U_{k-1}(t)$, where $U_{k-1}$ is the Chebyshev polynomial of the second kind. Logarithmic differentiation at $t=1$, using $U_{k-1}(1)=k$ and $U_{k-1}'(1)=k(k^2-1)/3$, gives exactly
$\ell_0'(1)=1+2(k^2-1)/3=(2k^2+1)/3$.
Hence

$$\sum_{j\ \mathrm{even}}u_j
=2\left(k^2-\frac{2k^2+1}{3}\right)
=\frac{2(k^2-1)}3,$$

which, with (155), yields the second formula in (162). QED.

The weights in (161) are the *leading asymptotics* of strictly positive, **exactly rational** solutions of (149). They are not claimed to be the exact finite-$n$ weights at all $n$, and not every leading coefficient is rational.



## 25. An exact cycle-index and transfer-matrix compression theorem for every rank

The earlier rank-three compression theorem (Theorem 20) is a special case of a general exact identity. For **every** fixed subset size $k$, the full orbital vector of a permutation depends only on its cycle counts of lengths **at most $k$**. This observation is stronger than the first-order Bernstein approximation: it is an identity over integers for **every finite $n$** and provides an exact proof/certificate interface for higher-rank finite classifications.

Write $c_\ell(g)$ for the number of length-$\ell$ cycles of $g\in S_n$. Let $u,t$ be commuting formal variables and define the $2\times2$ transfer matrix

$$M(u,t)=\begin{pmatrix}1&u\\1&ut\end{pmatrix}. $$

Let $\lambda_+(u,t)\in\mathbb Q[t][[u]]$ be the unique formal-power-series root with constant coefficient $1$ of

$$\lambda^2-(1+ut)\lambda+u(t-1)=0.$$

Thus $\lambda_+=1+u+(t-1)u^2+\cdots$. Define the **complete rank-$k$ orbital polynomial**

$$\mathcal F_{n,k,g}(t)
=\sum_{j=0}^k F_j^{(k)}(g)t^j.$$

**Theorem 30 (exact all-rank cycle compression).** For every integer $1\le k\le n$,

$$\boxed{\displaystyle
\mathcal F_{n,k,g}(t)
=[u^k]\left\{
\lambda_+(u,t)^{\,n-\sum_{\ell=1}^k\ell c_\ell(g)}
\prod_{\ell=1}^k
\big(\operatorname{tr}M(u,t)^\ell\big)^{c_\ell(g)}
\right\}.} $$

Only the coefficients through $u^k$ of the formal power series are required. In particular, **if two permutations have the same $c_1,\ldots,c_k$, then all their $k$-subset orbital statistics agree exactly**:

$$c_\ell(g)=c_\ell(h)\ (1\le\ell\le k)
\quad\Longrightarrow\quad
F_j^{(k)}(g)=F_j^{(k)}(h)\ (0\le j\le k). $$

Furthermore, nonnegative integers $c_1,\ldots,c_k$ arise from a permutation of $n$ points if and only if

$$r=n-\sum_{\ell=1}^k\ell c_\ell\in\{0\}\cup\{k+1,k+2,\ldots\}. $$

Consequently the general orbital primal-dual program of Theorem 18 can be compressed **without any loss in optimality** to at most $O_k(n^k)$ short-cycle-count vectors, instead of enumerating every integer partition of $n$. Every feasible vector has a canonical representative of cycle type $1^{c_1}\cdots k^{c_k}r$ when $r\ge k+1$, or $1^{c_1}\cdots k^{c_k}$ when $r=0$.

**Proof.** Restrict $g$ to a cycle of length $\ell$, written as the cyclic vertex list $v_1,\ldots,v_\ell$. Choosing a subset of its vertices is equivalent to choosing a cyclic binary word $\epsilon=(\epsilon_1,\ldots,\epsilon_\ell)$, where $\epsilon_i=1$ means $v_i$ is selected. Its contribution to the size of the selected set is $\sum_i\epsilon_i$; its contribution to $|E\cap g(E)|$ is $\sum_i\epsilon_i\epsilon_{i+1}$, indices taken cyclically.

For a transition from current binary state $r\in\{0,1\}$ to next state $s\in\{0,1\}$, the matrix entry $M_{rs}=u^s t^{rs}$ is exactly the weight for the next selected vertex and an adjacent selected pair. Consequently the partition function of the cycle is

$$Z_\ell(u,t)
=\sum_{\epsilon\in\{0,1\}^\ell}
u^{\sum_i\epsilon_i}t^{\sum_i\epsilon_i\epsilon_{i+1}}
=\operatorname{tr}M(u,t)^\ell.$$

Different permutation cycles contribute independently to the combinatorial subset generating function. Therefore the following identity is **exact** before truncation:

$$\sum_{E\subseteq[n]}u^{|E|}t^{|E\cap g(E)|}
=\prod_{\ell=1}^nZ_\ell(u,t)^{c_\ell(g)}.$$

The determinant and trace of $M$ are $u(t-1)$ and $1+ut$. Thus its characteristic roots are precisely $\lambda_+$ from (164) and a second formal root $\lambda_-=u(t-1)/\lambda_+$, satisfying $\lambda_-\in u\mathbb Q[t][[u]]$. Cayley–Hamilton, or the standard two-root trace recurrence, gives

$$Z_\ell=\lambda_+^\ell+\lambda_-^\ell.$$

If $\ell>k$, the polynomial/series $\lambda_-^\ell$ is divisible by $u^{\ell}$ and hence by $u^{k+1}$. Therefore in the quotient ring modulo $u^{k+1}$,

$$Z_\ell\equiv\lambda_+^\ell\quad(\ell>k).$$

Replace every factor corresponding to a long cycle in (168) by $\lambda_+^\ell$ modulo $u^{k+1}$, multiply, and extract the coefficient of $u^k$. This proves (165).

The dependence on $c_1,\ldots,c_k$ and their total contribution to $n$ is now explicit, proving (166). All remaining cycles have lengths at least $k+1$, so their sum is either zero or at least $k+1$. Conversely any such remainder $r$ is realized by one $r$-cycle, proving (167).

For the LP compression, Theorem 18 permits primal measures invariant under conjugation and dual functions in the orbital-count span. By (166), both their marginal constraints and their dual objective values are constant on any aggregate of conjugacy classes with the same short-cycle counts; all such types are realized by the canonical representatives. Aggregating class masses preserves feasibility and the identity atom, so the sharp LP optimum does not change. The number of nonnegative integer short-cycle vectors is at most $\prod_{\ell=1}^k(1+\lfloor n/\ell\rfloor)=O_k(n^k)$. QED.

**Effective exact arithmetic.** This theorem is directly implementable without symbolic eigensolvers. The trace polynomials satisfy

$$Z_0=2,\quad Z_1=1+ut,\quad
Z_\ell=(1+ut)Z_{\ell-1}-u(t-1)Z_{\ell-2}, $$

while coefficients $\lambda_+=\sum_{m\ge0}A_m(t)u^m$, $A_0=1$, satisfy the integer-polynomial recurrence

$$A_m=tA_{m-1}
-\sum_{i=1}^{m-1}A_iA_{m-i}
-\mathbf1_{\{m=1\}}(t-1)\quad(m\ge1).$$

Truncating every polynomial multiplication at $u^{k+1}$ yields (165) using **integer arithmetic only**.

The independent public checker
code/check_all_k_orbital_compression.py
implements both recurrences using sparse integer dictionaries. It crosschecks the coefficients against an unrelated, direct $k$-subset enumeration on one representative of **every integer partition** for $3\le n\le12$ and every $1\le k\le\min(n,6)$. This finite check is supplementary; the transfer-matrix argument proves (165) for **all** $n,k$.

**Next finite classification frontier.** Theorem 30 gives a rigorous compression layer for the exact $k=4$ primal-dual problem, while Theorem 25 has already resolved its sharp asymptotic coefficient $32$. It does not itself give the complete exact finite-$n$ optimum at $k=4$, which remains a separate classification problem.



## 26. Complete exact four-subset atom-modulus classification for $4\le n\le64$

The fixed-rank asymptotic theorem has a substantial finite counterpart in the first previously unresolved rank $k=4$. Here the exact optimal coefficient can be determined for **every $4\le n\le64$**, without using numerical optimization as proof.

**Theorem 31 (complete degree-64 four-subset spectrum).** Let $C_n^{(4)}$ be the sharp marginal-preserving atom/TV coefficient for $S_n$ acting on $\binom{[n]}4$. The exact values for all degrees $4\le n\le64$ are determined by the following disjoint exhaustive cases:

- $n=4$: $C_4^{(4)}=1$, because the action is trivial.
- $n=5$: $C_5^{(4)}=3/5$, by complementation and Theorem 15 for singleton actions.
- $n=6$: $C_6^{(4)}=2/5$, by complementation and the exact two-subset law of Theorem 17.
- $n=7$: $C_7^{(4)}=5/14$, by complementation and the exact three-subset certificate in Theorem 19.
- Every $8\le n\le64$: the exact rational optimum is the value labelled $C$ for that degree in the **fixed public certificate file**
  $$  \texttt{certificates/four\_subset\_n8\_64.json}. $$

This includes full exact **attainment**: for each listed degree there is a genuine nonnegative probability measure with all four-subset image marginals uniform and a singleton atom defect exactly $C_n^{(4)}$ times its total variation. Illustrative coefficients are:

| $n$ | Exact $C_n^{(4)}$ | $n$ | Exact $C_n^{(4)}$ |
|---:|:---|---:|:---|
|8|5/14|16|3591/9187|
|9|5/14|20|4147/9871|
|10|5/14|30|17347/34965|
|11|1629/4549|40|25257571/45082011|
|12|131/357|50|297240803/486850773|
|14|3106/8153|60|261072773/400563233|
|15|1345/3493|64|6491170033/9749353873|

No all-degree exact formula is implied by this bounded, albeit complete, classification.

### 26.1. Independent exact orbital formulas and full finite search space

For $g\in S_n$, let $x,y,z,w$ be its numbers of cycles of sizes $1,2,3,4$, respectively. Put $N=\binom n4$, and define binomial orbital moments

$$M_j(g)=\sum_{E\in\binom{[n]}4}
\binom{|E\cap g(E)|}{j},\qquad0\le j\le4.$$

One may compute these without transfer matrices:

$$\begin{aligned}
M_0&=N,\\
M_1&=x\binom{n-1}{3}+(n-x)\binom{n-2}{2}.
\end{aligned}$$

Introduce the exact pair-pattern counts

$$\begin{aligned}
c_{22}&=\binom x2+y,\\
c_{21}&=x(n-x)+(n-x-2y),\\
c_{20}&=\binom n2-c_{21}-c_{22}.
\end{aligned}$$

For a pair of image-intersection witnesses, the union of the two vertices and their preimages has size $4,3,2$ according as there are $0,1,2$ internal directed predecessor edges. Therefore

$$M_2=c_{20}+(n-3)c_{21}+\binom{n-2}{2}c_{22}. $$

For a triple witness, three internal predecessor edges mean a union of invariant cycles of total length three; two edges mean exactly one path-component or two fixed vertices plus one moved vertex. Directly classifying these cases gives

$$\begin{aligned}
c_{33}&=\binom x3+xy+z,\\
c_{32}&=\binom x2(n-x)+x(n-x-2y)
+y(n-2-x)+(n-x-2y-3z),\\
M_3&=c_{32}+(n-3)c_{33}.
\end{aligned}$$

Finally, an invariant four-subset is a union of cycles with total length four, hence

$$M_4=\binom x4+\binom x2y+\binom y2+xz+w. $$

Binomial inversion gives all five desired orbital counts:

$$\boxed{\displaystyle
F_j^{(4)}(g)=\sum_{i=j}^4(-1)^{i-j}\binom ij M_i(g),
\qquad0\le j\le4.} $$

Equations (172)–(176) are **integer identities for every permutation** and provide a second derivation independent of the transfer matrix (165). By Theorem 30, the entire class type relevant to these orbitals is represented by

$$(x,y,z,w,r),\quad
r=n-x-2y-3z-4w\in\{0\}\cup\{5,6,\ldots\}. $$

Every such type is realized by the permutation with cycles $1^x2^y3^z4^w$ and, if $r>0$, one additional $r$-cycle. Conversely every permutation maps to one of these types. Thus verifying (176) and a dual inequality over every tuple (177) is **exhaustive over all $S_n$**.

### 26.2. Fixed rational primal-dual certificate proof

For each $8\le n\le64$, (171) contains two positive rational probability measures $P_n,Q_n$ specified by central conjugacy-class weights and a four-component rational dual vector $\lambda_n$, together with two exact rational dual extrema $\ell_n,u_n$ and the claimed optimum $C_n$.

The **separate independent verifier**
$$\texttt{code/check\_four\_subset\_n8\_64.py} $$
establishes all of the following as exact integer/rational equalities and inequalities:

1. Both central measures are nonnegative, normalized and **disjointly supported**, with the identity in $P_n$ and not in $Q_n$.
2. All five orbital moments agree:
   $$   \mathbb E_{P_n}F_j^{(4)}
   =\mathbb E_{Q_n}F_j^{(4)}\quad(0\le j\le4).$$
   Since the orbital relations are exactly the five possible subset-intersection sizes, this implies equality of every individual image marginal.
3. The exact central dual function
   $$   h_n(g)=\mathbf1_{\{g=e\}}-
          \sum_{j=0}^3\lambda_{n,j}F_j^{(4)}(g)$$
   obeys $\ell_n\le h_n(g)\le u_n$ for **every** feasible type (177); no class is omitted. All denominators are cleared before the exhaustive integer comparisons.
4. Every $P_n$-support class attains $u_n$, every $Q_n$-support class attains $\ell_n$, and
   $$   u_n-\ell_n=P_n(e)-Q_n(e)=C_n. $$
5. The size of each canonical conjugacy class is computed exactly and used to exhibit $\delta>0$ such that $u_{S_n}+\delta(P_n-Q_n)$ remains a nonnegative probability measure. Because the supports are disjoint, this measure has total variation $\delta$, and its identity atom increases by exactly $\delta C_n$.

Theorem 18 gives the universal upper bound $C_n^{(4)}\le u_n-\ell_n$, while this attaining perturbation proves the reverse inequality. Thus the checker gives a **complete finite exact proof** for each of its 57 degrees, conditional only on the mathematical orbital reduction and on replaying the publicly displayed finite integer procedure.

The independent checker calls **no optimizer, floating-point routine, SymPy package or certificate generator**. Its complete published replay checks every feasible compressed conjugacy type for every $8\le n\le64$, totaling **440,670 types**, and returned:

$$\texttt{EXACT k4 FRACTIONAL OPTIMALITY CERTIFIED: 57 DEGREES,
440670 TYPES}.$$

The finite class supports were discovered with numerical linear programming and **reconstructed using exact rational arithmetic before freezing**; that discovery process is not a proof premise. The checker reads only the fixed JSON, recomputes all mathematical constraints independently, and never calls the discovery program. Together with the complement cases $4\le n\le7$, this establishes Theorem 31. QED.

**Scope.** This classification is exact but finite. Theorem 25 separately establishes the **all-degree sharp first-order asymptotic**
$
C_n^{(4)}=1-32/n+O(n^{-2})
$.
No exact closed formula for every $n\ge65$, no globally optimal finite-degree structural classification, and no external human peer review is claimed.
