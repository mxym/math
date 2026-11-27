# Quantitative limits of modular ideal clearing at a bad conductor prime

Ideal clearing makes an ideal quotient look like the underlying ring quotient by multiplication with a generator. For a nonmaximal order at a prime dividing its index, such a generator need not exist. Can a mixture of multiplication maps, all using the same hidden multipliers within a batch, nevertheless produce the desired uniform labels? For the scalar-conductor family below we determine the *minimum* total-variation error over every such mixture, even with auxiliary multipliers.

This compares synthetic additive label distributions with no secret, ciphertext, error sample, or concrete scheme. It bounds one proposed form of model substitution, not arbitrary reductions.

## Local order and reduction to a matrix model

Let $B$ be the integer ring of an unramified extension of $\mathbb Q_p$ of degree $n\ge2$, let $S=\mathbb Z_p+p^cB$ with $c\ge1$, and consider the full $S$-ideal $I=p^c B$ inside $S$. Scaling by $p^{-c}$ identifies $I$ with $B$ as an $S$-module. The prime $p$ divides the index $[B:S]=p^{c(n-1)}$. For $b\ge1$, choose $r$ multipliers in $I$ with an arbitrary joint law, independently of the inputs. For each of $m$ outputs use an independent uniform $r$-tuple from $S/p^b S$ and form their linear combination with those same multipliers, reduced in $I/p^b I$. The target is $m$ independent uniform labels in $I/p^b I$. Assume $1\le r<n$; at $r=n$ exact uniformity is obtained by a $\mathbb Z_p$-basis of $B$ after scaling.

Put $d=\min(b,c)$ and $A=\mathbb Z/p^d\mathbb Z$. Projection of each source coefficient into $B/p^dB$ lands in the scalar copy of $A$ and is uniform there, since the map from $S/p^bS$ onto this copy is an additive surjection. After scaling $I$ and choosing an additive basis of $B$, the projected batches have the form

$$
Y=TU,\qquad
T\in A^{n\times r}\text{ arbitrary and hidden},\quad
U\text{ uniform in }A^{r\times m}.
\tag{1}
$$

The same $T$ is used for every column. The projected target is uniform on $A^{n\times m}$. Projection therefore gives a lower bound on the original optimization. The lower bound is attainable: choose $T$ with its columns a basis of a uniformly chosen free rank-$r$ direct summand of $A^n$, and lift those basis elements to $B$. Each lift is primitive modulo $p$, hence a unit in $B$ by unramifiedness. If $b>d$, then $d=c$ and any one such multiplier gives all of $p^cB$ when its source coefficient ranges over the conductor part of $S$. Thus the conditional image in $B/p^bB$ is exactly the full preimage of the chosen summand in $B/p^dB$, and is conditionally uniform there. The target is also uniform on each fiber. In the case $b=d$ there are no further digits. In either case the optimum reduces exactly to (1).

## The optimal mixture and its likelihood

For a matrix $Y$, let $H(Y)\subset A^n$ be its column image. Its cyclic summand lengths are $\ell_1\ge\dots\ge\ell_k>0$, where a summand of length $\ell$ is isomorphic to $\mathbb Z/p^\ell\mathbb Z$. The zero image has $k=0$. Write $ {n\brack r}_p$ for the Gaussian binomial coefficient. Let $Q$ be uniform on $A^{n\times m}$, and let $P_*$ be the distribution obtained by choosing a uniformly random free rank-$r$ direct summand and, conditionally, choosing all $m$ columns uniformly and independently within it. Then

$$
\inf_{\mathcal L(T)}d_{\rm TV}(\mathcal L(TU),Q)=d_{\rm TV}(P_*,Q).
\tag{2}
$$

As a function of the image lengths the likelihood ratio is

$$
L(H(Y))=\frac{P_*(Y)}{Q(Y)}
 =
\begin{cases}
p^{(n-r)(dm-\sum_{i=1}^k(\ell_i-1))}
 \displaystyle\frac{{n-k\brack r-k}_p}{{n\brack r}_p},& k\le r,\\[5pt]
0,& k>r .
\end{cases}
\tag{3}
$$

Thus (2) is evaluable by summing $Q(H\text{ of specified type})\,(L(H)-1)_+$ over the types; a closed count is given below.

**Optimality.** The likelihood is proportional to the number of free rank-$r$ summands containing $H$. Smith normal form puts the image of every given type into coordinate form with generators $p^{d-\ell_i}e_i$. Two types ordered componentwise by lengths (padding with zeros) can be represented by nested submodules. Consequently the event $C=\{Y:L(H(Y))>1\}$ is monotone towards smaller lengths. For fixed $U$ and $T$, $H(TU)$ is a quotient of the column image of $U$: the map is the restriction of $T$ to that image. A quotient cannot increase any of its lengths. Indeed for each $j$, its dimension of $p^{j-1}H/p^jH$ over $\mathbb F_p$ cannot increase under a surjection, and these dimensions count cyclic lengths at least $j$. In contrast, when $T$ is a split injection all the lengths are unchanged. Coupling by the same $U$ proves $\Pr(TU\in C)\ge P_*(C)$. Hence the distance of any mixture from $Q$ is at least $P_*(C)-Q(C)$, which equals $d_{\rm TV}(P_*,Q)$ by definition of $C$. This argument covers every multiplier shape.

**Counting the likelihood.** For an image in Smith form, any containing summand must reduce modulo $p$ to a subspace containing $e_1,\ldots,e_k$: in its free quotient, $p^{d-\ell_i} e_i=0$ forces the class of $e_i$ to be divisible by $p^{\ell_i}$, hence to vanish modulo $p$. The number of such $r$-planes modulo $p$ is $ {n-k\brack r-k}_p$. For each one, choose a fixed lift containing all the $e_i$, with a fixed free complement. Other lifts are graphs of matrices from that lift to the complement with entries in $pA$. The $i$-th column for $i\le k$ must be divisible by $p^{\ell_i}$, and all other columns are arbitrary in $pA$. The number of containing summands is

$$
{n-k\brack r-k}_p\,p^{(n-r)((d-1)r-\sum_{i=1}^k(\ell_i-1))}.
$$

For $k=0$ this is the total number of $r$-summands, denoted $N_{n,r}(d)$. Each selected summand gives mass $p^{-drm}$ to each tuple of columns therein. Dividing by $Q(Y)=p^{-dnm}$ gives (3).

## Exact type count and consequences

Write $k_j=\#\{i:\ell_i\ge j\}$ for $1\le j\le d$ and $k_{d+1}=0$. The number of submodules of this type in $A^n$ is

$$
B_{n,d}(\ell)=
 \prod_{j=1}^d p^{(n-k_j)k_{j+1}}
                     {n-k_{j+1}\brack k_j-k_{j+1}}_p .
$$

For completeness, in counting $H$ fix $J=pH$ first, as a submodule of $(\mathbb Z/p^{d-1})^n$ with truncated lengths. The socle $H[p]$ is a $k_1$-dimensional subspace of $A^n[p]$ containing $J[p]$ of dimension $k_2$, giving the binomial at $j=1$. Fix cyclic generators of $J$. Each admits a lift under multiplication by $p$; its lift has $p^{n-k_1}$ possibilities modulo $H[p]$. Any choices give precisely one $H$: adjoin these lifts to $H[p]$. A relation on the generators of $J$ lifts only into $J[p]\subset H[p]$ (multiply each lifted generator by the order of its image), so the resulting socle is exactly $H[p]$. Conversely two lifts of a fixed generator in the same $H$ differ by its socle. This proves the recurrence, with the field case as base.

A uniformly chosen $m$-tuple in such an $H$ generates it with probability $\prod_{i=0}^{k_1-1}(1-p^{i-m})$ when $m\ge k_1$, by reducing to $H/pH$ and lifting generation over the finite local ring. Thus its total type probability under the reference law is

$$
Q(\ell)=
p^{-dnm} B_{n,d}(\ell)\,
                         p^{m\sum_i\ell_i}\prod_{i=0}^{k_1-1}(1-p^{i-m}),
$$

with zero probability if $m<k_1$. This and (3) give the finite optimum.

- **One label.** For $m=1$, $L<1$ on primitive vectors and $L\ge1$ on nonprimitive vectors (including zero). For a nonzero vector of length $\ell$, insert $k=1$ in (3) and use $ {n-1\brack r-1}_p/{n\brack r}_p=(p^r-1)/(p^n-1)$. At $\ell=d$ the ratio is below 1; dropping $\ell$ by one multiplies it by $p^{n-r}\ge2$, enough to reach 1. The optimum TV is therefore the excess probability of reduction to zero modulo $p$, exactly $p^{-r}-p^{-n}$.
- **More labels than multipliers.** If $m\ge r+1$, the optimal law dominates $Q$ on its support, and the optimum TV is exactly $1-Q(k_1\le r)$. Indeed every supported matrix belongs to at least one free $r$-summand, and $N_{n,r}(d)\le p^{(dr+1)(n-r)}\le p^{dm(n-r)}$. For the first inequality use the Gaussian binomial formula with $n-r$ factors, each denominator factor at least $1-1/p\ge1/p$. Thus even the smallest possible positive likelihood is at least 1. For fixed $p,d,r,m$ with $m>r$, the reference support mass has sharp asymptotic as $n\to\infty$:
  $$
  Q(k_1\le r)=
  (1+o(1))\,\frac{\prod_{i=0}^{r-1}(1-p^{i-m})}
                    {\prod_{j=1}^r(1-p^{-j})}\,p^{-d(n-r)(m-r)} .
  $$
  The free type of rank $r$ gives this mass by the count. Other finitely many types have $\sum\ell_i\le dr-1$, and $B_{n,d}(\ell)$ grows like a constant times $p^{n\sum\ell_i}$ by the leading powers in each Gaussian binomial. Hence those types are negligible relative to the free one.
- **At most as many labels as multipliers.** For fixed $p,d,r,m$ with $m\le r$ and $n\to\infty$, the optimum TV tends to $1-\prod_{i=0}^{m-1}(1-p^{i-r})$. Under $Q$ the $m$ columns form a basis of a free rank-$m$ summand with probability tending to 1. Under $P_*$ the same event is precisely that the $r\times m$ coefficient matrix is full column rank modulo $p$. Given this event, both laws are uniform on the same orbit, by the action of $\operatorname{GL}_n(A)$ on such matrices. The remaining $Q$ mass tends to zero, proving the limit.

In particular, hiding and randomizing a single multiplier can greatly improve its *one-label* marginal compared with a fixed multiplier, without making a batch close to independent uniform labels.

## Primary source comparison and limits

[Jutla–Lin, Enhancing Ring-LWE Hardness using Dedekind Index Theorem](https://eprint.iacr.asia/2022/1631.pdf) extend ideal clearing to orders at primes outside the index and give explicit multi-generator examples. They also give an ideal-clearing method removing the known-factorization qualification for the original maximal-order statement. This note does not claim a new removal of that qualification. It works at an *excluded* conductor prime and measures the exact distance from an additional, restricted uniform-label model that keeps the same hidden multipliers throughout a batch.

[Byrne–Horlemann–Khathuria–Weger, Proposition 3](https://arxiv.org/abs/2106.09403) gives the classical type counts used here. [Nóbrega–Feng–Silva–Uchôa-Filho](https://arxiv.org/abs/1311.4861) study multiplicative matrix channels and Smith shapes for other objectives. The scoped conclusion is optimality in (2) for uniform-input labels with a shared left multiplier and total-variation error, and its realization in this scalar-conductor model. It does not analyze noisy samples, changing multipliers between outputs, nonlinear transformations or different reductions. The good-prime theorem in the source is unchanged.

The verifier exhausts small matrix ensembles and confirms that the single monotone-event certificate works for every fixed multiplier in those ensembles. It does not process cryptographic instances.
