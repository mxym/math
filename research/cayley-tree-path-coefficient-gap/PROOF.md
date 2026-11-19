# A macroscopic exponential gap above the path's independent-set coefficients

Let $T_n$ be a uniform labeled tree on $[n]$, and $i_k(T)$ the number of $k$-vertex independent subsets. For every $0<\varepsilon\le1/2$, there is $b_\varepsilon>0$ such that, except with probability at most $e^{-c n}$ for all sufficiently large $n$, simultaneously for every integer $\varepsilon n\le k\le\lceil n/2\rceil$,
$$i_k(T_n)\ge e^{b_\varepsilon n}\binom{n-k+1}{k}.\tag{1}$$
Here $c>0$ can be absolute. This is the fixed-positive-density, nonzero-baseline improvement asked about in Heilman's JGT Question 8.3. It is false with a fixed positive exponential gain for $k=o(n)$, and the displayed path benchmark vanishes for $k>\lceil n/2\rceil$. We do not estimate the best exponential gain.

## 1. A deterministic improvement with pendant claws

Let $T$ be any tree on $n>4$ vertices rooted at a vertex. Suppose $N$ proper descendant subtrees are rooted three-leaf stars: the root of each has exactly three children, all leaves. Since they have equal size, the selected subtrees are disjoint. Their roots each have a parent in the nonempty connected remainder (deleting whole pendant subtrees cannot disconnect what remains). For any $0\le L\le N$ choose $L$ of them. Then, interpreting impossible binomial choices as zero,
$$i_k(T)\ge \sum_{s=0}^L \binom{L}{s}\binom{n-k-s+1}{k-3s}.\tag{2}$$

To prove this, remove the chosen claws, condition on each independent subset of the remaining tree, and multiply the local independence polynomials of the slots. Let $x$ mark size. Replace each four-vertex claw by a four-vertex path with an endpoint attached via the original parent edge. **If its parent is absent**, the claw and path contribute, respectively, $1+4x+3x^2+x^3$ and $1+4x+3x^2$. **If its parent is present**, their roots are forbidden; they contribute $(1+x)^3$ and $1+3x+x^2$. In either parent state the claw polynomial is at least the corresponding path polynomial plus $x^3$, coefficient by coefficient.

Expand the product of these lower polynomials. For a chosen subset of $s$ slots where the extra term $x^3$ is taken, this monomial is independent of parent states; the other $L-s$ slots use the path. Summing over the core configurations gives exactly $x^{3s}$ times the independence polynomial of a tree on $n-4s$ vertices: delete those $s$ entire slots and replace the others with paths. The core is nonempty; repeated attachment parents cause no issue. Wingard's path minimality says that every $q$-vertex tree has at least $\binom{q-j+1}{j}$ independent $j$-sets. Applying this to each residual tree with $q=n-4s$, $j=k-3s$ proves (2). Equivalently, the Wingard inequality follows by leaf deletion: omit the leaf or include it and remove it together with its neighbor. For the latter forest, add edges to form a tree without increasing any coefficient, and apply induction plus the path recurrence, starting with orders 0, 1 and 2.

## 2. Positive density of slots with an exponential tail

Write $p=e^{-4}/6$. The exponential concentration of the pendant-claw count about $pn$ already follows from [McDiarmid, Theorem 1.1](https://doi.org/10.1016/j.ejc.2024.103994): a centered claw has four vertices and six automorphisms, labeled trees have generating-function radius $1/e$, and the class is closed under pendant attachment and detachment. Its undirected pendant count and the root-oriented fringe count differ by at most one for $n>8$: the four-vertex pendant sides are disjoint, and only the side containing label 1 may be missed. The conditioned Poisson tree fringe-frequency theorem also gives convergence in probability. Here is an independent elementary derivation of the needed exponential lower tail. Take independent parent pointers $P_i$ uniform in $[n]$ for $i\ne1$. On the event that all arrows reach 1, of probability $1/n$ by Cayley's formula, this is exactly a uniform labeled tree oriented to root 1. Off that event define the same slot count as follows: for a potential center $z\ne1$, its preimage $C_z=\{i:P_i=z\}$ must consist of three labels distinct from $z$, and each of those labels must have empty preimage. For $n>4$ this agrees with the proper fringe-slot count on the tree event. Self-loops or cycles outside a valid slot need not be excluded.

For a fixed $z\ne1$ and a specified triple in $[n]\setminus\{1,z\}$, three pointers must be $z$ and the other $n-4$ pointers must avoid the center and its three children. Thus the unrestricted expectation of the count is
$$
(n-1)\binom{n-2}{3}n^{-3}(1-4/n)^{n-4}=pn+o(n).
$$
Changing one pointer from $u$ to $v$ changes only $C_u,C_v$. Apart from $u,v$ themselves, a potential center can be affected only if $u$ or $v$ is its child before or after the change. There are at most four such old/new parents (a pointer at vertex 1 does not exist). Thus the count has bounded differences at most 6, including coincidences and cycles. McDiarmid gives $\Pr(N<pn/2)\le e^{-c_0 n}$ in the unrestricted model for all sufficiently large $n$. Conditioning costs a factor $n$, which can be absorbed by decreasing $c_0$ for large $n$. No independence between different claw occurrences is needed.

## 3. A uniform comparison of coefficients

Work on $N\ge pn/2$. Fix $\varepsilon$ and set $L=\min(N,\lfloor\varepsilon n/6\rfloor)$, so $L\ge n\min(p/2,\varepsilon/12)$ for all sufficiently large $n$. For each integer $\varepsilon n\le k\le\lceil n/2\rceil$ write $B_s=\binom{n-k-s+1}{k-3s}$. For $0\le s\le L$, $k-3s\ge\varepsilon n/2$ and $n-2k+2s+1\ge0$, so these are positive binomials, including at the odd upper endpoint. In particular $0\le k-3s\le\lceil(n-4s)/2\rceil$ as required. For $s<L$ cancellation gives
$$
\frac{B_{s+1}}{B_s}
=\frac{(k-3s)(k-3s-1)(k-3s-2)}
{(n-k-s+1)(n-2k+2s+2)(n-2k+2s+3)}.
$$
For sufficiently large $n$ the numerator's smallest factor is at least $\varepsilon n/3$. Each positive denominator factor is at most $n$ (use $k\ge 3s+\varepsilon n/2$). Therefore $B_s\ge B_0(\varepsilon^3/27)^s$. The binomial theorem in (2) proves (1) with
$$b_\varepsilon=\min(e^{-4}/12,\varepsilon/12)\log(1+\varepsilon^3/27)>0.$$
The event used is independent of $k$.

## 4. Precise interpretation and prior work

[Heilman, *Independent Sets of Random Trees and Sparse Random Graphs*](https://doi.org/10.1002/jgt.23225), published Lemma 7.3 and Question 8.3, considers an exponentially improved high-probability lower bound for a typical uniform labeled tree. It derives its lower bound from G. C. Wingard, *Properties and Applications of the Fibonacci Polynomial of a Graph*, Mississippi dissertation (1995), Theorem 5.1. The unnormalized exact path benchmark is $i_k(P_n)=\binom{n-k+1}{k}$; [Basit and Galvin, *On the independent set sequence of a tree*](https://academicweb.nd.edu/~dgalvin1/pdf/journal/random_trees_J.pdf) also explicitly use it. With $a=k/n\le1/2$, uniformly bounded away from 0, Stirling's estimate and Bedrosian's exact $\mathbb Ei_k=\binom nk(1-a)^{k-1}$ give
$$n^{-1}\log\!\left(i_k(P_n)/\mathbb E i_k(T_n)\right)
=(2-3a)\log(1-a)-(1-2a)\log(1-2a)+O(\log n/n),$$
with $0\log0=0$. Thus the improvement in (1) persists with a strictly positive exponent in the normalized exponential-scale form of Lemma 7.3; the odd endpoint $k=(n+1)/2$ is addressed by the exact unnormalized comparison rather than extending that logarithmic formula above $a=1/2$. A literal fixed-$k$ interpretation would be wrong: for **every** $k=o(n)$, $i_k(T)\le\binom nk=e^{o(n)}$ and the positive path count is at least one. No tree has a fixed positive exponential improvement there. Path minimality remains sharp deterministically.

[Csikvári, *On a Poset of Trees II*](https://doi.org/10.1002/jgt.21693) treats coefficient monotonicity under generalized tree shifts; this particular claw/path domination should not be promoted as a new instance of qualitative path minimality. [Janson](https://www2.math.uu.se/~svantejs/papers/sj264.pdf), Theorem 7.12(ii) and Example 10.2, already give the linear-frequency fringe input for uniform labeled trees. The existing exponential probability estimate also follows by the elementary parent-map argument in §2, in the spirit of [Heilman's endofunction work](https://arxiv.org/abs/2006.06724). There is also an elementary prior inference for sufficiently large densities: the classical typical maximum independent set has size $(\rho+o(1))n$, $\rho e^\rho=1$, so its subsets alone give a strict exponential gain over the path for each fixed $1-\rho<a\le1/2$. The claimed nontrivial coverage includes all smaller fixed positive densities, and simultaneous $k$; it is not a claim of the first gain at the endpoint or of an optimal exponent. Other results on the total count, **maximal** independent sets or maximum cardinality alone compare different statistics. The proof is independent of the location and Gaussian fluctuations of the mode (Question 8.2).

The script uses the independent-set recurrence to check (2) for all 20,299 unlabeled rooted shapes through order 13 (271,248 coefficient checks at orders 5–13). This is a finite test, not the proof of (1).
