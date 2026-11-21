# Two retained primes: center count and corank bound

Let $N$ be even and $p_1,\ldots,p_k$ be the labels of a [Bożek exceptional autonomous component](https://arxiv.org/abs/1909.09900). Orient edges from $p_i$ to factors of $N-p_i$. Then $A_{ij}=v_{p_j}(N-p_i)$ is irreducible and loopless, all row sums are at least two, and each complementary factorization is entirely on these labels.

Call a set of labels *retained* if each row uses at most one factor outside the set, counting multiplicity. The labels at most $\sqrt N$ form such a set. There are at least two: the complement of the smallest label is composite, does not contain that label, and has a factor at most its square root.

**Count.** For fixed $K\ge2$, at most $O_K(Y(1+\log X)^{2K+1})$ centers $N\le X$ carry a component on at most $K$ labels with a retained pair of which at least one label is at most $Y$. In particular, the count is $X^{1/2+o(1)}$ for components with exactly two labels at most $\sqrt N$, even for $K=o(\log X/\log\log X)$ and without assuming that $A$ or $I-A$ is invertible. For a prescribed prime in the retained pair and fixed $K$, the count is polylogarithmic. These estimates count centers carrying components, not the Goldbach exceptional set.

**Rank.** For a retained set of size $s$, $\operatorname{corank}_{\mathbb Q}(I-A)\le s-1$. Thus corank at least two requires at least three labels at most $\sqrt N$.

## Exact elimination with two retained primes

Order the pair as $x,y$, with the bounded label first. Fix the ordered exponent signature and write $L$ for the other labels, with prime column $p_L$. Each row has the form $p_i+b_i+r_i p_L=N$. A row with no outside factor has $r_i=0$ and $b_i$ a monomial of degree at least two in $x,y$. Otherwise $b_i=0$, and $r_i$ has a single nonzero entry, a monomial of positive degree in $x,y$. This uses the term “factor” with multiplicity and the compositeness of the complements.

The outside rows give $(I+T)p_L=N\mathbf1-b$. Put $D=\det(I+T)$ and $M=\operatorname{adj}(I+T)$. For empty $L$, take $D=1$ and vector products over $L$ to be zero. The graph of $T$ has at most one outgoing edge at each vertex and no loops. The determinant expands as the product of $1-(-1)^\ell H$ over its disjoint cycles, where $\ell$ is the length and $H$ the product of the monomial entries. At positive prime inputs $H>1$, so $D\ne0$. Substitution into the retained rows gives
$$
R_i N=V_i,\qquad R_i=D-r_iM\mathbf1,\qquad V_i=D(p_i+b_i)-r_iMb.
$$
Each $R_i$ has constant term 1; each $V_i$ has zero constant term and linear part $p_i$. Thus the polynomial $P=V_1R_2-V_2R_1$ starts with $x-y$, with integer coefficients. In particular $P(x,0)\equiv x\pmod{x^2}$, so specialization at any integer $x\ge2$ leaves a nonzero polynomial in $y$. Its degree is $O(k(1+\log X))$, since each exponent row sum is at most $\log X/\log3$.

At a physical tuple, either retained row yields a nonzero coefficient $R_i$. Follow the unique outside-target path from that row, if there is one. When it terminates, the terminal prime has coefficient 1 of $N$ in its affine expression. Going backwards transforms the coefficient $a$ to $1-ha$ for an integer $h\ge3$, so it remains integral and nonzero. When the path enters a cycle, every row along the path and cycle has $b_i=0$. Solving the cycle and retracing gives the homogeneous expression $p_i=(R_i/D)N$. At a physical tuple this coefficient equals $p_i/N>0$. Once $N$ is known, the invertible outside block determines all remaining labels.

For each $k$ there are at most $[(k-1)(1+\lfloor\log X/\log3\rfloor)^2]^k$ signatures: choose the outside target or its absence and the two retained exponents separately on each row. Sum the degree bound over these signatures and at most $Y$ possible integers $x$. The signature-and-degree factor is $X^{o(1)}$ throughout the stated growing-$K$ range.

## Rank with any retained set

For $Aw=w$, each outside row either determines $w_i$ from retained coordinates or expresses it as $w_j+h_i\cdot w_S$ for the unique outside target $j$, with a nonzero nonnegative vector $h_i$ of retained exponents. If there is an outside cycle, summing its equations gives the nonzero relation $(\sum_{\rm cycle}h_i)\cdot w_S=0$. In addition, every outside cycle can be reached from a retained vertex by a path with no later retained vertex: use strong connectivity and take the last retained vertex on such a path. The equation at the starting vertex fixes the coordinate of its sole outside successor from $w_S$. The recurrence then fixes a vertex of the cycle, hence the entire cycle. All other outside coordinates follow by reaching a sink or an already determined cycle. Thus restriction to $w_S$ is injective, and the relation gives the bound.

If there are no outside cycles, substitution gives $w_S=K_0w_S$ for a nonnegative $K_0$ whose row sums are all at least two. Indeed each original factor contributes its exponent times a retained unit coordinate or a nonnegative substituted expression of row sum at least one; all paths terminate in expressions involving retained labels. Then $I-K_0\ne0$ and restriction is again injective.

## Scope and replay

Run the companion replay with `python -O check_eac_two_retained.py`. It checks the genuine component at 2200, exact elimination with three retained labels and a genuine rank-one kernel at 128, and an integer outside-cycle fixture that is **not** a prime component.

The [invertible-A count](EACJacobianSquareRoot.md), [invertible-I-minus-A count](EACNonsingularSquareRoot.md) and [five-label count](EACFiveSquareRoot.md) use different hypotheses. This result requires sparse outside factors instead of any invertibility assumption, and works with larger cardinality. It is distinct from the [one-label-above-53 criterion](EACOneLarge.md). It gives no bound on the cardinality or retained size of a component forced by a hypothetical Goldbach failure.

Literature checked through 2026-11-21: [Kelanemer, Aug 12; revised Sep 6](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7274460) analyzes the adjacent exponent-matrix setting. The full text was not accessible in this check; no priority or nonoverlap claim is made about it. [Nelson, Nov 16 v2](https://arxiv.org/abs/2611.14580) concerns additive prime-sum relations instead.
