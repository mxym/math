# Finite even-tree extremality via grandbranch rearrangement

Write $E_n$ for the rooted binary tree with $n$ leaves obtained recursively by joining $E_{\lfloor n/2\rfloor}$ and $E_{\lceil n/2\rceil}$, with $E_1$ a leaf. A copy of $E_k$ means a $k$-subset of leaves inducing that unlabeled rooted shape, after suppressing unary vertices. Let $A(n,k)$ be the number of such copies in $E_n$. Set $A(n,0)=1$ and $A(n,k)=0$ for $n<k$. We say order $k$ is extremal if **for every $n\ge k$** no rooted binary tree with $n$ leaves has more than $A(n,k)$ copies of $E_k$.

**Theorem.** For all integers $n\ge k\ge1$, the finite even tree $E_n$ maximizes the number of leaf-induced copies of $E_k$ among all $n$-leaf rooted binary trees. Moreover $A(n,k)$ has nonnegative two-by-two minors when the host sizes and pattern sizes are both listed in increasing order. No uniqueness or higher-arity statement is asserted.

This addresses the binary finite Conjecture 1 of Czabarka–Székely–Wagner. The limiting inducibilities were already known for all $k$. Coronado–Mir–Rosselló–Valiente already proved the finite $k=4$ case, with uniqueness, by comparing grandbranch exchanges. The proof below uses the three- and four-occupied grandbranch counts and a quantitative induction for finite balanced-host ratios. The limiting two-pattern question of Brosch–Puges is not the finite statement here.

## 1. Balanced-host counts and a growth bracket

There is a deletion $E_s\to E_{s-1}$ for every $s\ge2$: if a root side is larger, recurse there, and otherwise recurse in either side (for $s=2$, suppress the root). In particular $A(s,j)>0$ whenever $s\ge j$ and $A(s,j)$ is nondecreasing in $s$. For $j=1,2,3$ the count in any tree is $\binom{s}{j}$. To count larger even shapes put $l=\lfloor s/2\rfloor$, $h=s-l$, $a=\lfloor j/2\rfloor$, $b=j-a$. Then
$$ A(s,j)=A(l,j)+A(h,j)+A(l,a)A(h,b)+\mathbf1_{a\ne b} A(l,b)A(h,a). \tag{1} $$
Indeed, copies wholly in a branch retain their shapes; a spanning copy induces $E_j$ just when the child counts split as $a,b$ and each child induces the prescribed even shape. The same rule with the corresponding child counts holds at the root of every binary tree.

Suppose the even hosts are extremal for order $j$ at host sizes $s-1,s$. With $s\ge j$ and $s\ge2$, put $P_j(s)=1-A(s-1,j)/A(s,j)$. Then
$$ \frac{j}{s-1+j}\le P_j(s)\le\frac js. \tag{2} $$
For the upper bound, delete a uniformly random leaf of $E_s$. The expected surviving count is $(1-j/s)A(s,j)$ and is at most the extremal count $A(s-1,j)$. For the lower bound duplicate a uniformly random leaf of $E_{s-1}$ by replacing it with a cherry. All old copies survive if the first new leaf is used as the old label. In addition, for each old copy containing the chosen leaf, substituting the second new leaf yields a distinct extra copy. Thus the mean is at least $(1+j/(s-1))A(s-1,j)$ and is at most $A(s,j)$. This argument never assumes that the random duplication itself gives a balanced host.

For $0<a<b$ set
$$ M_s(a,b)=A(s-1,a)A(s,b)-A(s-1,b)A(s,a). $$
The sign is nonnegative by support alone for $s\le b$. Above this range, (2) for $b$ and $a$ shows that $M_s(a,b)\ge0$ whenever
$$ s(b-a)\ge a(b-1), \tag{3} $$
provided the smaller-size extremality hypotheses used in (2) hold. Indeed $b/(s-1+b)\ge a/s$. If the adjacent minors are nonnegative through $y$, then for any $0\le x\le y$,
$$ A(x,a)A(y,b)-A(x,b)A(y,a)\ge0. \tag{4} $$
For $x\ge a$ this follows by the nondecreasing ratio $A(\cdot,b)/A(\cdot,a)$; for $x<a$ it is zero. For $a=0$ the same statement follows directly from monotonicity in host size. For equal ranks the determinant is zero.

## 2. A four-grandbranch exchange

Take a host whose two root children are even. Their capacities can be sorted so that $x_1\le x_2\le x_3\le x_4$ are the capacities of their four grandchildren, with the original pairing $12|34$ if the root child capacities differ by at least two. This follows from $x_2-x_1, x_4-x_3\in\{0,1\}$. A child of size one is represented by the pair of capacities $0,1$; a virtual empty tree is suppressed on joining. If the root child capacities already differ by at most one, the host is $E_n$ and no exchange is necessary. Otherwise replace the pairing $12|34$ by $14|23$, retaining the very same even grandbranches.

Write $f_i(t)=A(x_i,t)$. We compare copies of $E_k$, $k\ge4$. When at most two grandbranches receive sampled leaves, the induced tree is invariant under the new pairing. When at least three are occupied, the induced root uses both root children, hence must have a balanced split. Within each occupied grandbranch the sampled leaves must induce their own even shape. Thus each admissible assignment of the four occupancies $(t_i)$ contributes exactly $\prod_i f_i(t_i)$: there are no multinomial factors for unlabeled subsets of disjoint leaf sets.

* With three occupied grandbranches let $d$ be the size in the branch paired to the empty branch. Necessarily $d\in\{\lfloor k/2\rfloor,\lceil k/2\rceil\}$, and the other two positive counts are $b=\lfloor(k-d)/2\rfloor$, $c=\lceil(k-d)/2\rceil$; $0<b\le c\le d$. Mark $0,d$ as outer and $b,c$ as middle. A pairing counts exactly the assignments that pair the two outer slots to each other and the two middle slots to each other. This remains right when $d$ equals a middle rank: the positive outer slot is specified uniquely by the mate of the zero. For convenience distinguish both middle labels, and divide all resulting sums by $2$ when $b=c$.

  Group the indices into columns $I=(1,3)$ and $J=(2,4)$, each listed with nondecreasing capacity. If either column receives two outer or two middle labels, neither pairing works. Otherwise fix an outer label $u$ and a middle label $v$ in $I$; let $U,V$ be the remaining outer and middle labels in $J$. Sum over their possible positions within the columns. The contribution for new minus old then factors as
$$
 [f_1(u)f_3(v)-f_1(v)f_3(u)]
 [f_2(V)f_4(U)-f_2(U)f_4(V)] . \tag{5}
$$
  If $u=0$, $U=d$ and both factors are nonnegative by (4) for rank pairs $(0,v)$ and $(V,d)$. If $u=d$, both factors are nonpositive. Thus (5) is nonnegative provided (4) holds for $(b,d)$ and $(c,d)$ whenever distinct. Sum over admissible $d$ without repeating the same value when $k$ is even. Each valid three-slot assignment in a given pairing determines its own $d$.

* With four occupied grandbranches write $k=4t+j$, $0\le j\le3$. The multiset consists of $4-j$ copies of $t$ and $j$ copies of $t+1$. If $j=0,1,3$ all pairings work. If $j=2$, each pair must be mixed. Assigning two low or two high ranks to the same column makes both pairings mixed. When both columns have one rank of each kind, summing over their positions gives new minus old equal to
$$
 [f_1(t)f_3(t+1)-f_1(t+1)f_3(t)]
 [f_2(t)f_4(t+1)-f_2(t+1)f_4(t)]\ge0. \tag{6}
$$
  This uses (4) only for $(t,t+1)$.

After the exchange the root child sizes $x_1+x_4$ and $x_2+x_3$ differ by at most one: their signed difference is $(x_4-x_3)-(x_2-x_1)$. It is not claimed that the new children are themselves even. They will be replaced using induction.

## 3. Proving all the required minors

We use one induction on the **host size** $N$. In addition to extremality at $N$ for every pattern order, our induction conclusions are, for $1\le j<N$,
$$
 \Delta_j(N):=P_{j+1}(N)-P_j(N)\ge0,\qquad
 \Delta_j(N)\ge\frac{1}{16Nj^2}\quad\text{if }N\ge2j-1. \tag{7}
$$
Thus, once (7) has been established up to a given host size, **all** rank pairs in (4) are available through that host size. Indeed the $P_j(s)$ are nondecreasing across ranks $1,\ldots,s$, so $P_b(s)\ge P_a(s)$ for $a<b\le s$, equivalent to $M_s(a,b)\ge0$. Other ranks follow by support or the rank-zero convention, and (4) follows by multiplying ratios. This step does not require a quantitative bound for non-adjacent ranks.

### 3.1 The order of induction

The case $N=1$ is immediate. Suppose both conclusions are known for every smaller host. In an arbitrary $N$-leaf host first replace the two root children by even trees of the same sizes. This cannot decrease the target count, by (1) with the counts in the actual children and the joint smaller-host hypothesis. If the root is not balanced, perform the exchange of §2; all its factors compare grandbranch capacities strictly smaller than $N$, so (4) is already available. Replace the two new children by even trees, again without decreasing the count. The new root was balanced by the exchange, so this yields $E_N$. This proves extremality at $N$ for all $k$ before any step establishing (7) at $N$. Patterns of size at most three are already shape-independent, and those of size above $N$ have zero copies. In particular the proof may now use (2) up to and including $N$.

If $N\ge2j^2$, the bounds (2) directly give
$$
 \Delta_j(N)\ge \frac{j+1}{N+j}-\frac{j}{N}
 =\frac{N-j^2}{N(N+j)}\ge \frac{1}{4N}.
 \tag{8}
$$
When $j<128$ and $j<N<2j^2$ we use only balanced-tree arithmetic from (1), with no hypothesis on other hosts. For each such pair [fullcert.py](fullcert.py) checks
$$
 m=A(N-1,j)A(N,j+1)-A(N-1,j+1)A(N,j)\ge 0.
$$
If $N\ge2j-1$ it checks also $16Nj^2m\ge A(N,j)A(N,j+1)$. Each check is precisely (7) after clearing its positive denominators. The program performs 1,373,505 sign checks and 1,365,630 quantitative checks; the largest tested population is 32,257. Reproducible [output](FULL-CHECKS.txt). It remains to handle $j\ge128$ and $j<N<2j^2$.

### 3.2 Canonical-leaf inclusion conditional on a root-spanning copy

Write $h=\lceil N/2\rceil$, $l=N-h$. In $E_N$ mark a leaf in the side of size $h$ by recursively taking a deletable leaf from the larger side (either side if equal). Its individual deletion gives $E_{N-1}$, so for a uniform copy of $E_i$ in $E_N$ its inclusion probability is exactly $P_i(N)$. Conditional on that copy spanning the root, write the inclusion probability as $B_i$. Set $a=\lfloor j/2\rfloor$. The possible adjacent pair $j,j+1$ uses one of the two consecutive gaps in the list
$$ B_{2a}=P_a(h),\quad
 B_{2a+1}=(1-w)P_a(h)+wP_{a+1}(h),\quad
 B_{2a+2}=P_{a+1}(h). \tag{9} $$
Only the indices at most $N$ that are actually used are needed. To see this, the root-spanning allocations are the two balanced child occupancies. Given these, the selections within the children are independent and uniform over copies in those children. The larger side gets $a+1$ in the odd case with probability
$$
 w=\frac{A(h,a+1)A(l,a)}
 {A(h,a+1)A(l,a)+A(h,a)A(l,a+1)}.
$$
Our range always has $h\ge a+1$, $l\ge a$, and the denominator is positive; an impossible split has weight zero.

For $N<2j-1$ neither order $j$ nor $j+1$ fits entirely within a child. Hence $P_i(N)=B_i$ for these two indices. Both differences in (9) are nonnegative by the smaller-host induction at $h$, proving all that (7) requires here.

For $N\ge2j-1$ we have $h\ge j\ge2a$, $a\ge64$. Both split allocations are possible. If $h=l$, $w=1/2$. Otherwise $l=h-1$. By the smaller-host adjacent minor comparing capacities $h-1,h$ and ranks $a,a+1$, we have $w/(1-w)\ge1$. By the deletion (upper) bound in (2), and by monotonicity of $A(\cdot,a)$, we have
$$
 \frac{w}{1-w}=
 \frac{A(h,a+1)}{A(h-1,a+1)}
 \frac{A(h-1,a)}{A(h,a)}
 \le\frac{h}{h-a-1}\le3.
$$
Thus $w,1-w\ge1/4$. Applying the quantitative part of (7) at the smaller host $h$ (which is at least $2a$), (9) gives
$$ B_{j+1}-B_j\ge \tfrac14\Delta_a(h)
 \ge\frac{1}{64h a^2}
 \ge \frac{N/h}{16Nj^2}\ge\frac{3}{2}\frac1{16Nj^2}, \tag{10} $$
since $j\ge2a$ and $N/h\ge3/2$.

### 3.3 Bounding non-spanning copies without losing the gap

Let $\eta_i$ be the probability that a uniform copy of $E_i$ in $E_N$ lies entirely in one root child. It is zero if $i>h$. Otherwise monotonicity and repeated use of the duplication (lower) bound in (2), valid by the extremality already established, give
$$
 \eta_i=\frac{A(l,i)+A(h,i)}{A(N,i)}
 \le2\prod_{s=h+1}^N\frac{s-1}{s-1+i}
 \le2\exp\!\left(-\frac{i\lfloor N/2\rfloor}{N-1+i}\right)
 \le2e^{-i/4}. \tag{11}
$$
The last step uses $i\le h\le(N+1)/2$ and $N\ge3$. The actual inclusion probability is a mixture of $B_i$ and a number in $[0,1]$ with mixing weight $\eta_i$, hence $|P_i(N)-B_i|\le\eta_i$. For $j\ge128$, $N<2j^2$,
$$
 \eta_j+\eta_{j+1}\le4e^{-j/4}\le \frac1{64j^4}
 \le \frac1{32Nj^2}. \tag{12}
$$
Indeed $e^{x/4}/x^4$ is increasing for $x>16$, and $e^{32}>2^{40}>256\cdot128^4$ (use $e>5/2$ and $(5/2)^4>32$). Subtracting (12) from (10) proves both conclusions in (7). The induction is complete.

This is a finite exact-arithmetic argument for *unbounded* $n,k$: the finite base covers only the explicitly stated small-column exceptions in the balanced-host ratio lemma. No finite enumeration of arbitrary tree shapes is substituted for the proof; a sign or quantitative failure in the base checker raises an error, including in optimized Python.
