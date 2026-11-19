# Alternating words uniquely maximize binary three-insertion input entropy

Yongxian Zhang. Research draft. All logarithms are base two unless written ln.

**Theorem.** For a uniformly distributed binary input to the exact three-insertion channel of Ma–Zhang, the length-$n$ received words maximizing the posterior Shannon entropy of the shorter input are precisely the two alternating words, for every $n\ge7$. This is the **second assertion** of [Ma–Zhang, Conjecture 6.2](https://arxiv.org/html/2611.01064v1). It does not establish the three-deletion assertion. The maximal value and the smaller-length exceptions are already in their Corollary 5.2 and Proposition 6.1.

## 1. Masks and the target

Fix the host (received word) $y$ of length $n$. Choose a uniform three-element subset $S$ of its sites and delete those sites, leaving the length-$n-3$ word $X$. This has exactly the posterior distribution in question (Ma–Zhang Lemma 2.1): all masks are equally likely, so a word with $k$ embeddings has probability $k/\binom n3$. Set $f(k)=k\log k$, with $f(0)=0$. If $C(y)=\sum_x f(e(x,y))$, then
\[
C(y)=\binom n3 H(S\mid X),\qquad H(X)=\log\binom n3-C(y)/\binom n3.
\]
Write $m=n-2$ (thus the shorter input has length $m-1$, **not** $m$). An alternating host has $m$ outputs of multiplicity $m$ and all other positive multiplicities one, so the target cost is $m f(m)$.

Here are the alternating-word facts we use (Ma–Zhang Theorem 5.1). For a host of length $a$ and zero or one deletions, all positive multiplicities are one. With two deletions, a single output, the alternating word of length $a-2$ with the same initial phase, has $a-1$ masks, the adjacent pairs; all other positive multiplicities are one. With three deletions and $a\ge3$, the following $a-2$ distinct words have $a-2$ masks apiece: shorten the host by two while preserving phase, then delete one site. All remaining outputs have multiplicity one. The statements about zero-length words use their unique empty word. To see the counts, in the infinite alternating word the earliest positions spelling an output are obtained greedily. Any other embedding adds nonnegative multiples of two to the leading and internal gaps. With two or three deletions the number of such embeddings is either one or (shorter length plus one), corresponding to zero or one units of free gap. Shortening by two and then possibly erasing one position produces exactly the cases with such a unit. The choices of the last single erasure in an alternating string are distinct. Expressions below at length one or two automatically give zero three-erasure cost.

## 2. Two compatible accounting devices

Partition $y$ into its maximal constant runs and, separately, its maximal alternating segments. With $D$ equal adjacent bonds the latter lengths are $l_1,\ldots,l_b$, $b=D+1$. Write $K,T$ for the respective count vectors of the sites of $S$ in those two partitions. The bipartite incidence graph has the two block families as vertices and one edge per site. It is a tree: starting at the first edge, each next site enters a new run or a new alternating segment, and stays in the other block. On a tree its vertex sums determine any choice of zero-one edge labels, by leaf stripping. Thus $(K,T)$ determines $S$. Since $X$ is already determined by $K$,
\[
H(S\mid X)=H(S\mid X,T)+H(T\mid X)
\ge H(S\mid X,T)+H(T\mid X,K)=H(S\mid X,T)+H(S\mid K).
\]

Given $T$, the surviving segment lengths are fixed and the segmentwise masks independent uniform; the local outputs can be read separately from $X$. Multiplying their contributions by $\binom n3$ and using the alternating-word facts gives the sum of
\[
B_n(l)=(n-l)f((l-1)_+)+(l-2)_+ f((l-2)_+).
\]
Indeed, two deletions in one segment give $n-l$ choices for the outside deletion, and three inside give its own three-deletion cost.

Given $K$, the choices within any run of length $r$ containing $k$ deleted sites have uncertainty $\log\binom rk\ge 2k(r-k)/r$. For $0<k\le r/2$, use $\binom rk\ge(r/k)^k$ factor by factor and $-\log u\ge 2(1-u)$ for $0<u\le1/2$ (equality at one half, check derivative). Use symmetry at larger $k$. The expected $k(r-k)$ counts ordered deleted/retained pairs within the run, so after multiplying by $\binom n3$ it equals $r(r-1)\binom{n-2}2$. Summing over the runs, $\sum(r-1)=D$, proves
\[
\boxed{C(y)\ge Dm(m-1)+\sum_{j=1}^b B_n(l_j).} \tag{1}
\]

## 3. At least two equal bonds

For $x=(l-2)_+$, $B_n(l)\ge m f(x)$ (use $f(l-1)\ge f(l-2)$ when $l\ge2$ and the fact that $n-l+l-2=m$). Also $\sum_j x_j\ge m-2D$. Put $c=\log e$, so $4/3<c<3/2$ by strict midpoint/trapezoid bounds on $\int_1^2 dt/t$. By the tangent line for the convex extension of $f$ at $t=m/b$, whose derivative $\log t+c$ is positive since $b\le m+2$ and $m\ge5$,
\[
\sum_j f(x_j)\ge m\log(m/b)-2D(\log(m/b)+c).
\]
For $D\ge2$, $\log(D+1)/D\le(\log3)/2<4/5$ (the quotient decreases, and $3^5<2^8$). Thus by (1)
\[
[C(y)-m f(m)]/m\ge D[m/5-1-2\log m-2c].
\]
At $m=128$ the bracket is positive, and thereafter its derivative $1/5-2c/m$ is positive. Section 5 supplies the finite range $n=7,\ldots,129$.

## 4. A single equal bond: the critical family

Let $y$ be formed from the alternating word $w$ of length $n-1=m+1$ by duplicating the letter at its position $p$. Write $L=p-1, R=m+1-p$ for the lengths flanking the two copies, so $L+R=m$. If $\min(L,R)\le1$, the longer alternating segment of $y$ has length at least $m$. Formula (1) gives $C(y)\ge m(m-1)+m f(m-2)$. For $m\ge16$, $f(m)-f(m-2)\le2(\log m+c)<m-1$ (strict at 16 and derivative comparison thereafter). The finite boundary cases are in Section 5.

Suppose $L,R\ge2$. Separate masks retaining **both**, **one**, or **neither** of the copies. The one-copy masks can be obtained in pairs from two-site deletions in $w$ which do not delete $p$, choosing which copy to keep. There are $m(m-1)$ such masks. Each contributes at least one bit to the total cost, since its partner has the same output. We improve this baseline on specific disjoint outputs.

The alternating length-$m-1$ output with phase that of $w$ has $m$ adjacent-pair masks in $w$. Exactly $m-2$ of those avoid $p$, giving $2(m-2)$ one-copy masks in $y$; the two remaining pairs give two neither-copy masks, and both copies cannot be retained. Thus its multiplicity is $2m-2$.

For other large classes, first remove an adjacent pair from the **left flank**, keeping both copies, then erase one further site in either flank. After the pair is removed the resulting word $z_L$ equals $w$ with its site $p-1$ erased: its double consists of what were sites $p-2,p$ in $w$. This phase-preserving identity follows from alternation on each side. If the further erasure is on the shortened left flank, its $L-2$ sites give distinct outputs of both-copy multiplicity at least $L-2$ each, by the three-erasure alternating formula applied to that flank. If on the right flank, its $R$ sites give distinct outputs of both-copy multiplicity at least $L-1$ each by the two-erasure formula on the left. All $L-2+R$ outputs here are distinct: deleting two different single sites in $z_L$ gives the same output only if the entire interval between the sites is constant, and the erasures are outside its only doubled run. Each output retains a double and hence is **not** alternating. Each is therefore obtainable from $w$ by a *unique* two-site mask, with sites $\{p-1,j\}$ where $j$ is not one of the two sites comprising the retained double. In particular $j\ne p$, and exactly two one-copy masks of $y$ also produce this output. Interchange left and right to get a second family anchored at $p+1$.

The two families intersect in exactly one output: by uniqueness of the mask in $w$ the mask at the intersection must be $\{p-1,p+1\}$. In the left family it erases the first right-flank site of $z_L$; in the right family the last left-flank site of $z_R$. These two both-copy subfamilies have disjoint three-site masks (two erasures on the left versus two on the right); they give at least $(L-1)+(R-1)$ both-copy masks and in addition the same two one-copy masks. The following are consequently lower bounds on the indicated classes, **not** an upper-bound classification of all possible coincidences:

|number of distinct outputs|lower bound on multiplicity|
|---:|---:|
|$L-2$|$L$|
|$R-1$|$L+1$|
|$R-2$|$R$|
|$L-1$|$R+1$|
|$1$|$m$|

There are $2m-5$ outputs in the table. Each uses exactly two one-copy masks, and the earlier alternating output uses $2(m-2)$. The remaining one-copy masks still each contribute at least one bit. They number $m(m-1)-2(2m-5)-2(m-2)=m^2-7m+14$. Therefore
\[
\begin{aligned}
 C(y)\ge{}&m^2-7m+14+(L-2)f(L)+(R-1)f(L+1)\\
 &+(R-2)f(R)+(L-1)f(R+1)+f(m)+f(2m-2).
\end{aligned} \tag{2}
\]

By convexity $f(x+1)\ge f(x)+\log x+c$ and $f(L)+f(R)\ge m(\log m-1)$. As $L,R\ge2$, the two cross terms $(R-1)\log L+(L-1)\log R$ are at least $m-2$. The tangent at $2m$ gives $f(2m-2)\ge (2m-2)(\log m+1)-2c$. Substitution in (2) yields
\[
C(y)-m f(m)\ge m(c-1)-2\log m+10-4c.
\]
Using the tangent $\log m\le3+c(m-8)/8$ gives a lower bound $m(3c/4-1)+4-2c>0$.

## 5. Exact finite certificate and conclusion

For $7\le n\le129$ and $D\ge2$, exponentiate (1) in base two. Set $g_l=2^{B_n(l)}$, $U=2^{Dm(m-1)}$, $V=m^{m^2}$, all integers. If $U>V$, the case is done. Otherwise verify $g_l^2\le g_{l-1}g_{l+1}$ for every $2\le l<n$; this is an integer check for each of the finitely many lengths. A product of $b$ factors at positive indices with fixed sum $n$ is then minimized at balanced indices (transfer one from a larger index to a smaller whenever they differ by at least two). If even the balanced product times $U$ exceeds $V$, stop. Otherwise enumerate all ordered compositions into $D+1$ positive lengths. An ordered composition determines exactly one binary word starting in zero, and complement preserves all counts. For any composition still not strictly certified by (1), enumerate all three-site masks to compute the exact integer $\prod_x e(x,y)^{e(x,y)}$, and check strict comparison with $V$.

[verify.py](verify.py) implements these checks without floats, external libraries, or optimization-sensitive assertions. The run-only and balanced screens respectively certify 7,587 and 511 pairs $(n,D)$; another 1,972 ordered compositions are certified directly by (1). The remaining 343 words have $n\le25$ and pass exact mask enumeration. The same exact enumeration verifies the 22 boundary representatives $\min(L,R)\le1$ for $7\le n\le17$ (complement and reversal preserve counts). See [CHECKS.txt](CHECKS.txt).

All nonalternating words at all claimed lengths have strictly higher cost, finishing the proof. No conclusion on Rényi entropies or on posterior **supersequences** for the three-deletion channel follows from this comparison.
