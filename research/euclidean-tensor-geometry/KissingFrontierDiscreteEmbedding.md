# A discrete embedding of the entire 73/127-point kissing frontier

Take a hypothetical 73-point kissing code in dimension six containing 26 antipodal pairs, or a 127-point code in dimension seven containing 53 antipodal pairs. These are the [largest possible pair counts presently allowed here](KissingNineteenPointEnergy.md). Every other point may be arbitrary; **no root system is prescribed**.

Choose a unit representative $u_i$ on each of the $p$ marked axes. Represent **each** code point $x$ by the integer column
\[
 L(x)_i=\operatorname{round}(2u_i\cdot x)\qquad (1\le i\le p).
\]
Use symmetric tie choices for the marked Gram matrix and opposite choices on the two signs of a marked axis, so $L(-u_i)=-L(u_i)$. Other ties may be settled either way.

| Original case | Integer labels | Rank of the matrix of **all** labels | Squared distance between distinct labels |
|---|---|---:|---:|
| 73 points, 26 marked axes in $\mathbb R^6$ | 73 distinct in $\mathbb Z^{26}$ | **at most 11** | at least 1 |
| 127 points, 53 marked axes in $\mathbb R^7$ | 127 distinct in $\mathbb Z^{53}$ | **at most 12** | **at least 6** |

The 21 unmarked labels are ternary: all their entries belong to $\{-1,0,1\}$. A marked column has just one exceptional entry $\pm2$. Moreover, the symmetric marked block has at least **six or seven positive eigenvalues**, respectively. Thus, *if* that block has rank equal to the ambient dimension, it is a positive semidefinite root Gram matrix: 26 of the lines must lie in a rounded $D_6$ or $E_6$ frame, or all 53 in a rounded $E_7$ frame. This is an assertion about the **integer labels**, not an identification of the original real code with a root system.

This strengthens the [angular stability theorem](KissingFrontierAngularStability.md) in two ways: it encodes all points, not just the antipodes, and lowers even the marked block's rank upper bounds from 12/13 to 11/12. It does not establish that such a counterexample exists or is impossible.

## 1. Controlling all projection errors together

Let $U$ and $V$ have the $p$ marked representatives and the 21 unmarked vectors as columns. Set $\gamma=10/21$, $\theta=2\gamma$, $\mu=(p+10)/n$, $c=6/(n+4)-1/4$, and $e=\|UU^T+\gamma VV^T-\mu I\|_F$. Write $G=2U^TU$, $A=2U^TV$ and let $H,K$ respectively be their integer roundings. The [weighted deficit proof](KissingFrontierAngularStability.md#1-a-weighted-deficit-estimate) and the pointwise inequality $t^2(1/4-t^2)\ge(3/16)\min(|t|,1/2-|t|)^2$ give
\[
 \|G-H\|_F^2+\theta\|A-K\|_F^2\le \frac{64}{3}(\Delta-ce^2),\qquad
 \Delta=\tfrac{100}{21}U_{21,n}-\tfrac{15}{2}.
\]
Here $U_{21,n}$ bounds the diagonal-included ordered energy per unmarked point for $f(t)=t^4-t^2/4$. Use the existing six-dimensional chart unchanged. In dimension seven use the same positive rational Gram factors as before, with the sharper pair slack $1/400000$ and the original triple slack $1/150000$. The [energy and arithmetic verifier](verify-kissing-frontier-discrete-embedding.js) rechecks both charts; the new seven-dimensional bound, also reproduced with independent closed-form Gegenbauer expansion and reversed-coordinate Bernstein subdivision, is $23807257697230457/15000000000000000$. Thus $D=(64/3)\Delta$ is less than $47/50$ or $31/25$, respectively.

### Hemispherical second-moment lemma

For any unit vector $v$, divide the unmarked points by the sign of their projection onto $v$. A group of $k$ contributes to $\sum_j(v\cdot y_j)^2$ at most
\[
 b_n(k)=
 \begin{cases}
 0&k=0,\\
 (k+1)/2&1\le k\le n,\\
 (k+\sqrt{(k-2)^2+8n})/4&k>n.
 \end{cases}
\]
To prove this, reverse an entire group if needed, so $w_i=v\cdot y_i\ge0$, and let $T=\sum w_i^2$. Write $C=(y_i\cdot y_j)$, $W=\operatorname{diag}(w_i)$, $Q=(I+\mathbf1\mathbf1^T)/2$. The symmetric matrix $F=W(Q-C)W$ has trace zero and nonnegative entries. The sum of its entries bounds its nuclear norm, which is twice the sum of its positive eigenvalues. If $k>n$, a $(k-n)$-dimensional subspace of $\ker(WCW)$ sees the positive form $WQW\succeq W^2/2$. Thus the sum of entries of $F$ is at least the sum of the $k-n$ smallest $w_i^2$ (use the minimum trace on subspaces of that dimension). Now
\[
 T^2\le\Big\|\sum_i w_i y_i\Big\|^2
 \le\tfrac12\big(T+(\sum_iw_i)^2\big)-\sum_{\text{smallest }k-n}w_i^2,
\]
with the last term absent for $k\le n$. Divide the right hand side by $T$ and take its largest Rayleigh quotient. When $k>n$ the maximizing eigenvalue is that of the two-block matrix with diagonal $(n+1)/2,(k-n-1)/2$ and off-diagonal $\sqrt{n(k-n)}/2$. The case $T=0$ is immediate.

The maximum of $b_n(k)+b_n(21-k)$ for $0\le k\le21$ is below $B=10.94$ in dimension six or $B=11.036$ in dimension seven, as checked by rational square-root enclosures. Hence $UU^T\succeq(\mu-\gamma B-e)I$. In particular $H$ has at least $n$ positive eigenvalues, by the eigenvalue perturbation bound and
\[
 2e+\|G-H\|_F \le \sqrt{\Delta(4/c+64/3)} < 2(\mu-\gamma B).
\]
The positive semidefinite rank-$n$ corollary now follows from the ADE counts for integral norm-two systems: in rank six only $D_6,E_6$ can contain 26 axes; in rank seven only $E_7$ can contain 53.

### Integer separation

Distinct unit code points obey $\|x-x'\|\ge1$. Except for opposite signs of the *same* marked axis, their two rounding errors involve distinct columns of $G$ or $A$, so their difference has norm bounded by $\sqrt{64(\Delta-ce^2)/(3\gamma)}$ by weighted Cauchy–Schwarz. The same bound works when comparing one nonzero code point with the zero vector and its zero label. Meanwhile $\|2U^T(x-x')\|\ge2\sqrt{\mu-\gamma B-e}$. For $m=0$ in dimension six and $m=5$ in dimension seven, the verifier establishes
\[
 2\sqrt{\mu-\gamma B-e} >
 \sqrt m + \sqrt{\tfrac{64}{3\gamma}(\Delta-ce^2)}
 \quad (0\le e\le\sqrt{\Delta/c}).
\]
It partitions $[0,1]$ into 4,096 rational intervals, using the lower bound for the left side at the right endpoint and the upper bound for the right side at the left endpoint; the infeasible tail is skipped. Opposite marked labels already differ by four in one coordinate. Consequently all labels are nonzero, they are distinct, and the integer squared distances give the claimed bounds.

## 2. How many rounded axes can lie in a low-dimensional flat?

For $0\le j\le7$ the following are valid upper bounds for the number of original marked columns of $H$ in a subspace of dimension $j$:
\[
  (m_0,\ldots,m_7)=(0,1,3,6,12,20,36,63).
\]
Indeed their principal block then has rank at most $j$, diagonal 2, and other entries $0,\pm1$. The Euclidean bounds are the usual ADE maxima. Indefinite blocks cannot exceed them: the [separate exact finite census](verify-signed-gram-flats-through-seven.js) gives the **sharp** maximum sizes for each nonzero negative index below (a dash means the signature is impossible).

| Rank | 1 negative direction | 2 negative | 3 negative | Nonsingular basis orbits by negative index starting at 0 |
|---:|---:|---:|---:|---|
| 4 | 5 | – | – | 11, 4 |
| 5 | 10 | 5 | – | 30, 52, 1 |
| 6 | 18 | 10 | 6 | 112, 888, 90, 1 |
| 7 | 32 | 18 | 10 | 469, 24,750, 14,660, 60 |

There are no higher negative indices or indefinite examples in lower ranks. The enumeration uses the standard [star-complement extension principle for signed graphs](https://doi.org/10.1515/spma-2022-0161) in Gram form: select a nonsingular principal basis $B$ of size $j$. Its other columns have restriction $w\in\{-1,0,1\}^j$ up to sign; keep precisely $w^TB^{-1}w=2$. Two candidates can coexist precisely when $w^TB^{-1}w'\in\{-1,0,1\}$. A maximum clique plus the original basis gives the largest possible block for this $B$; its inertia is unchanged by the extensions. Conversely each such clique realizes its full Gram block. A symmetric rank-$j$ matrix has a nonsingular principal basis, e.g. by an inertia factorization $XJX^T$.

All signed basis patterns, including singular ones at intermediate extension steps, are generated by adding one vertex, and identified only by permutations and sign switching. Independently Burnside's formula for signed permutations on the edge positions gives 2, 5, 18, 100, 1,242 and 43,425 basis-pattern orbits, in ranks 2 through 7. On each edge orbit with negative accumulated sign only entry zero is fixed; with positive sign there are three choices. Characteristic coefficients and adjugates are integral; the number of negative eigenvalues is the number of sign changes in $\det(tI+B)$, ignoring zeros, since all roots are real. The verifier checks each extremizer's norm and pairwise products. The finite table is about integer Gram systems, **not** the unrestricted spherical kissing numbers.

## 3. Counting integer minors after appending the unmarked columns

Let $h=\operatorname{rank}H$, $r=\operatorname{rank}[H\ K]$. For the weighted rectangular matrix $X=[H\ \sqrt\theta K]$, the real comparison matrix $[G\ \sqrt\theta A]$ has rank at most $n$, and has nuclear norm at most $S=2\sqrt{p(p+21\theta)}$ by Frobenius Cauchy–Schwarz on the two factors. Its squared Frobenius distance from $X$ is at most $D$. If $r>n$, write $J$ for the product of the $r$ nonzero singular values of $X$. For some $x\in[0,D]$,
\[
 J^2\le
 \left(\frac{S+\sqrt{nx}}n\right)^{2n}
 \left(\frac{D-x}{r-n}\right)^{r-n}.
\]
Indeed the sum of squared differences of singular values is bounded by the squared Frobenius error (Mirsky's inequality); allocate $x$ to the first $n$ slots and apply both arithmetic–geometric means. The verifier uses the slightly larger rational $D_*$ in place of $D$ and splits its range for $x$ into 512 intervals with outward rational square-root bounds.

For a lower bound, the squared product $J^2$ is the sum of squared full minors. Any row basis and column basis give a nonzero full minor (use a rank factorization); before scaling it is a nonzero integer. Thus it suffices to lower-bound the number of row bases times the sum of $\theta^{\#\text{ unmarked columns}}$ over column bases.

Here are the details of the finite counts in the verifier. For $a$ available marked rows/columns and $j$ previously spanned dimensions, define
\[
 I(a,j,k)=\frac1{k!}\prod_{i=0}^{k-1}\max(0,a-m_{j+i})\quad (I(a,j,0)=1).
\]
This counts a lower bound for independent extensions by $k$ marked indices when the first $j$ are fixed. A marked row of $[H\ K]$ restricts to its row in $H$; the flat capacity $m_j$ therefore also bounds marked rows in any $j$-span.

**Row bases.** Fix a basis of $r$ rows and let $d=p-r$. Put $I_k=I(d,0,k)$. Each independent outside set extends to a basis using only original basis rows, and different outside sets have disjoint extensions. This gives the initial lower bound $\sum_{k=0}^{\min(r,8)} I_k$. To improve it, express the outside rows in coordinates of the fixed basis. An independent outside $k$-set has exactly one possible extension only if its support union consists of $k$ coordinates: any nonzero coordinate column of the coefficient array can be included in some nonzero $k$-minor. No outside singleton or pair has this property, by $m_1=1,m_2=3$ including the coordinate basis elements themselves. Hence add $I_1+I_2$.

An exceptional triple (one extension) uses exactly three coordinates. Any pair in it has support union at least three, so uniquely determines these coordinates, and at most $m_3-3=3$ outside rows lie in their span. Thus there are at most $X_3=\lfloor\binom d2/3\rfloor$ exceptional triples. For an exceptional four-set, deleting one member leaves a triple supported on three or four of its coordinates. If it uses four, these determine the coordinate flat, leaving at most $m_4-4-3=5$ choices for the deleted member. If it uses three, there are at most $d-3$ choices, and the triple was itself exceptional. Consequently a valid upper bound for exceptional four-sets is $X_4=\lfloor(5\binom d3+\max(0,d-8)X_3)/4\rfloor$. Add $\max(0,I_3-X_3)+\max(0,I_4-X_4)$ to the row lower bound. Call the result $L_r$.

**Column bases.** Fix a column basis containing $h$ marked and $t=r-h$ unmarked columns. There remain $a=p-h$ marked and $b=21-t$ unmarked columns outside that basis. All unmarked columns are distinct nonzero ternary vectors. A $j$-span contains at most $3^j-1$ such vectors: project injectively onto $j$ suitably chosen coordinate positions. The number of independent $k$-sets of outside unmarked columns is at least $V_k=(1/k!)\prod_{i=0}^{k-1}\max(0,b-(3^i-1))$. Append any independent subset of the outside marked columns and extend to a basis using the fixed basis alone. A resulting basis has at most $k+t$ unmarked columns. Since $\theta<1$ the weighted column-basis sum is therefore at least
\[
 W_{h,r}=\sum_{k=0}^{\min(3,r)}\theta^{k+t}V_k
                 \sum_{j=0}^{\min(8-k,r-k)} I(a,k,j).
\]

Finally $n\le h$ by the positive inertia result, and the [previous marked theorem](KissingFrontierAngularStability.md) gives $h\le12,13$ respectively. In dimension six, exclude $h=12$ first: for $H$ alone use $S=2p$ in the singular-product bound and compare with $J^2\ge L_{12}^2$ from its row and column bases. For the rectangular matrix one now has $J^2\ge L_rW_{h,r}$. The verifier contradicts the singular-product upper bound for every $r\ge12$ in dimension six or $r\ge13$ in dimension seven, with all $n\le h\le r\le\min(p,h+21)$ in the indicated ranges. Adding negatives of marked columns does not change rank, completing the proof.

**Replay:** run `node verify-signed-gram-flats-through-seven.js` and `node verify-kissing-frontier-discrete-embedding.js`. Both are standalone and use only Node.js.