# Single-harmonic obstructions above 72 and 126 kissing points

**Six dimensions.** A kissing code with harmonic index $7,13,19,25$, or **any odd $k\ge29$**, has at most **72** points.

**Seven dimensions.** A kissing code with harmonic index $7,13$, or **any odd $k\ge19$**, has at most **126** points.

Each individual index is sufficient: the code need only sum to zero on all homogeneous harmonic polynomials of that **one** degree. No other harmonic moments, exact antipodes, root subset, point group or prescribed distances within the code are assumed. Consequently an unrestricted counterexample has nonzero harmonic moment at **every** indicated degree simultaneously. At degree seven the equality cases are exactly the $E_6$ and $E_7$ root codes up to isometry. At the other indices the cardinality bounds are also attained by these antipodal codes; we do not claim uniqueness there. These are harmonic necessary conditions, not new general upper bounds on cardinality.

There are also smaller improvements at some of the degrees not covered above. In six dimensions index $21,23$ or $27$ implies at most **73** points. In seven dimensions index $15$ implies at most **131**, and index $17$ at most **128**. These are not claimed sharp.

## 1. A closed formula at degree seven

Let $P_j$ denote the degree-$j$ Gegenbauer polynomial for real ambient dimension $d$, normalized to $P_j(1)=1$. For a unit spherical code $X$ of $N$ points write
$$
 M_j(X)=\frac1{N^2}\sum_{x,y\in X}P_j(x\cdot y).
$$
The [spherical addition formula](https://doi.org/10.1007/BF03187604) makes $M_j\ge0$, with equality precisely when all degree-$j$ harmonic sums vanish. Put
$$
 g(t)=(t^4-t^2/4)\bigl(1+(7t-4t^3)/3\bigr)
     =t^2(2t-1)(2t+1)^2(1+t)(3-2t)/12 .
$$
It is nonpositive on the entire kissing interval $[-1,1/2]$, with zeros $-1,-1/2,0,1/2$. We have $g(1)=3/2$. In its Gegenbauer expansion only the degree-seven coefficient is negative. The constant and that negative coefficient are $(1/48,-5/32)$ for $d=6$ and $(1/84,-128/663)$ for $d=7$. Direct expansion by the recurrence in §3 verifies these signs. Summing the polynomial over the ordered pairs proves the quantitative statements
$$
 M_7(X)\ \ge\
 \begin{cases}
 \dfrac2{15}(1-72/N), &d=6,\\[3pt]
 \dfrac{221}{3584}(1-126/N), &d=7.
 \end{cases}
$$

If equality in the cardinality bound is attained with $M_7=0$, all off-diagonal products must be roots of $g$. Hence $X\cup(-X)$ is an antipodal kissing code and contains $X$. The classical antipodal maxima in these dimensions are $72$ and $126$, with equality unique ([Anstreicher, Table 1 and the uniqueness discussion](https://optimization-online.org/wp-content/uploads/2001/01/248.pdf)). Thus $X$ was already the corresponding root code.

## 2. High degrees: a circle obstruction and harmonic interpolation

There is a useful distinction between many points and many **unpaired** points. In real dimension $d\ge6$, a non-antipodal kissing code of any single odd harmonic index $k\ge5$ has **at least $2k+2$ unpaired points**. This conclusion has no upper cardinality hypothesis.

In fact consider any nonempty collection of $r$ distinct real projective directions carrying a degree-$k$ harmonic relation with nonzero weights. If $r\le2k+1$, then some real two-dimensional linear subspace contains at least $k+2$ directions. Here is the interpolation proof. Use an orthogonal change of coordinates and put
$$
 L(x)=(x_1+i x_4,\ x_2+i x_5,\ x_3+i x_6)\in\mathbb C^3 .
$$
Choose the rotation generically so that every linearly independent real subcollection of up to three of the original vectors remains independent over $\mathbb C$ after $L$. For each subcollection some minor is nonzero for a rotation placing its span in the first three real coordinates; the failure set is therefore a proper real-analytic zero set on the connected rotation group. The intersection of finitely many such dense open sets is nonempty. Every homogeneous holomorphic polynomial in the three forms $L$ pulls back to a degree-matched harmonic polynomial.

Suppose no two-plane contains more than $k+1$ directions. Fix a target direction $x$. Group the other directions by the real plane they span with $x$, so each class has at most $k$ members. Order the $r-1\le2k$ directions class by class, pad to length $2k$ with blanks, and group positions $i$ and $i+k$, $1\le i\le k$. No pair of actual directions comes from one class. For each such pair $y,z$, the vectors $L(x),L(y),L(z)$ are independent; there is a complex linear form vanishing on the pair and nonzero on the target. For a singleton, or two blanks, select any linear form with the analogous property. Their product is a degree-$k$ harmonic test that singles out the target, contradicting the relation.

In a kissing code first discard all antipodal pairs; oddness preserves the moment equations. At most five residual points can lie on a great circle: six at separation at least $60^\circ$ must form a regular hexagon and would include antipodal pairs. Thus the interpolation obstruction applies for $k\ge5$, proving the stated residual count. For comparison, without the kissing-angle hypothesis the exact minimum and its regular-polygon rigidity are [proved here](SingleOddHarmonicMinimum.md).

Use [Tomar's unrestricted certified bounds](https://www.mefyi.com/papers/kissing-numbers-five-seven/) $N\le76$ and $N\le132$ in dimensions six and seven. Thus for odd $k\ge39$ or $k\ge67$, respectively, a code with harmonic index $k$ must already be antipodal, and the classical bounds apply. This leaves only finitely many smaller degrees.

## 3. Exact certificates for the finite gap

For each finite certificate the [standalone standard-library checker](verify-kissing-single-harmonic-obstructions.py) stores sparse **integer** coefficients of $F(t)=c_0+\sum_j c_j P_j(t)$, using $c_0=999500$. The only negative coefficient is $c_k$. It verifies both $F(t)\le0$ on $[-1,1/2]$ and $F(1)<Bc_0$, where $B$ is the first forbidden cardinality in the relevant theorem. Consequently
$$
                  M_k(X)\ge\frac{c_0-F(1)/N}{|c_k|}>0
                  \quad\text{whenever }N\ge B.
$$
This gives explicit positive lower bounds as well as exclusions. The table has 12 rows in dimension six and 28 in seven (the degree-seven rows are redundant controls for the analytic polynomial in §1). Each degree in the finite range claimed above is explicitly indexed; no interpolation between different degrees is used.

The checker forms the exact rational polynomials from
$(j+d-2)P_{j+1}=(2j+d-2)tP_j-jP_{j-1}$, $P_0=1,\ P_1=t$.
It converts $F(-1+3u/2)$ to Bernstein form for $u\in[0,1]$, clears denominators, and subdivides by integer de Casteljau until every Bernstein coefficient on every surviving interval is nonpositive. All 40 rows pass in 597 terminal intervals in total. The discretized numerical fit used to locate candidate coefficients is **not** a sign test. Reproduce with `python3 verify-kissing-single-harmonic-obstructions.py`.
