# A linear degree gap for completion of a Segre clan coordinate

**Theorem.** Let $q=2^n$, where $n\ge5$ is odd, $F=\mathbb F_q$, and $T=\mathrm{Tr}_{F/\mathbb F_2}$. Write polynomial functions in their unique form of degree $<q$. Suppose $G(0)=0$ and

$$T\!\left(\frac{(x+y)(G(x)+G(y))}{x^6+y^6}\right)=1 \quad\text{for all }x\ne y\text{ in }F.\tag{1}$$

Then either $G(X)=X^5+C^2X+CX^3$ for $C\in F$, or $\deg G\ge q/4+5$. In particular we determine every solution of ordinary univariate degree **at most $q/4+4$**, uniformly in the field order. In the small omitted field $q=8$, the same restricted conclusion follows from the direct certificate in §5. The proof for every odd $n\ge5$ is symbolic and needs no computations.

This is a degree-restricted case of the Segre-herd completion question, [Penttila–Storme (1998), Conjecture 5.6](https://doi.org/10.1006/jcta.1997.2855). In their prescribed Segre coordinates the coefficient triple is $(t^{1/6},t^{1/2},a(t))$. Put $t=x^6$, a permutation since $\gcd(6,q-1)=1$ for odd $n$. The resulting triple is $(x,x^3,G(x))$, where $G(x)=a(x^6)$. The difference of two binary quadratic forms of the clan is anisotropic if and only if (1) holds. The degree hypothesis is about **this $G$**, not $a(t)$ or its Boolean algebraic degree. It suffices that it hold in one such normalization, not every possible coordinate system. It is not asserted to be a projective invariant. The conclusion says that the clan is cone-projectively equivalent to the standard Payne clan: substitute $(v,w)\mapsto(v+Cw,w)$ in $xv^2+x^3vw+x^5w^2$. An unrestricted arbitrary-function conclusion for all odd field degrees is **not** proved here.

## 1. Linearization, the gauge, and the weights

Write $p=xy$ and $D_0=x^2+xy+y^2$. For $x\ne y$, $x^6+y^6=(x+y)^2D_0^2\ne0$. Expansion gives the two identities

$$\frac{(x+y)(x^5+y^5)}{x^6+y^6}=1+(p/D_0)^2+p/D_0,\qquad
\frac{(x+y)(C^2(x+y)+C(x^3+y^3))}{x^6+y^6}=(C/D_0)^2+C/D_0.$$

Since $T(1)=1$ and $T(z^2+z)=0$, these prove inclusion of the whole stated family. Let $D=q/4+4$ and assume $\deg G\le D$. First subtract the particular solution $X^5$. Then subtract the known homogeneous solution $C^2X+CX^3$ with $C^2$ equal to the linear coefficient of $G-X^5$ (squaring is bijective). Call the resulting polynomial $H=\sum_{i=1}^{D} c_iX^i$. Its constant and linear coefficients vanish; its degree is still at most $D$. We must prove $H=0$.

Set $N=q-1$. For $y\in F^*$ and $r\in F\setminus\{1\}$ take $x=ry$ in the homogeneous equation. It becomes

$$T\left(\sum_{i=1}^{D} c_i\,\frac{1+r^i}{A(r)}y^{i-5}\right)=0,\qquad
 A(R)=(1+R)(1+R+R^2)^2=1+R+R^2+R^3+R^4+R^5.\tag{2}$$

Here $(1+R^6)=(1+R)A(R)$ and $A$ has no root in $F$ apart from $1$. The identity includes $r=0$; it need not hold at $r=1$. Call $w=i-5\pmod N$ the **weight** of a coefficient. Monomials in $y$ with exponents $0,\ldots,N-1$ form a basis for functions $F^*\to F$: a polynomial of degree $<N$ with $N$ roots is zero. Consequently the sum of all contributions to each weight in the expansion $T(z)=\sum_{t=0}^{n-1}z^{2^t}$ vanishes for each permissible $r$.

## 2. Every possible nonzero weight orbit has a two-slot gap

Multiplication by $2$ modulo $N$ rotates an $n$-bit word. We count slots for **all $n$ rotations**, even when the least period is shorter. The zero residue is represented by the all-zero word. Call a slot occupied if its rotated weight corresponds to a nonzero coefficient of $H$, where the coefficient index $i$ is recovered as the unique positive integer at most $N$ congruent to $w+5$. The inequality $D<N$ makes this label unambiguous and rules out double counting within a slot. We prove that every nonzero orbit has two consecutive empty slots, in either cyclic orientation.

* If the orbit does not meet $-1,-2,-3,-4$, all its occupied weights, as nonnegative integers, are in $[1,D-5]=[1,q/4-1]$. Mark any one of its bits equal to 1. In two consecutive rotations it occupies bit positions $n-2$ and $n-1$ (positions start at zero). Both represented weights are at least $q/4$, so neither slot is occupied.
* The orbit of $-1,-2,-4$ consists of the complements of a single bit. Its minimum nonnegative representative is $q/2-1>q/4-1$, so only the three stated negative weights might occur. Weight $-4$ corresponds to $i=1$ and was killed by the gauge. The orbit has full period $n$. At most two occupied slots on a cycle of odd length $n\ge5$ leave two consecutive empty slots.
* The orbit of $-3$ consists of the complements of two cyclically adjacent 1 bits, and also has period $n$ (the adjacent pair has a unique initial position). Its minimum representative is $q/4-1$, obtained only when the two highest bits are absent. Hence the only possibly occupied slots are $-3$ (index 2) and that one positive boundary weight (index $D$). Again at most two slots can be occupied. The two exceptional orbits are distinct by Hamming weight.

No assertion of full orbit size was needed in the first case; repetitions still have their two consecutive empty positions. There is no coefficient of index zero, so weight $-5$ does not furnish an additional exceptional slot.

## 3. A gap forbids the entire orbit

Suppose a nonzero orbit is occupied. Traverse its slots by **halving** the weight modulo $N$; after a run of at least two empty slots, start at the next occupied one. Write $j$ for its coefficient index and $e=j-5$ for its weight modulo $N$. Number successive slots in this direction by $t=0,1,\ldots,n-1$. The last two slots are empty. If $i_t$ is the coefficient index for the $t$th occupied slot, then

$$2^t(i_t-5)\equiv j-5\pmod N.\tag{3}$$

Let $S$ denote the set of occupied $t$, $J=\max S$, $M=2^J$, and $b_t=c_{i_t}^{2^t}$ for $t\in S$. Then $0\in S$, $b_0=c_j\ne0$, $J\le n-3$ and $M\le q/8$. The coefficient at $y^e$ in (2) is exactly

$$\sum_{t\in S} b_t\frac{1+r^{i_t2^t}}{A(r)^{2^t}}=0.\tag{4}$$

Indeed, for each given trace summand $t$, equation (3) has only one residue $i_t$ since $2$ is invertible mod $N$. For shorter orbits the *same* $c_i$ can contribute for several different $t$; all such terms appear in (4). Taking $r=0$ gives $\sum_{t\in S} b_t=0$. In particular $J\ne0$, because otherwise that sum is $b_0\ne0$.

For every $r\in F^*\setminus\{1\}$, (3) allows replacing $r^{i_t2^t}$ by $r^{j+5(2^t-1)}$. Clear $A(r)^M$ and let

$$U(R)=\sum_{t\in S} b_t A(R)^{M-2^t},\quad
 V(R)=\sum_{t\in S} b_t R^{5(2^t-1)} A(R)^{M-2^t}.$$

The polynomial $P(R)=U(R)+R^j V(R)$ vanishes on $F^*\setminus\{1\}$. It also vanishes at $R=1$ **from its polynomial definition**: each summand contains $(1+R^{j+5(2^t-1)})$, so is zero there, including the summand with the zeroth power of $A$. We did not use (2) at its pole. We have

$$\deg U,\deg V\le5(M-1),\qquad \deg P\le j+5(M-1)\le(q/4+4)+5(q/8-1)=7q/8-1<N.$$

For $V$, the two contributions to the degree add to $5(2^t-1)+5(M-2^t)=5(M-1)$. Thus vanishing at all $N$ nonzero elements makes $P$ **the zero polynomial**. The only modular reduction used was on values $r\ne0$ in (3); the explicit representatives in $P$ have total degree $<N$, so no cyclic wrap can invalidate comparing ordinary coefficients. Overlap of lower-degree monomials is allowed and does not affect the following comparison.

At $R=0$, $A(0)=1$, so $U(0)=\sum b_t=0$ and $V(0)=b_0\ne0$. The coefficient of $R$ in $U$ equals $b_0$, since $A=1+R+O(R^2)$, $M-1$ is odd and all the other exponents $M-2^t$ are even. Hence $U$ has a **simple zero** at $0$. The zero order of $R^j V$ is exactly $j$. As $P=0$ implies equality of the two polynomials in characteristic two, we obtain $j=1$. But by construction $c_1=0$ whereas the starting slot had $c_j\ne0$. Contradiction. No nonzero orbit is occupied.

## 4. The weight-zero coefficient

The only remaining possible term is $H=c_5X^5$. In (2), putting $r=0$ first gives $T(c_5)=0$. By §1 the ratio $(1+r^5)/A(r)$, for $r\ne1$, equals $1+v(r)^2+v(r)$, where $v(r)=r/(1+r+r^2)$. The denominator is nonzero on $F$. At $r=1$ we have $v=1$ and $T(c_5(1+v^2+v))=T(c_5)=0$ as well. Therefore

$$T\big((\sqrt{c_5}+c_5)v(r)\big)=0\qquad\text{on all of }F.$$

Here $T(c_5v^2)=T(\sqrt{c_5}v)$. Cross multiplication shows $v(r)=v(s)$ iff $(r+s)(rs+1)=0$. Thus $0,1$ are singleton fibers and all other inputs form reciprocal pairs: the image has $q/2+1$ values. If $\sqrt{c_5}+c_5\ne0$, its trace functional has kernel of size only $q/2$ (multiplication by a nonzero element is bijective and $T(1)=1$). Consequently $c_5\in\mathbb F_2$ and then $0=T(c_5)=c_5$ since $n$ is odd. This finishes the proof. ∎

## 5. Independent arithmetic checks and precise scope

Python 3.10+, no packages:

    python3 verify_gaps.py
    python3 verify_equations.py

* `verify_gaps.py` uses only integer rotations and exhausts every orbit at odd $n=5,7,\ldots,19$. It checks even maximal allowed supports (before any further coefficients vanish), two-slot gaps, index reduction, the root bound, and proper shorter orbits at $n=9,15$. Removing any occupied sites preserves existence of a two-slot gap.
* `verify_equations.py` uses no weight or rational reduction. It constructs the original pair constraints on the $nD$ scalar binary coefficients of $H$ via polynomial-basis field products and absolute trace. The field is verified by generating its entire multiplicative cycle. It tests the particular solution and the $n$ basis gauges on each row and stops when the rank reaches the rigorous upper bound $nD-n$; §1 supplies the global gauges, which are independent since their cubic coefficient recovers $C$. For $n=3,5,7,9$ it gives $(D,\mathrm{rank})=(6,15),(12,55),(36,245),(132,1179)$. Thus $q=8$ has the stated independent small-field certificate (the gap proof was not asserted there). At $q=32$ the symbolic argument applies including the boundary weight 7; at $q=128$ the actual inclusive degree bound is 36, not 35. The certificates are regression tests, not a numerical extrapolation.

## 6. Closest prior results

* [Penttila–Storme (1998), Theorems 5.1–5.2 and Conjecture 5.6](https://doi.org/10.1006/jcta.1997.2855) discuss monomial hypotheses and the Segre–Payne problem. The Payne example and its cone-coordinate transforms are old. [O’Keefe–Penttila (2000)](https://doi.org/10.1023/A:1005153406421) explicitly distinguish the Segre case from their classification for translation ovals. [Monzillo–Penttila–Siciliano (2022)](https://arxiv.org/abs/2205.05344) includes $q=8,32$ in the complete small-order classification. We do not claim any new flock.
* **Direct prior degree result:** [Bartoli–Durante–Grimaldi (2024), *On the classification of low-degree ovoids of* $Q^+(5,q)$, equation (3), Main Theorem case 1, and Remark 1.4](https://doi.org/10.1007/s10801-024-01365-4). Set $f_1(X,Y)=Y+X^3$ and $f_2(X,Y)=G(X)$. For distinct first coordinates $x,y$, their equation (3) requires that $w^2+(x^3+y^3)w+(x+y)(G(x)+G(y))$ never vanish as $w$ ranges over $F$. For equal first coordinates and distinct points the condition reduces to $w^2\ne0$. Thus their criterion is precisely (1), because $x^3+y^3\ne0$ for $x\ne y$. Their Main Theorem assumes $q>6.31(\max(3,\deg G)+1)^{13/3}$; in characteristic two its nonlinear alternative requires $3<\deg G\le5$ odd, hence $\deg G=5$. It does not give all compatible quintic coefficients in its statement. Here the fixed middle function $X^3$ permits a **linear bound $q/4+4$**, instead of their general range of order $q^{3/13}$, and gives all compatible coefficients. The fact that a single fixed polynomial persisting over unbounded fields must have degree five already follows from their result and is not presented as a new exceptional-polynomial classification.
* [Caullery–Schmidt (2015), *On the classification of hyperovals*](https://doi.org/10.1016/j.aim.2015.07.016) concerns low degree of the o-polynomial of **one** hyperoval, not its arbitrary compatible clan coordinate in this normalization. Targeted searches for low-degree flocks, Segre/Payne herd completion, and low-degree hyperbolic ovoids located the 2024 result above, but not this fixed-coordinate linear degree window. This is a bounded literature comparison, not a guarantee of priority.
