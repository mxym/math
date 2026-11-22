# A short integer witness for every remaining rank

Let $A$ be a hypothetical Conway adjacency matrix. Let $N_m$ count its signed integral $-4$ eigenvectors of squared norm $m$, counting both orientations. Define $F_1$ to count the vectors having seven entries $+1$, eighteen entries $-1$, and zeros elsewhere that satisfy $Ab=-4b-2\mathbf1$. Define $F_2$ to count the vectors with three entries $+1$, twenty-five entries $-1$, and zeros elsewhere that satisfy $Ab=-4b-4\mathbf1$. Then

$$N_{24}+16N_{16}+2F_1+F_2\ \ge\ 784.$$

All four counts in this statement can be defined from the graph. The argument applies to Seidel ranks 36, 38, 40 and 42 and also when the associated integral lattice has no roots. In particular, at least one of the four indicated support types occurs. The four types still require existence or nonexistence arguments.

## Separating the nine translates

Use the rank-44 lattice $U$ of determinant 49 with marks $v_i=3u_i$. Put $D=\{x\in U:(x,v_0)\equiv0\pmod3\}$. This has index three since $v_0^2=28$. Each $u_i-u_0$ belongs to $D$. The class $\alpha=[u_0]$ in $D^*/D$ has order nine and quadratic value $14/9$ modulo one. Indeed $9u_0\in D$ and $(u_0,u_0)=28/9$ has denominator nine. This cyclic group accounts for the entire 3-primary part of $D^*/D$. The 7-primary part is the anisotropic quadratic plane from $U$. [Rank-44 reduction](../maximal-marked-lattice/README.md)

For $0\le a\le4$ and integer $j$, write $Y_{a,j}$ for the number of $y\in D^*$ with class $a\alpha$, zero 7-component and squared norm $2j/9$. Write $X_{a,j}$ for the number with 3-component $a\alpha$, arbitrary 7-component and squared norm $2j/63$. Negating the charge preserves these counts. The two zero coefficients are one. When $7\mid j$, the norm forces the 7-component to be isotropic and hence zero. Thus $X_{a,7j}=Y_{a,j}$.

For such a vector the evaluations are $(y,u_i)=b_i+a/9$ with $b_i\in\mathbb Z$. Centering, the eigenvector equation and tightness yield

$$\sum_i b_i=-11a,\qquad Ab=-4b-2a\mathbf1,\qquad \sum_i b_i^2=(14j/\rho+11a^2)/9,$$

where $\rho=1$ for $Y$ and $7$ for $X$. The evaluations determine $y$ since the $u_i$ span. In particular, the last expression is an integer at least $11a$, congruent to $11a$ modulo two. For $a=0$, its nonzero values are at least fourteen. [Integral eigenvector bound](../short-support-packing/README.md)

## Fourier identity

The graph bounds above and the level-seven theta transformation give the following exact relation:

$$
\begin{aligned}
X_{0,108}+2X_{1,107}+2X_{2,86}+X_{2,104}
+84X_{1,44}+2X_{1,53}
={}&8(Y_{1,14}-1)+2X_{0,81}+2X_{1,62}+2X_{1,71}\\
&+X_{1,80}+2X_{2,95}+X_{3,108}+X_{4,110}.
\end{aligned}
$$

To obtain it, glue $D$ to the rank-eight root lattice $A_8$ along their cyclic discriminant groups at three. In the realization $A_8=\{d\in\mathbb Z^9:\sum d_i=0\}$, the charge-one generator in $A_8^*/A_8$ has quadratic value $4/9$, opposite to $14/9$ modulo one. Gluing gives an even rank-52 lattice $J$ of determinant 49 and level seven. In $J$ and $J^*$ the two 3-components match by construction. In $J$ the 7-component vanishes, while in $J^*$ all 7-components occur.

Use the axis $h=(8,-1,\ldots,-1)$ in $A_8$, with $h^2=72$. In charge $a$ the auxiliary vector has the form $w=d-(a/9)\mathbf1$ with $\sum d_i=a$, giving $r=9w^2/2=(9\sum d_i^2-a^2)/2$ and $(w,h)=9d_1-a$. The least $r$ is $a(9-a)/2$. At exponent $n$ in the theta series of $J$ or $\sqrt7 J^*$, the original shell index is $j=9n-\rho r$. The graph bounds in the preceding section determine which shell variables can be nonzero. Enumerating the nine integer coordinates gives the moments through degree eight without knowing the lattice $U$.

For each even $d=0,2,4,6,8$, weight these two theta series by the degree-$d$ zonal harmonic on the axis $h$. Its terms are $c_i(z,h)^{d-2i}(z^2h^2)^i$, with $c_0=1$ and $c_{i+1}/c_i=-(d-2i)(d-2i-1)/(2(i+1)(52+2d-2i-4))$. The resulting forms have weight $26+d$ and trivial character on $\Gamma_0(7)$. In the order scaled dual, primal, Poisson summation takes the first component to the second by $-7^{12}W_7$. The Fourier phase of the homogeneous harmonic cancels the degree-dependent phase in the slash operator. The odd-character Eisenstein product basis and its Fricke multipliers are as in the level-seven computation. For weight $k$ the dimension is $1+2\lfloor k/3\rfloor$. The checker verifies the same rank for the explicit products in the two-cusp expansion at every weight used. [Level-seven Fricke formulas](https://github.com/YesterdaysLemon/conway-99-research/tree/main/attempts/wave86-level7-exact) · [Harmonic theta series on lattices of given level](https://www.math.rwth-aachen.de/~Gabriele.Nebe/papers/stperfdim14.pdf)

Run `python3 affine_witness.py` with `python-flint` installed. Through exponent 20 the checker builds 114 independent affine equations in 134 variables. Reducing the displayed identity against these rows gives zero exactly. The verification requires no inequality solver.

## Eliminating two small profiles

Write $T=\sum b_i^2$. For $a=1$, there is no solution with $T\le19$. The budget $\sum b_i(b_i+1)\le8$ bounds the positive mass by four. An entry at most $-2$ would need neighbor sum at least six. An entry $+2$ leaves at most one other positive unit. Each negative unit would then have to see that site of value two. There are at least thirteen negative units, so the neighbor sum there is at most $-12$, contrary to the required $-10$. In the remaining case, with $p\le4$ positive units, every one of the $11+p$ negatives needs two positive neighbors; the positive pairs have at most $2\binom p2$ common-neighbor incidences. Thus in particular $X_{1,44}=X_{1,53}=0$.

For $a=2$, the case $T=24$ is impossible. The budget is two. A sole $-2$ among the nonunits would need a positive neighbor sum. The remaining possibility has one positive site $p$ and 23 negative units. Exactly eight negatives see $p$. Each of these eight sees one negative neighbor, whereas the other fifteen see none. Thus the eight form four mate pairs within the neighborhood of $p$. Each of the fifteen negatives outside that neighborhood must have two common neighbors with $p$, both among the six remaining neighbors of $p$. A mate pair already has $p$ as its unique common neighbor, and each nonmate pair can be used by at most one of the fifteen. There are only $\binom62-3=12$ nonmate pairs. This proves $X_{2,86}=0$.

## The four graph counts

Set $d_i=3e_i-Ae_i$, a vector of squared norm 23. Replacing $b$ by $b\pm d_i$ changes $a$ to $a\pm1$ and changes the squared norm to $T+23\pm2(7b_i+2a)$. This follows directly from $A^2=12I-A+2J$.

* At $a=0,T=24$, an entry of magnitude at least two would, after choosing the orientation and adding $d_i$, give $a=1,T\le19$. Thus every such eigenvector has twelve entries of each sign.
* At $a=2,T=28$, an entry at least two gives $a=1,T\le15$ by subtraction. An entry at most $-2$ gives $a=3,T\le31$ by addition, although the absolute sum must be at least 33. The unit profile consequently contributes at most $F_2$.
* At $a=1,T=25$, an entry at most $-2$ gives $a=2,T=24$ or $T<22$, both impossible. An entry at least two gives $a=0,T=16$ or $T\le2$ by subtraction. Here $T=0$ cannot occur since the new squared norm equals $44-14b_i$. Each norm-16 eigenvector has eight entries of each sign. The distinguished site is one of its negative sites since $b_i=2$ and $(d_i)_i=3$. Reversing the subtraction gives at most eight preimages per oriented norm-16 vector. All other $a=1,T=25$ vectors have the unit profile counted by $F_1$.

The 99 original points $u_i$ lie in $D+u_0$ and give $Y_{1,14}\ge99$. The right side of the identity is at least $8(99-1)=784$. The left side is at most $N_{24}+16N_{16}+2F_1+F_2$ by the preceding exclusions and the injectivity of evaluation. This establishes the claimed graph inequality.

## An exact count for each rank

Write $r=44-2m$ for the Seidel rank over $\mathbb F_7$. Let $G_{a,T}$ count all integer solutions of $Ab=-4b-2a\mathbf1$ with $b^tb=T$. Let $S$ count the solutions at $(a,T)=(1,23)$ with six positive units, seventeen negative units and all other entries zero. Let $C$ count the solutions at $(1,23)$ with $b-d_0$ in the integer span of all $d_i-d_j$. All these definitions use only the adjacency matrix. The stronger equality is

$$
\begin{aligned}
N_{24}+16N_{16}+2F_1+F_2={}&98(7^m+1)+7N_{14}+2N_{18}+S\\
 &+7^m(C-99)+2G_{2,26}+G_{3,35}+G_{4,44}.
\end{aligned}
$$

In particular $C\ge99$ since every $d_i$ qualifies. The constants $98(7^m+1)$ for ranks $36,38,40,42$ are respectively $235396,33712,4900,784$. At rank 36 the [support packing inequality](../short-support-packing/README.md) and the prism bound $P\le851$ give $16N_{16}\le196080-28N_{14}$. Thus

$$N_{24}+2F_1+F_2\ \ge\ 39316+35N_{14}+2N_{18}.$$

At rank 36 the graph must therefore have at least 19,658 distinct signed labelings of these last three types, since their largest coefficient is two. All signs are assigned to the 99 fixed vertices. Opposite sign assignments are distinct. The [sharper packing argument](norm16-packing.md) raises the lower bound to 62,258 and allows the signs to be forgotten.

For the proof put $M=\langle u_i-u_j\rangle_{\mathbb Z}$. The lattice $L$ is obtained from $M$ by adjoining $3u_0$, which has order three modulo $M$. Indeed the sum of $u_0-u_j$ over all sites is $99u_0$, and the sum over its neighbors is $18u_0$. Their integer span contains $9u_0$. Pairing with $u_0$ shows that no smaller positive multiple belongs to $M$. The discriminant of $M$ has cyclic 3-part generated by $[u_0]$ with quadratic value $14/9$, and 7-part $V=L^*/L$, a nonsplit quadratic space of dimension $2m$. For every maximal totally isotropic $H\subset V$ the corresponding $D=D_H$ contains $M$, with $D_H/M=H$ under this identification. In fact $D_H\cap L=M$ by the index-three character, and $[D_H:M]=[U:L]$.

Every graph solution gives a unique $y\in M^*$ by setting its evaluations equal to $b_i+a/9$. To see this, sum the adjacency equation to obtain $\sum b_i=-11a$. The centered vector $b+(a/9)\mathbf1$ then belongs to the $-4$ eigenspace, which is exactly the image of the evaluation map since the Gram matrix is $3I-A+J/9$. Pairings with differences are integral. The 3-component of $[y]$ is $a[u_0]$ since its pairing with $u_0$ is $a/9$ modulo one. If $v$ denotes the 7-component of $[y]$, then $y\in D_H^*$ exactly when $v\in H^\perp$. In particular $C$ counts the vectors at $(1,23)$ with $v=0$, by evaluating $y-u_0$ on every mark.

Average the identity over all $H$. For a fixed nonzero value of the quadratic form the probability that $v\in H^\perp$ is $p=8/(7^m+1)$. Indeed $V$ has $7^{2m-1}+7^{m-1}$ vectors at each nonzero value. Each $H^\perp$ contains $8\cdot7^{m-1}$ of them, by its anisotropic plane quotient. The orthogonal group acts transitively at each fixed nonzero value by Witt's lemma. For a nonzero isotropic vector, $v\in H^\perp$ is equivalent to $v\in H$. There are $(7^m+1)(7^{m-1}-1)$ nonzero isotropic vectors in $V$, and $7^{m-1}-1$ in $H$. The probability is $1/(7^m+1)$ whenever such vectors exist. At $m=1$ there are none. The two ambient counts follow by adjoining $m-1$ hyperbolic planes to an anisotropic plane.

Every $X$ index in the displayed Fourier identity has $7\nmid j$, so it has nonzero 7-primary quadratic value and averages to $p$ times its global graph count. All vectors in $G_{1,23}$ have isotropic 7-component. Hence the average of $Y_{1,14}$ is $C+(G_{1,23}-C)/(7^m+1)$. The terms $X_{1,62},X_{1,71},X_{1,80}$ vanish by the $T\le19$ bound.

Two multiplicities complete the proof. At $(1,25)$ the nonunit vectors are exactly $b'+d_i$ for a norm-16 eigenvector $b'$ and one of its eight negative sites. The entry two uniquely determines $i$ since the other coordinates are at most one. At $(1,23)$ an entry at most $-2$ would give $a=2,T\le22$ by adding $d_i$. Equality requires $b_i=-2$ and all new entries nonpositive, whereas the new entry at $i$ is one. An entry at least two gives $a=0,T=42-14b_i$ by subtracting $d_i$. This yields exactly the 99 vectors $d_i$ or the vectors $b'+d_i$ for a norm-14 eigenvector $b'$ and one of its seven negative sites. Again the exceptional entry determines the site. Thus $G_{1,25}=F_1+8N_{16}$ and $G_{1,23}=99+7N_{14}+S$. Substitution in the averaged identity gives the stated equality.
