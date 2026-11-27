# Trace-zero Moore determinants and a rank-metric degree cutoff

## 1. Result and parameters

Let $q$ be any prime power, $F=\mathbb F_{q^m}$, $K=\mathbb F_q$, and $H=\ker\operatorname{Tr}_{F/K}$. For $a\in F^*$ put
$$
D(x,y)=x^q y-xy^q,\qquad N_a=\#\{(x,y)\in H^2:D(x,y)=a\}.
$$
We prove the uniform two-sided count
$$
\left|q^2N_a+q(q+1)-(q^m+1)\right|
\le \bigl(q(q+1)(q^2-2)+2\bigr)q^{m/2}.
\tag{1}
$$
Consequently $D(H,H)$ contains every nonzero element of $F$ when $m\ge9$, for every $q$, and also when $q=2,m=8$.

For $\delta\in F^*$ of norm one, define
$$
f_\delta(x)=x^q+\delta x^{q^{m-1}},\qquad
U_\delta=\{(x,f_\delta(x)):x\in H\}.
\tag{2}
$$
This is the length-$m-1$ trace-zero family in Bartoli–Giannoni–Marino–Neri's §5(ii), using their $m=5$ displayed definition with the indicated exponent for general $m$. A subspace of $F^2$ is called **scattered** here if each one-dimensional $F$-subspace meets it in a $K$-subspace of dimension at most one. In the degree range just stated, no $U_\delta$ of norm one is scattered, so the corresponding two-dimensional rank-metric codes are not MRD. This is an existence cutoff for one family; these are not examples of nonextendable MRD codes.

There is a separate conditional nonextendability statement: for any $q$ and $m\ge6$, no $U_\delta$ with $\delta\ne0$ sits in a $\Gamma\mathrm L(2,F)$ image of a full graph $\{(z,z^{q^s}):z\in F\}$ with $\gcd(s,m)=1$. It follows that each scattered binary instance with $m\ge6$ is nonextendable, using Payne's classification. For $q=2$ we give the remaining exact finite data, including $m=5$, in Sec. 6. No general nonextendability claim is made for surviving cases at $q>2$ outside the previously published results.

## 2. Scatteredness and the Moore determinant

Any two nonzero vectors of (2) are on the same $F$-line exactly when their slopes $f_\delta(x)/x$ and $f_\delta(y)/y$ agree. They are $K$-proportional exactly when their first coordinates are. For $x,y\ne0$, put $u=x^{q-1}$ and $v=y^{q-1}$. Raising the two slopes to the $q$-th power gives $u^q+\delta^q/u$ and $v^q+\delta^q/v$ because $x^{q^m}=x$ and likewise for $y$. If $u\ne v$, equality is therefore equivalent to
$$
\delta^q=uv(u-v)^{q-1}=(xy(u-v))^{q-1}=D(x,y)^{q-1}.
\tag{3}
$$
Here $u\ne v$ is equivalent to $x/y\notin K^*$, and $D(x,y)\ne0$ also rules out zero coordinates. In the cyclic group $F^*$, the image of $a\mapsto a^{q-1}$ equals the norm-one subgroup: the image lies in it and both have size $(q^m-1)/(q-1)$. Thus for norm-one $\delta$ one may fix any $a\ne0$ with $a^{q-1}=\delta^q$. Every witness counted by $N_a$ is an actual pair of nonproportional vectors of equal slope in $U_\delta$.

Conversely if $\delta=0$ or its norm is not one, (3) forbids collisions on the whole field, so the full graph is scattered and any trace restriction extends to it. This is the known full-graph side of the contrast, not a new construction. The same norm-one cutoff holds for every trace hyperplane $\{x:\operatorname{Tr}_{F/K}(\lambda x)=0\}$, $\lambda\ne0$: the diagonal map $(x,y)\mapsto(\lambda x,\lambda^q y)$ takes (2) with that domain to the normalized $H$ with $\delta$ replaced by $\delta\lambda^{q-q^{m-1}}$, of unchanged norm.

For completeness, set $n=m-1$ and take a $K$-basis of $U_\delta$ as the columns of a $2\times n$ generator matrix over $F$. For $m\ge4$ this space spans $F^2$ over $F$: otherwise $f_\delta(x)=c x$ on $H$ for a constant $c$. An $F$-valued $K$-linear map vanishing on $H$ is an $F$-multiple of the trace, by factoring through the one-dimensional quotient. But $f_\delta(x)-cx$ has at most three nonzero cyclic $q$-exponents, whereas a nonzero multiple of the trace has all $m$. Uniqueness of the linearized representation follows from degree at most $q^{m-1}<|F|$. In the norm-one case $f_\delta(x)-cx$ is not identically zero; the same argument applies at $\delta=0$. Relative trace is surjective, since its nonzero linearized polynomial has degree $<|F|$, including when the characteristic divides $m$.

A nonzero row combination of the generator has rank weight $n-\dim_K(U_\delta\cap L)$, where $L$ is the kernel $F$-line of the corresponding $F$-linear functional. Hence the code is MRD of minimum rank distance $n-1$ iff the subspace is scattered; a basis vector supplies a line with intersection at least one. A one-column MRD extension corresponds exactly to adding a $K$-independent vector to get a scattered dimension-$m$ subspace. For the forward direction choose generator rows so their puncturing is the original matrix; a new column in the old $K$-span cannot raise the minimum rank distance from $n-1$ to $n$. The reverse direction is the same line-intersection formula. This is the ordinary $F$-linear rank-metric extension question.

## 3. A smooth curve and its two Artin–Schreier equations

For a fixed $a\ne0$ define the projective plane curve over $F$
$$
E_a:\ X^qY-XY^q=aZ^{q+1}.
$$
Its partial derivatives are $(-Y^q,X^q,-aZ^q)$ because the characteristic divides $q$ but not $q+1$. They never vanish simultaneously at a projective point, even over $\overline F$. Thus $E_a$ is smooth and geometrically irreducible (distinct plane components would intersect and give a singularity). Its degree is $q+1$, so its genus is $g_0=q(q-1)/2$.

Set $x=X/Z$, $y=Y/Z$. The points at infinity are precisely $P_t=(1:t:0)$ for $t\in K$ and $P_\infty=(0:1:0)$, all rational. At $P_t$ in the $X=1$ chart, writing $z=Z/X$ and $w=Y/X-t$, the equation reads $w-w^q=a z^{q+1}$. The derivative with respect to $w$ is one, so $z$ is a local parameter; at $w=0$ its valuation equation then gives $\operatorname{ord}(w)=q+1$. Therefore $x=1/z$ has a simple pole and $y-tx=w/z$ has a zero of order $q$. At $P_\infty$ in the $Y=1$ chart the analogous equation is $w^q-w=a z^{q+1}$ with $w=X/Y$, which gives a simple pole for $y$ and a zero of order $q$ for $x$.

The covering curve $C_a$ is the smooth projective model of the function field obtained by adjoining $U,V$ with
$$
U^q-U=x,\qquad V^q-V=y.
\tag{4}
$$
We show its degree over $E_a$ is $q^2$, even geometrically. If $g$ has a simple pole in a discrete valuation field, a root $u$ of $u^q-u=g$ has negative valuation $v'(u)$ in the extension, and $q\,v'(u)=-e$, where $e$ is the ramification index. Thus $q$ divides $e$, and the degree is at most $q$, forcing degree and $e$ both $q$. Apply this to $U$ at the pole of $x$ over $P_0$. At $P_\infty$ the right side $x$ is regular of residue zero, so $U^q-U=x$ splits into $q$ local components: reducing yields the $q$ simple roots in $K$, lifted by Hensel's lemma. On each, $y$ still has a simple pole, so the same valuation argument proves degree $q$ for the second extension. This proof applies unchanged over algebraically closed constants. In particular the smooth projective curve has constant field exactly $F$ and is geometrically irreducible.

## 4. Local different, genus, and the count

At any affine point of $E_a$ the right sides of (4) are regular and the two equations are finite étale there (monic with derivative $-1$); hence there is no affine ramification. At a point $P_t$, change variables from $(U,V)$ to $(U,V-tU)$: since $t\in K$, their right sides become $x,y-tx$. The second equation splits with $q$ components as before, while the first is totally ramified of degree $q$. At $P_\infty$ use $U$ for the split equation and $V$ for the totally ramified one. Thus exactly $q$ rational places lie over each of the $q+1$ points at infinity, with residue degree one and ramification index $q$ at each.

For a totally ramified degree-$q$ local component as above, $u^{-1}$ is a uniformizer (since $v'(u)=-1$). The Galois translations are $u\mapsto u+c$, $c\in K$. For each $c\ne0$ the difference $(u+c)^{-1}-u^{-1}$ has valuation 2: the numerator is the unit $-c$ and the denominator has valuation $-2$. The Hilbert different formula then gives different exponent $2(q-1)$ for this component. With the constant field just verified, Riemann–Hurwitz gives
$$
\begin{aligned}
2g(C_a)-2
&=q^2(2g_0-2)+(q+1)q\,2(q-1)\\
&=q(q+1)(q^2-2).
\end{aligned}
$$
This calculation counts all wild ramification and applies in each characteristic.

On $F$, the image of $u\mapsto u^q-u$ is $H$, since the image is contained in $H$, the kernel is $K$, and both dimensions agree. A pair $(x,y)\in H^2$ with determinant $a$ has exactly $q^2$ rational lifts by (4), while other affine rational points of $E_a$ have no rational lifts. Affine points of (4) are already smooth by étaleness, so this counts precisely the affine points of $C_a$. Adding the $q(q+1)$ points at infinity and applying Hasse–Weil proves (1).

To see the cutoff with explicit inequalities, let $M=q^{m/2}$ and $G=q^4+q^3-2q^2-2q+2=2g(C_a)$. The lower bound on the number of affine rational points is
$$
M(M-G)+1-q(q+1).
\tag{5}
$$
If $q=2$ and $m\ge8$, then $G=14$ and $M\ge16$, giving at least $27>0$. If $q\ge3$ and $m\ge9$, then $M\ge\sqrt q\,q^4>\tfrac32 q^4$ and $G<q^4+q^3\le\tfrac43 q^4$. Thus $M-G>q^4/6>1$ and $M\ge q^4>q(q+1)$, making (5) positive. In both cases $N_a>0$. By (3) this establishes the claimed failure of scatteredness for norm one. This is independent of any classification of maximum scattered subspaces.

## 5. Pseudoregulus exclusion and the binary extension conclusion

Let $m\ge6$ and $\delta\ne0$. Suppose $U_\delta$ is contained in a linear image of the graph of $z^{q^s}$, with $1\le s<m$ and $\gcd(s,m)=1$. Applying the inverse matrix gives an identity on $H$ for some $A,B,C,D\in F$ with $AD-BC\ne0$:
$$
(Ax+B f_\delta(x))^{q^s}=Cx+D f_\delta(x).
\tag{6}
$$
The same reduction handles a semilinear image: the field automorphism sends $H$ to itself and carries $\delta$ to its conjugate, or can be absorbed into the monomial graph, which is automorphism-invariant.

The difference of the two sides in the unique linearized representation has cyclic $q$-exponent support in $\{0,1,m-1,s-1,s,s+1\}$ modulo $m$. By vanishing on $H$ it is a multiple of trace. For $m\ge7$ the support omits an exponent; for $m=6$, the units $s$ are 1 and 5 and the support still omits exponents. Thus the multiple is zero. Compare coefficients on all of $F$:
- If $s=1$ or $m-1$, one of $s\pm1$ lies outside $\{0,1,m-1\}$ and forces $B=0$. The exponent in $\{1,m-1\}$ other than $s$ then forces $D=0$ (using $\delta\ne0$), making the matrix singular.
- If $2\le s\le m-2$, exponent $s$ forces $A=0$. The two exponents $s-1,s+1$ cannot both belong to $\{0,1,m-1\}$ for $m\ge6$. At the one outside, the coefficient from $B$ or $B\delta$ forces $B=0$, also making the matrix singular.

For $m=5$ only the binary case is used here. Swapping the two coordinates takes the full monomial graph of exponent $s$ to that of exponent $5-s$, so it is enough to test $s=1,2$. For $s=1$ the support argument gives the same contradiction. For $s=2$, in characteristic two the polynomial in (6) can equal a multiple $\eta$ of trace only if the coefficients at exponents $0,1,2,3,4$ satisfy
$$
C=D+(B\delta)^4=A^4=B^4=D\delta=\eta.
$$
If $\eta=0$ then $A=B=0$; otherwise $\delta^{-1}+\delta^4=1$, giving $\delta^5+\delta+1=0$. Over $\mathbb F_2$ this polynomial factors as $(X^2+X+1)(X^3+X^2+1)$; the factors have no $\mathbb F_2$ root and are irreducible of degrees 2 and 3. Neither degree divides 5, so there is no root in $\mathbb F_{32}$. This is the binary instance of the coefficient obstruction in Bartoli et al. Prop. 3.7.

To apply the exclusion to binary MRD extension, a scattered dimension-$m$ subspace of $\mathbb F_{2^m}^2$ has exactly $2^m-1$ occupied $F$-lines among the $2^m+1$ available, since each contains exactly one nonzero vector of the subspace. Move the two missing lines to the coordinate axes by an $F$-linear map. The resulting subspace is the graph of an additive permutation $g:F\to F$, and $g(z)/z$ permutes $F^*$ because all nonzero slopes are distinct and both axes are absent. Payne's classification of additive permutations with this ratio property gives $g(z)=c z^{2^s}$ with $c\ne0$ and $\gcd(s,m)=1$; scale the second coordinate to remove $c$. This is a classification of the actual subspaces under linear changes, not just an inference from projective equivalence of their occupied point sets. Therefore a scattered binary $U_\delta$ at $m\ge5$ cannot have an MRD extension. This part uses Payne's theorem, but in the small surviving cases it is also checked directly without relying on the classification.

## 6. Exact finite supplement for $q=2$

In binary arithmetics the norm-one condition covers all $\delta\ne0$. On $H$, the determinant is $xy(x+y)$, so by (3) the allowed $\delta$ are precisely those whose square is absent from the set of products of the three nonzero elements of a binary plane in $H$. The following table is exact finite enumeration, not an analytic hypothesis used for the large-degree result.

| $m$ | Number of attained nonzero determinants | Scattered parameters $\delta$ |
|---:|---:|---|
| 5 | 25 of 31 | $1$ and the five roots of $X^5+X^4+X^3+X^2+1$ |
| 6 | 63 of 63 | none |
| 7 | 126 of 127 | $1$ |

One checker forms the determinant set, builds the slopes by the original formula and verifies the field-invariant polynomial description of the five nontrivial roots. The independent checker enumerates image dimensions for each rank-metric word instead, in different polynomial-basis fields where available. It also checks all nonzero quotient classes of $F^2/U_\delta$ for every scattered binary case in the table. Since the base field is binary, each such class specifies a unique one-dimensional enlargement of the quotient; the test covers every one-column extension. All seven instances are nonextendable. For $m\ge8$ the uniform analytic theorem covers all binary degrees, also consistent with the prior strong D-property result.

This addresses large-degree nonexistence for the named family and exact behavior over the binary base field. In particular the general $(q>2,m=7)$ existence and extendability questions are not settled here, nor are any of the other general MRD-code classification questions in the source.
