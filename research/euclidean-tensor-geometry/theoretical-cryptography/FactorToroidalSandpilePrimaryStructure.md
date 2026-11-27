# Primary structure of the critical group of a rectangular torus

**Scope.** We give (i) exact \(p\)-ranks for \(C_m\square C_n\) at every prime, (ii) full elementary divisors at each odd prime not dividing both lengths, and (iii) a dyadic reduction to one square, with exact rank, order and stable shifts of *all* elementary divisors. We do not give a nonrecursive list for the dyadic square, settle the odd-prime case \(p\mid\gcd(m,n)\) beyond rank, or describe the sandpile identity configuration.

Let \(K_{m,n}\) denote the torsion subgroup of the full integral Laplacian cokernel of \(C_m\square C_n\). We take \(m,n\ge 3\) for simple cycles. Formulas using widths 1 or 2 count the two coordinate steps with multiplicity: loops cancel in the Laplacian and the two steps in \(C_2\) are parallel edges. Write \(K_{(p)}\) for the \(p\)-primary subgroup. An exponent \(e=0\) contributes no cyclic summand.

## 1. Local presentation

Fix \(p\), write \(m=A m_0,\ n=B n_0\) with \(A=p^a,\ B=p^b\) and \(p\nmid m_0 n_0\). The full cokernel over \(\mathbb Z_p\) is the quotient of the cyclic group ring by
\[
 L=4-x-x^{-1}-y-y^{-1},\quad x^m=y^n=1.
\]
It has one free summand because the graph is connected. Choose an unramified integer ring \(\mathcal O/\mathbb Z_p\) containing all \(m_0\)-th and \(n_0\)-th roots of unity. This scalar extension changes neither the Smith exponents nor their multiplicities, as is immediate by tensoring a Smith diagonal.

The factorizations \(x^m-1=\prod_{\alpha^{m_0}=1}(x^A-\alpha^A)\) and its \(y\)-analogue split the ring into blocks \(x=\alpha X,\ y=\beta Y,\ X^A=Y^B=1\). Distinct factors are coprime modulo \(p\), so the Chinese remainder decomposition is integral. Each block is finite free over \(\mathcal O\) and complete local: modulo \(p\) it is a truncated polynomial ring at \(X=Y=1\). It contributes only if \(L(\bar\alpha,\bar\beta)=0\). We count every root pair in the splitting ring, not just its residue-field Galois orbit; the result is the multiset of \(\mathbb Z_p\)-Smith exponents, without asserting a canonical choice of its summands.

## 2. The prime 2

Here assume \(a\le b\), interchanging the coordinate directions if necessary, and set \(g=\gcd(m_0,n_0)\). The complete reduction is
\[
(K_{m,n})_{(2)}\cong
\begin{cases}
(\mathbb Z/2)^{\,2(g-1)}, & b=0,\\
\mathbb Z/2^b\ \oplus\ (\mathbb Z/2^{b+2})^{\,2(g-1)},& a=0<b,\\
\operatorname{shift}_{b-a}\bigl((K_{A,A})_{(2)}\bigr)
 \ \oplus\ (\mathbb Z/2^{b+2})^{\,2A(g-1)}, & 1\le a\le b.
\end{cases}
\]
The shift replaces every cyclic order \(2^e\) by \(2^{e+b-a}\). In particular, a fixed odd part and \(b\ge\max(a,1)\) give an exact doubling law in the second length: every elementary-divisor exponent increases by one, and no new summands appear. This threshold is exact: below it the rank strictly increases under doubling, by the rank formula below.

Put \(d=\gcd(m,n)\). The rank is \(2d-2\) if both lengths are odd, and \(2d-1\) otherwise. The order exponent is
\[
 v_2|K_{m,n}|=
 \begin{cases}
 2(g-1),& b=0,\\
 b+2(g-1)(b+2),& a=0<b,\\
 2d(b+2)-5a-b-1,&1\le a\le b.
 \end{cases}
\]

### 2.1. Nontrivial odd roots

Modulo 2 we have \(L=(x+y)(1+1/(xy))\). The pairs are exactly the common odd roots with \(\beta=\alpha^{\pm1}\), by uniqueness of lifting roots of odd order. One pair is \((1,1)\). Each of the \(g-1\) other choices of \(\alpha\) gives two distinct pairs.

Fix one nontrivial pair. Let \(R_A=\mathcal O[X]/(X^A-1)\) and \(x=\alpha X\). The monic polynomial
\[
 f(y)=y^2-(4-x-x^{-1})y+1
\]
has two distinct residue roots, hence lifts to \(f(y)=(y-y_1)(y-y_1^{-1})\) over \(R_A\), with \(\bar y_1=\bar\beta\). In the given local \(y\)-block the other factor is a unit. At \(y_0=-x^{\pm1}\), with the sign chosen for \(\beta\), we have \(f(y_0)=-4y_0\) and \(y_0-y_1^{-1}\) a unit. Therefore \(y_1=y_0+4u\) for a unit \(u\), and \(y_1/\beta=-X^{\pm1}(1+4v)\) for a unit \(v\). Substitution for \(y\) leaves \(R_A/(y_1^B-\beta^B)\).

If \(b\ge 1\), then \(A\mid B\) and \((-1)^B=1\). Repeated squaring of \(1+4v\) shows \((1+4v)^B-1=2^{b+2}\) times a unit: for \(k\ge2\), the step factors as \((1+2^k w)^2-1=2^{k+1}w(1+2^{k-1}w)\). Thus a block contributes \(A\) copies of \(\mathcal O/(2^{b+2})\). If \(b=0\), then \(A=B=1\) and \(y_1/\beta-1=-2(1+2v)\) contributes one copy of \(\mathcal O/(2)\).

### 2.2. The dyadic core

The \((1,1)\) block is the full Laplacian quotient of \(C_A\square C_B\). For \(A=1\), setting \(u=y-1\) gives \(u^2=0,\ Bu=0\), so the torsion is \(\mathbb Z/2^b\) (or zero when \(b=0\)).

For \(a\ge1\) let \(R=\mathbb Z_2[X]/(X^A-1)\), \(s=4-X-X^{-1}\) and \(S=R[Y]/(Y^2-sY+1)\). Multiplication by \(Y^B-1\) on \(S\), a free \(\mathbb Z_2\)-module of rank \(2A\), presents the full core cokernel. Define \(T_j=Y^{2^j}+Y^{-2^j}\), so \(T_0=s,\ T_{j+1}=T_j^2-2\). The analogous sequence \(T'_j\) evaluated at \(Y=-X\) satisfies \(T'_0=-X-X^{-1}\). Inductively \(T_j-T'_j\in 2^{j+2}R\): the base difference is 4, and the sum is even at each step. If \(j\ge a-1\), the two powers of \(X\) in \(T'_j\) agree, so \(T_j/2\) is a unit of the local ring \(R\). For \(b\ge a\),
\[
 Y^{2^b}+1=Y^{2^{b-1}} T_{b-1}
\]
is therefore twice a unit in \(S\). The map presenting the next doubling is multiplication by \((Y^{2^b}-1)(Y^{2^b}+1)\), giving the asserted stable shift from the square, including the unchanged free rank.

All \(2A-1\) nonzero square Smith entries are even. Indeed
\[
 Y^{2^b}-1=Y^{2^{b-1}}(Y-Y^{-1})\prod_{j=0}^{b-2}T_j
 \quad (b\ge1),
\]
where the product is empty for \(b=1\). Modulo 2 the product apart from its unit power of \(Y\) is \(s^{2^{b-1}}\), since \(Y-Y^{-1}\equiv s\) and \(T_j\equiv s^{2^j}\). As \(s\equiv (X-1)^2/X\), this vanishes for \(B\ge A\). Exactly one Smith entry is zero, from the free rank one.

For an exact square presentation, compute \(Y^A-1=u+vY\) in \(S\) by repeated squaring, then use the linear map over \(R\)
\[
 \begin{pmatrix}u&-v\\v&u+sv\end{pmatrix}.
\]
Representing the entries by regular cyclic multiplication yields a \(2A\times2A\) integer matrix, with \(X^A=1\) and \(X^{-1}=X^{A-1}\) in the calculation. Its Smith valuations give the square. For example, the positive exponents for \(A=2,4,8\) are respectively \((1^2,3)\), \((1^2,3^4,5)\), and \((1^2,3^4,5^8,7)\), with superscripts indicating multiplicity. The reduction requires no Smith form of the original \(mn\times mn\) matrix.

### 2.3. Square tree-number valuation

For \(A=2^a\) with \(a\ge 1\), the eigenvalue for a pair of \(A\)-th roots \(x,y\) is \(4-x-x^{-1}-y-y^{-1}\). The product over all pairs except \((1,1)\), divided by \(A^2\), is the tree number. Extend the valuation \(v_2\) to the cyclotomic splitting field, normalized by \(v_2(2)=1\).

For \(x\) of exact order \(2^r\), \(r\ge1\), the value \(2-x-x^{-1}=-(x-1)^2/x\) has valuation \(2^{2-r}\). This follows also from the product of \(1-x\) over all primitive \(2^r\)-th roots, equal to 2, as conjugate factors have equal valuations. Mixed-order pairs have the smaller of their two valuations, including when one root is 1. There are \(2\cdot2^{r-1}\cdot2^{r-1}\) mixed-order pairs of maximum order \(2^r\), contributing \(2^{r+1}\) to the sum. The pair \((-1,-1)\) contributes 3.

For \(r\ge2\) and both roots of exact order \(2^r\), use
\[
 L=4-(x+y)(1+1/(xy)).
\]
The two values \(y=-x\) and \(y=-x^{-1}\) are distinct and each contributes 2. At any other \(y\) both factors are nonzero. When \(r\ge3\), write \(x=\zeta^u,\ y=\zeta^v\) with \(u,v\) odd; one of \(u+v,v-u\) is \(2\bmod4\), and stays so when shifted by \(2^{r-1}\). Thus one factor has valuation \(2^{2-r}\le1/2\) and the other at most 1. Their sum is less than 2, hence equals \(v_2(L)\). At \(r=2\) there are only the two exceptional values of \(y\).

For fixed \(x\), each factor as \(y\) varies has nonzero values with total valuation \(r-1\): up to units they are \((1-w)_{w^{2^{r-1}}=1,\ w\ne1}\). At the zero of its companion factor it has valuation \(2^{2-r}\), which must be subtracted. Adding the two exceptional valuations, the contribution per \(x\) is \(2r+2-2^{3-r}\). Multiplying by \(2^{r-1}\) gives \((r+1)2^r-4\). Summing all eigenvalue contributions and subtracting \(2a\) from \(A^2\) yields
\[
 v_2|K_{A,A}|=2A(a+2)-6a-1.
\]
The general order formula follows from the rank of the core, the shift, and the nontrivial odd-root blocks.

## 3. Exact \(p\)-rank for every odd prime

In this section interpret root pairs in an algebraic closure of \(\mathbb F_p\) and retain exactly the pairs satisfying \(L=0\). Define \(E_x\) and \(E_y\) as the numbers of retained pairs with \(\alpha=-1\) and with \(\beta=-1\), respectively. Let \(R_0\) be the number of retained pairs with neither coordinate in \(\{1,-1\}\). Then
\[
\begin{aligned}
 \dim_{\mathbb F_p} K_{m,n}/pK_{m,n}
 ={}&2\min(A,B)-\mathbf 1_{A=B}-1\\
 &+R_0\min(A,B)+E_x\min(A,2B)+E_y\min(2A,B).
\end{aligned}
\]

To prove it, the block modulo \(p\) has local parameters \(u=x-\alpha,\ v=y-\beta\) truncated by \(u^A=v^B=0\). If neither derivative of \(L\) vanishes, solve for \(v\) as a series with initial term of degree 1 in \(u\), giving length \(\min(A,B)\). At \(\alpha=-1\), the other derivative is nonzero and the initial term has degree 2 because the quadratic coefficient of \(x+x^{-1}\) is nonzero there; the length is \(\min(A,2B)\). The other orientation is symmetric. The pair \((-1,-1)\) is not retained since \(p\ne2\). Either coordinate 1 implies the other is 1. At \((1,1)\), the equation is \(u^2/(1+u)+v^2/(1+v)=0\). Formal coordinate changes \(u\mapsto u/\sqrt{1+u}\), \(v\mapsto v/\sqrt{1+v}\) preserve the truncation ideals and put it into the form \(u^2+v^2=0\). If \(A\le B\), reduce first to a free module on \(1,v\) over the ring \(k[u]/(u^A)\). The relation \(v^B=0\) is a unit multiple of \(u^{B-1}v=0\), as \(B\) is odd. This removes no dimension for \(A<B\) and one dimension for \(A=B\). Summing these lengths and removing the one free summand proves the formula.

The three counts require no splitting-field computation. Put \(C_0(z)=2,\ C_1(z)=z,\ C_{j+1}=zC_j-C_{j-1}\). Let
\[
 D=\deg\gcd\!\left(x^{m_0}-1,\ C_{n_0}(4-x-x^{-1})-2\right),
\]
taking the Laurent expression modulo \(x^{m_0}-1\). This counts horizontal roots allowing at least one vertical root. For any such horizontal root, the roots of the vertical quadratic are reciprocal, and \(C_{n_0}(z)=2\) is equivalent to their \(n_0\)-th powers being 1. The only repeated vertical roots are \(1,-1\), with 1 possible only at the origin. Therefore
\[
 \begin{aligned}
 E_y&=\mathbf1_{2\mid n_0}\deg\gcd(x^{m_0}-1,x^2-6x+1),\\
 E_x&=2\,\mathbf1_{\,2\mid m_0,\ C_{n_0}(6)=2\ \text{in }\mathbb F_p},\\
 R_0&=2D-2-E_x-2E_y .
 \end{aligned}
\]

## 4. All odd-primary exponents when one length is prime to \(p\)

Arrange \(p\nmid m\), so \(A=1\), and lift each retained root pair at \(p\) to \((\alpha,\beta)\) as in Section 1. These retain distinct meanings for \(\beta=1,-1\) in the odd residue characteristic. The primary exponents are the multiset union of:
* \((1,1)\): the single exponent \(b\);
* \(\beta\notin\{1,-1\}\): the single exponent \(b+v_p(4-\alpha-\alpha^{-1}-\beta-\beta^{-1})\);
* \(\beta=-1\): the two exponents \(b\) and \(b+v_p(\alpha+\alpha^{-1}-6)\).

As always, discard exponent zero. The origin reduces to the cycle as above. In the second case \(x=\alpha\) is constant and the quadratic has a unique lift \(y_1\equiv\beta\); the other root differs by a unit. The valuation of \(y_1-\beta\) is the valuation of \(L(\alpha,\beta)\), and for the unramified ring and odd \(p\), powering by \(p^b\) adds exactly \(b\) to the valuation of \(y_1^{p^b}-\beta^{p^b}\). This follows repeatedly by binomial expansion, with the first term the uniquely lowest valuation.

For \(\beta=-1\), put \(y=-(1+u)\), \(\kappa=\alpha+\alpha^{-1}-6\). The two-dimensional local algebra \(S'=\mathcal O[u]/(u^2-\kappa(1+u))\) has remaining relation \((1+u)^{p^b}-1=0\). If \(p\ge5\), expand the first \(p\)-th power as \(puV\); the final term in \(V\) is \(u^{p-1}/p\), which lies in \(pS'\) by \(u^2=\kappa(1+u)\) and \(p\mid\kappa\). The other terms are congruent to 1 modulo the maximal ideal, and \(V\) is a unit. For \(p=3\), the reduction of \(\alpha\) has order four (its trace is zero); its lift has trace zero as well, so \(\kappa=-6\). The factor \(V=1+u+u^2/3\) is a unit since it reduces to \(-1\) modulo the maximal ideal. Further \(p\)-th powers each multiply by \(p\) times a unit, by the binomial formula as the previous difference is already in \(pS'\). Thus the relation is \(p^b u\) times a unit, also for \(b=0\). Multiplication by \(u\) on \(S'\) has matrix \(\begin{pmatrix}0&\kappa\\1&\kappa\end{pmatrix}\); its Smith entries are 1 and \(\kappa\) up to units. All valuations in the nonsingular and negative-trace cases are finite: over a complex embedding the trace of a root of unity lies in \([-2,2]\), and equality in the sum of traces attaining 4 is possible only at the origin.

## Checks and related work

The companion script [verify_factor_toroidal_sandpile_primary.py](verify_factor_toroidal_sandpile_primary.py) checks the formulas with exact modular elimination, including full Laplacians through \(12\times12\) tori at 2, transfer matrices through \(A=64\), all rank formulas over four odd primes on small tori, checks of the full odd-primary formulas with explicitly lifted roots, and fixtures with repeated vertical roots that split only after extension. The checks support, but do not replace, the proofs.

* Biggs, [Chip-Firing and the Critical Group of a Graph](https://doi.org/10.1023/A:1018611014097), and Dhar–Ruelle–Sen–Verma, [Algebraic Aspects of Abelian Sandpile Models](https://arxiv.org/abs/cond-mat/9408020), give the classical relationship between chip firing, Laplacian invariants, and the critical group.
* Mednykh–Mednykh–Yudin, [On Jacobian group of the \(\Delta\)-graph](https://arxiv.org/abs/2211.12007), obtain the full integral group of \(C_3\square C_n\) as a special case of their cyclic-graph results. The formulas here apply to arbitrary width and distinguish residue-root singularities; they do not replace that integral formula.
* Mednykh–Mednykh, [Cyclic coverings of graphs](https://www.mathnet.ru/php/archive.phtml?jrnid=rm&option_lang=eng&paperid=10098&wshow=paper), Example 7.6, give the toroidal spanning tree product. Its \(2\)-adic valuation and the Smith structure are different questions.
* Gonet, [Iwasawa Theory of Jacobians of Graphs](https://doi.org/10.5802/alco.225), treats asymptotic Jacobian orders and modules in general voltage towers. Section 2 above instead computes the starting threshold and every finite invariant-factor shift for the fixed-width dyadic torus tower, together with the explicit tame blocks. The spectral product used for the tree number is standard; the proof above gives its finite dyadic valuation directly.
