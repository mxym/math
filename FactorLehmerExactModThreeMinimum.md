# The exact Mahler minimum for uniform inner coefficients 2 modulo three

**Theorem.** Let $P\in\mathbb Z[x]$ be monic of positive even degree $D\ge2$, reciprocal in the sense $x^D P(1/x)=P(x)$ (so its constant coefficient is 1), and assume that every coefficient other than the leading and constant coefficients is $2\bmod3$. Suppose $P$ has no root of unity. Then its Mahler measure is minimized uniquely by
\[
                 P_4(x)=x^4-x^3-x^2-x+1.
\]
Its measure is the positive real root $\rho\in(1.7220,1.7221)$ of $P_4$ greater than 1. Every other polynomial in the stated class has
\[
                         M(P)>431/250=1.724.
\]
There is no irreducibility or coefficient-height assumption. The theorem does not concern the unrestricted Lehmer problem or residues other than the stated one. The positive-degree hypothesis is necessary to exclude the constant polynomial 1; positive odd reciprocal degrees cannot occur without the unit root $-1$.

This resolves the minimum in the $r=2,m=3$ class of [Jha–Thangadurai, Theorem 1.2](https://arxiv.org/abs/2610.33631). The [previous auxiliary resultant](FactorLehmerAuxiliaryModThree.md) left a finite degree interval. Rather than enumerate that whole interval, the new argument combines the reciprocal pairing with the Hadamard three-circle theorem to concentrate all radial loss in the same bound. The only needed finite computations beyond the rational comparisons below are the already fixed degree-eight and degree-ten checks, stated precisely in Section 3.

## 1. A reciprocal resultant inequality with radial loss

We use $M(P)=\prod_\alpha\max(1,|\alpha|)$, over roots counted with multiplicity, for a monic $P$. Let $F$ be another polynomial of degree $d$ satisfying $z^dF(1/z)=\eta F(z)$ with $|\eta|=1$, and set
\[
               U(h)=\max_{|z|\le e^{-h}}|F(z)|,\qquad h\ge0.
\]
For any integer $s\ge1$ and monic reciprocal $P$ of degree $D=2m$ without roots $\pm1$,
\[
 \big|\operatorname{Res}(P,F(x^s))\big|
 \ \le\ M(P)^{sd}\,U(0)^{D-2}\,U(s\log M(P))^2.
\tag{1}
\]
Indeed, partition the multiset of roots of $P$ into pairs $\alpha_i,\alpha_i^{-1}$ with $r_i=|\alpha_i|\ge1$. Define $h_i=s\log r_i$. Then $\sum_i h_i=s\log M(P)$. By reciprocity of $F$,
\[
 |F(\alpha_i^s)F(\alpha_i^{-s})|
   =r_i^{sd}|F(\alpha_i^{-s})|^2
   \le r_i^{sd}U(h_i)^2 .
\]
Hadamard's three-circle theorem makes $\log U(h)$ convex in $h$, since $\log e^{-h}=-h$ is affine. Put $L(h)=\log U(0)-\log U(h)$. This is concave with $L(0)=0$. For nonnegative $a,b$ with $a+b>0$, concavity gives
\[
 L(a)\ge\frac a{a+b}L(a+b),\qquad
 L(b)\ge\frac b{a+b}L(a+b),
\]
so $L(a)+L(b)\ge L(a+b)$. The case $a=b=0$ is immediate. Induction yields
\[
 \sum_i\log U(h_i)
   =m\log U(0)-\sum_i L(h_i)
   \le (m-1)\log U(0)+\log U\!\left(\sum_i h_i\right).
\]
Multiplying the paired estimates proves (1). This correction is valid for any placement of the roots on and off the unit circle.

## 2. The uniform analytic gap for every $D\ge12$

Use the reciprocal auxiliary polynomial
\[
 F(z)=(z-1)^{12}(z+1)^2(z^2+z+1)^5,\qquad \deg F=24.
\]
One has $U(0)<218$. On the unit circle,
\[
 |F(z)|^2=[2(1-x)]^{12}[2(1+x)]^2(1+2x)^{10},\qquad x=\operatorname{Re}z.
\]
Its zeros split the interval at $-1,-1/2,1$; the two nonzero maxima are at roots of $24x^2+17x-5$, from logarithmic differentiation. The exact intervals
$[-.931893,-.931892]$ and $[.223559,.223560]$ isolate those two roots. Bounding each factor outward over the respective interval gives the strict rational comparison with $218^2$. The verifier checks these comparisons. For the interior disks, the triangle inequality also gives
\[
   U(h)\le (1+u)^{14}(1+u+u^2)^5,\qquad u=e^{-h}.
\tag{2}
\]

Let $H_D=1+x+\cdots+x^{D-1}$. The coefficient assumption gives $P\equiv(x+1)H_D\bmod3$. If two polynomials have a common monic factor of degree $k$ modulo 3, the resultant of a monic $P$ with the other polynomial is divisible by $3^k$: the matrix of multiplication by the other polynomial on the integral free module $\mathbb Z[x]/(P)$ has rank deficiency at least $k$ modulo 3. This determinant interpretation works even when the common factor has multiplicities. In particular:
* $x^D-1=(x-1)H_D$ gives at least $3^{D-1}$. When $3\mid D$, the additional factor $P(1)\equiv2D\equiv0\bmod3$ improves this to $3^D$, by multiplicativity with the two displayed factors.
* $x^{2D}+x^D+1\equiv(x^D-1)^2\bmod3$. Since $D$ is even, $x+1$ divides $H_D$, so the reduction of $P$ itself divides this square. The resultant therefore contributes $3^D$.
* The remaining auxiliary factor gives a nonzero integer resultant. In fact none of these resultants vanishes: each factor tested has only roots of unity.

It follows that
\[
 \big|\operatorname{Res}(P,F(x^D))\big|\ \ge 3^{17D-12};
\tag{3}
\]
if $3\mid D$, the stronger divisor is $3^{17D}$. First use the coarser upper estimate $218^D M(P)^{24D}$, which follows from the unit-circle norm and reciprocity. The exact comparisons at $D=12$ and the positivity of the multiplying base give $M(P)>203/125$ at every $D\ge12$. Explicitly, $(3^{17}/[218(203/125)^{24}])^{12}>3^{12}$, and the base is greater than 1.

Therefore $u=M(P)^{-D}\le (125/203)^{12}$, and (2) gives $U(D\log M(P))<107/100$ by another rational comparison at this endpoint. Using the improved result (1) with $s=D$ against (3) yields
\[
 3^{17D-12}
       <218^{D-2}(107/100)^2 M(P)^{24D}.
\]
Put $R=431/250$. The rational number $z_0=3^{17}/(218 R^{24})$ is greater than 1 and satisfies
\[
 z_0^{12}218^2>3^{12}(107/100)^2.
\]
Thus $M(P)\le R$ contradicts these inequalities for every $D\ge12$. No finite upper limit on the degree is used.

## 3. The degrees below twelve and the unique minimizer

**Degrees two and four.** Suppose $M(P)\le R$, and put $T=461/200$. Each trace $t=\alpha+\alpha^{-1}$ satisfies
$|t|\le R+R^{-1}<T$ and $|\operatorname{Im}t|\le R-R^{-1}<\sqrt2$. In degree two this leaves coefficients $a\in\{-1,2\}$ for $x^2+a x+1$, both cyclotomic. In degree four write $P=x^4+a x^3+b x^2+a x+1$, so its trace quadratic is $t^2+a t+c$ where $c=b-2$. Vieta and the residues give
\[
                 a\in\{-4,-1,2\},\qquad c\in\{-3,0,3\}.
\]
When $c=0$, trace 0 gives unit roots of unity. When $c=-3$, the two cases $a=-4,2$ give a real root outside $[-T,T]$: at the endpoint with sign opposite to $a$ the quadratic is negative. When $c=3$, the case $a=-4$ has trace 3, and the other two cases have imaginary part of absolute value at least $\sqrt2$, also impossible.

The remaining pair $(a,c)=(-1,-3)$ gives exactly $P_4$. Its traces are $(1\pm\sqrt{13})/2$, one inside $(-2,2)$ and one greater than 2. Neither trace is in $\{-2,-1,0,1,2\}$, so there is no cyclotomic factor of degree one or two. A cyclotomic factor of degree four would force all roots on the unit circle, which the greater trace excludes; these are the only possible cyclotomic degrees through four. Thus $P_4$ belongs to the class. Its single outside root is isolated by the signs at $1.7220$ and $1.7221$, yielding the displayed strict gap.

**Degree six.** The strengthened divisor $3^{17D}$ and the coarser upper bound give $M(P)>(3^{17}/218)^{1/24}>R$.

**Degrees eight and ten.** These are the only computational inputs aside from the rational constants and low-degree tests above. The [fixed degree-eight and degree-ten theorem at commit 75217125](https://github.com/mxym/math/blob/7521712504a582aeb4ac320a4eeaac7ee6950907/research/euclidean-tensor-geometry/theoretical-cryptography/FactorLehmerSmallModThreeMinima.md) gives minima in $(2.2773,2.2774)$ and $(1.9970,1.9971)$ in these two degrees, respectively. It applies to this exact monic reciprocal class with no roots of unity, including reducible polynomials, and uses integer moments, an exact strict Schur test and exterior power traces. Both minima exceed $R$. The degree-four witness is therefore the unique global minimum in the stated class.

**Exact replay.** Run `python3 -O verify_factor_lehmer_exact_mod_three.py` for the rational norm, all-degree threshold, and the degree-two and degree-four comparisons. Run `python3 -O verify_factor_lehmer_small_mod_three.py 8 10` in the same folder for the separately fixed low-degree inputs. Neither the earlier degree-14 replay nor any larger degree search is needed for this proof.
