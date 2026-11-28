# Effective Runge bounds for the two doubled unequal binomial shifts

For \(d\ge2\), let \((a,b)=(d,2d)\) or \((2d,d)\). Suppose \(n,k\) are nonnegative integers, \(n-k\ge a+b\), and
\[
                         {n\choose k}={n-a\choose k+b}.
\tag{1}
\]
Then
\[
                         n<2\cdot10^{29}d^{10}+3d.
\tag{2}
\]
For \(d=2,3\) the four cases are completely settled: the only solution is the boundary case \(k=0,n=3d\), representing the value 1. Thus no positive interior entry collides with either shift in these four cases. In addition, the positive real branch of each doubled-shift curve with \(d\ge2\) satisfies no nonzero polynomial of total degree at most five.

[Hugo Jenkins, *Repeated Binomial Coefficients and High-Degree Curves*, Theorem 1 (2016)](https://math.colgate.edu/~integers/q69/q69.pdf) proves qualitative finiteness for **all unequal** shifts \(a,b>0\); he points out much older complete elliptic calculations for \((1,2)\) and \((2,1)\). The bound here is effective and uniform but only for the stated two doubled-shift families. It neither bounds unrestricted multiplicity nor extends the previous repository result for equal shifts. No priority over unlocated independent computations is claimed.

## 1. The positive branch and the rational expansion

Put \(z=n-k,\ y=k,\ W=z-3d/2,\ Y=y+(b+1)/2\). For \(m\ge1\) let \(C_m(v)=\prod_{j=-(m-1)/2}^{(m-1)/2}(v+j)\), with step one. Cancelling factorials yields
\[
 \prod_{j=0}^{a+b-1}(z-j)
   =\prod_{j=0}^{a-1}(z+y-j)\prod_{j=1}^{b}(y+j),\qquad
 C_{3d}(W+1/2)=C_a(W+Y)\,C_b(Y).
\tag{3}
\]
For each real \(z\ge a+b\) the first equation has a unique real solution \(y(z)\ge0\). The right side is continuous and strictly increasing in \(y\), while at \(y=0\) the ratio left/right is \(\prod_{j=a}^{a+b-1}(z-j)/b!\ge1\). At \(y=z\) every factor on the right is at least \(z\), so the solution has \(y\le z\). It is analytic, since the derivative with respect to \(y\) is nonzero. It is also strictly increasing in \(z\), because at fixed \(y\ge0\) the logarithmic \(z\)-derivative of left/right is positive (compare the first \(a\) terms and retain the remaining \(b\)).

Write \(p=a/d,\ q=b/d\), so \(p+q=3\), and set \(\xi=d^2\), \(u=W^{-1}\), \(T=Y/W\). Let \(\alpha\in(1/3,1)\) solve \((1+\alpha)^p\alpha^q=1\), and put \(A(t)=(1+t)^p t^q\). The cubics \(A(t)-1=t^3+p t^2+(p-1)t-1\) are irreducible by the rational root test. Work in \(K=\mathbb Q[t]/(A(t)-1)\) with basis \(1,t,t^2\) and positive embedding \(t\mapsto\alpha\).

For any \(m\) define \(S_{m,j}\) as the sum of \(2j\)-th powers of the centered indices of \(C_m\). Taking a normalized logarithm in (3), or expanding the pairs of opposite linear factors, gives the formal identity for the branch
\[
 A(T)=(1+u/2)^3
 \exp\!\left(\sum_{j\ge1}\frac{u^{2j}}{2j}
 \left[
     \frac{S_{pd,j}/d}{(1+T)^{2j}}
    +\frac{S_{qd,j}/d}{T^{2j}}
    -\frac{S_{3d,j}/d}{(1+u/2)^{2j}}
 \right]\right).
\tag{4}
\]
It uniquely determines \(T=t+\sum_{j=1}^6 c_j u^j+O(u^7)\) in the cubic field, since \(A'(t)\ne0\); the recurrence divides by \(A'(t)\) at each next order and the right-hand dependence on that next coefficient is offset by \(u^2\). For the three moments required here, \(S_{kd,j}/d\) is respectively
\[
 \frac{k(k^2\xi-1)}{12},\qquad
 \frac{k(k^2\xi-1)(3k^2\xi-7)}{240},\qquad
 \frac{k(k^2\xi-1)(3k^4\xi^2-18k^2\xi+31)}{1344}.
\]
These are finite centered power sums. It follows inductively from the series operations that \(\deg_\xi c_j\le\lfloor j/2\rfloor\): inversion of a series with constant term in \(K^\times\) preserves this filtration, as do products; each new moment of degree \(j\) is offset by \(u^{2j}\).

## 2. A fixed polynomial certificate for every \(d\)

Put \(H=(W+Y)^pY^q-W^3\). For each monomial \(B\) in the ordered list \(1,W,Y,W^2,WY,Y^2\), begin with \(HB\) and substitute \(Y=WT\). To its coefficient at successive powers \(W^j\) for \(j\ge0\), subtract the homogeneous polynomial \(\sum_{i=0}^{\min(j,2)}b_i W^{j-i}Y^i\), choosing the \(b_i\) from the coordinates of that coefficient in the cubic basis. This kills the whole leading term for \(j\ge2\); it can leave only a \(t^2 W\) coordinate at \(j=1\), and \(t,t^2\) coordinates at \(j=0\). Each subtraction also changes lower terms, which are recomputed. Denote the resulting polynomial by \(P_B\), and let \(M(\xi)\) be the matrix with columns its six residual coordinates: these three nonnegative-power coordinates, followed by all three coordinates at \(W^{-1}\).

All entries can be constructed through order six in (4). For a column with \(\deg B=m\), an entry at power \(W^j\) has degree in \(\xi\) at most \(\lfloor(3+m-j)/2\rfloor\), by the series filtration and the successive subtractions. Direct rational substitution gives \(M(1)=0\); in particular \(M(\xi)/(\xi-1)\) has polynomial entries.

Number the six columns from 0. For \((p,q)=(1,2)\) take \(J=(0,1,2,3)\); for \((2,1)\) take \(J=(0,2,3,4)\). In the first three rows of \(M/(\xi-1)\) restricted to \(J\), form the signed maximal minors \(v_i=(-1)^i\det(\text{delete column }i)\), where \(i=0,1,2,3\) is the index inside \(J\). Then the polynomial \(P=\sum_i v_i P_{B_{J_i}}\) has all three nonnegative-power residuals zero. Its coefficient \(\ell(\xi)\in K\) at \(W^{-1}\) is the last three rows of \(M\) in that same combination. The degree bounds give that the ordinary coefficients of \(P\) have \(\xi\)-degree at most 4 and \(\ell\) at most 5. To see the former explicitly, a minor \(v_i\) for a removed constant column has degree at most 3, and for a removed column of degree 1 or 2 at most 2; adding the degree of the homogeneous correction at power \(j\ge0\) gives at most 4. This also gives the latter bound at \(j=-1\).

The accompanying exact checker constructs these polynomials by interpolation at \(\xi=2,\ldots,7\), justified by the degree bounds. For the positive embedding of \(K\), it checks that **all six coefficients** of \(\ell(4+s)\), from the constant term to \(s^5\), are strictly positive. For these checks one can bound \(\alpha\) between \(3/4\) and \(19/25\), respectively between \(23/50\) and \(47/100\); the endpoint inequalities for \(A\) are rational. Scale by \(L=48922361856000\), a multiple of 32 times the common denominator of the coefficients of \(P\) for either case. Thus \(L P\) takes integer values on every relevant half-integer pair \((W,Y)\). From the positive coefficient bounds and simple absolute coefficient sums, the checker verifies
\[
 \delta d^{10}\le L\,\ell(d^2)\le K_0 d^{10},\qquad
 \big|u^5 L\,P(1/u,T/u)\big|\le B_0 d^8
 \quad (|u|\le1,\ |T|\le21/20).
\tag{5}
\]
Here the second inequality is understood after evaluating its polynomial in \(u,T\); no pole is included. Exact constants, for the two cases in order, are:
\[
\begin{array}{c|r|r|r}
(p,q)&B_0&K_0&\delta\\ \hline
(1,2)&99142638469120&2116034336000/189&1132359841125/131072\\
(2,1)&100482568439808&2530468219904/63&10970523581697/163840
\end{array}
\]
For the lower bound, split \(4\le\xi\le8\) (use the constant coefficient) and \(\xi\ge8\) (use the coefficient of \(s^5\) and \(s=\xi-4\ge\xi/2\)); the code makes these same rational tests. The upper bound just sums the absolute values of the coefficients, using \(|\alpha|<1\).

The full residual matrix has the additional invariant
\[
 \det M(\xi)=\frac{(\xi-1)^6 R(\xi)}{D_0}
\]
for explicit degree-eight polynomials \(R\) given in the verifier and positive rational denominators \(D_0\). It suffices to interpolate at 15 points because the determinant degree is at most \((26-(-2))/2=14\): the sum of column weights \(3+m\) is 26, and the sum of row powers \(j\) is \(-2\). All coefficients of \(R(4+s)\) are positive in both cases. This shows the stated no-low-degree-relation result. Indeed, divide any proposed polynomial of degree at most five by the monic-in-\(Y\) cubic \(H\). For each quotient \(Q\) of degree at most two the unique possible remainder canceling every removable nonnegative power is the one produced by the above subtractions. An identity on the branch would force all six residuals to vanish; invertibility gives \(Q=0\), and then the successive leading-term tests give zero remainder.

## 3. Uniform control beyond the formal series

On the complex circle \(|t-\alpha|=1/20\), the modulus of \(A(t)-1\) is at least \(299/8000\): its linear part has modulus at least \(1/20\), and the quadratic and cubic pieces have absolute sum at most \(5/400+1/8000\). Let \(|u|\le \rho=1/(1024d)\). The right side of (4) is analytic on this whole \(t\)-disk, using the logarithms of the paired centered factors. Each argument \(j u /v\) in those factors has modulus less than \(1/100\): the three possible \(v\)'s are \(t,1+t,1+u/2\), all of modulus at least \(17/60\), and \(|j|\le3d/2\). Thus the logarithm of each factor \(1-(j u/v)^2\) has modulus less than \(1/9999\), and the total normalized logarithmic correction has modulus at most \(6/9999<1/1000\). Also \(|(1+u/2)^3-1|<1/500\). The right side differs from 1 by less than \(1/100\). Rouché's theorem gives one simple root in the fixed \(t\)-disk; it is holomorphic in \(u\) and bounded by \(21/20\). For real positive \(u\le\rho\) this root gives \(y\ge0\) and agrees with the unique solution in (3), so the formal series is genuinely its Taylor expansion.

The function \(u^5L P(1/u,T(u)/u)\) has zero coefficients through degree five and coefficient \(L\ell(\xi)\) at degree six. For \(W\ge2/\rho\), Cauchy's coefficient bounds using (5) give
\[
 \left|L P(W,Y)-\frac{L\ell(d^2)}W\right|
             \le \frac{2B_0\,1024^7 d^{15}}{W^2}.
\]
For \(W\ge 10^{29}d^{10}\) the remainder is strictly less than half the leading term, and the sum is less than 1. The sufficient numerical inequalities are \(10^{29}>2K_0,\ 10^{29}>4B_0\,1024^7/\delta,\ 10^{29}>2048\); the code checks them exactly. Thus \(LP(W,Y)\) is a nonzero real number of absolute value less than 1, contradicting its integer value. Since \(n=z+y\le2z=2W+3d\), this proves (2).

## 4. Complete enumeration for \(d=2,3\)

Four smaller frozen degree-five Runge certificates are included in a separate checker, based directly on the uncentered polynomial \(F(z,y)\) of (3). For each one, its quintic \(G(z,y)\) tends to zero on the positive branch: independently expand \(F(z,y)/z^{a+b}\) in \(u=1/z\), \(t=y/z\), solve successive coefficients modulo the corresponding cubic, and verify that \(u^5 G\) vanishes through degree five. Then compute the three univariate resultants \(\operatorname{Res}_y(F,G+s)\) for \(s=-1,0,1\). After translating \(z\) by the indicated bound, every coefficient of each resultant is of one strict sign, excluding their real zeroes there. By continuity \(G\) cannot reach either \(-1\) or \(1\) beyond the bound, since it tends to 0. As \(G\) also cannot equal 0 there, no integer point is possible in the tail.

| \((a,b)\) | certified tail starts at \(z\) | all integer \((n,k)\) |
|---|---:|---|
| \((2,4)\) | 13,600,000 | \((6,0)\) |
| \((4,2)\) | 3,900,000 | \((6,0)\) |
| \((3,6)\) | 842,000 | \((9,0)\) |
| \((6,3)\) | 1,070,000 | \((9,0)\) |

For the remaining integer scan, increasing \(z\) never decreases the least integer \(y\) at which the right side reaches the left (by the monotone positive branch). Updating both products by exact adjacent factorial ratios allows one forward scan, and every equality is checked against the products themselves. No numerical roots, guesses about irreducibility of the full curve, or bounds on unseen branches are needed.

**Reproduction (Python and SymPy).** `python3 verify_singmaster_unequal_uniform.py --determinants` checks the uniform constants and all determinant data; `python3 verify_singmaster_unequal_four_cases.py` checks the four small tail certificates and exhausts the finite ranges. Use `--tail-only` for the latter program to skip the scan.
