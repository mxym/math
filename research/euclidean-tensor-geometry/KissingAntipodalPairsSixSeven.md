# Near-antipodal kissing codes in dimensions six and seven

**Theorem.** A kissing configuration in \(\mathbb R^6\) with at least 29 antipodal pairs has at most 72 points. A kissing configuration in \(\mathbb R^7\) with at least 56 antipodal pairs has at most 126 points. Both cardinality ceilings are achieved by the respective root systems, but the pair criteria are not asserted optimal. Thus any improvement over either root-system configuration must have at least seventeen unpaired points. No unrestricted upper-bound improvement is claimed.

## Classical positive kernel, used with two weights

For \(X\subset S^{n-1}\) with distinct pairwise inner products at most \(1/2\), call \(p\) the number of whole antipodal pairs, choose one representative of each, and call the other points singletons. Work with \(f(t)=t^4-t^2/4\). Its Gegenbauer expansion has constant \(c_0=(10-n)/(4n(n+2))\) and nonnegative coefficients in positive degrees when \(n=6,7\). Indeed, with the normalized spherical zonal polynomials
\[
 P_2(t)=\frac{nt^2-1}{n-1},\qquad
 P_4(t)=\frac{(n+2)(n+4)t^4-6(n+2)t^2+3}{(n-1)(n+1)},
\]
the coefficients are \(c_2=(6/(n+4)-1/4)(n-1)/n\) and \(c_4=(n-1)(n+1)/((n+2)(n+4))\). Positivity of the harmonic Gram matrices therefore gives, for all real weights \(w_i\),
\[
 \sum_{i,j}w_iw_j f(x_i\cdot x_j)\ \ge\ c_0\left(\sum_i w_i\right)^2 .
\]
This is the ordinary [Delsarte–Goethals–Seidel spherical-code kernel method](https://doi.org/10.1007/BF03187604). The fully antipodal bounds, including 72 in dimension 6, are classical; see [Anstreicher, Table 1](https://optimization-online.org/wp-content/uploads/2001/01/248.pdf).

Put \(P=f(1)/c_0=3n(n+2)/(10-n)\), equal to 36 or 63. Any set of unit vectors with absolute pairwise inner products at most \(1/2\) has at most \(P\) elements, since all its off-diagonal \(f\)-values are nonpositive. In particular \(p\le P\). Between pair representatives, and between a pair representative and any singleton, the absolute bound holds because both signs of the representative are present in \(X\).

Suppose \(|X|\ge2P+1\) but \(p\ge P-4\). Put \(s=P-p\); when \(s=0\) a single extra singleton violates the absolute bound just proved. For \(1\le s\le4\), retain any \(q=2s+1\) singletons. Make a graph on these \(q\) vertices, with an edge \(ij\) when \(x_i\cdot x_j<-1/2\). Its independence number is at most \(s\) by adjoining the corresponding singletons to the \(p\) representatives. It is triangle-free, since for three mutually adjacent points their sum would have negative squared norm. Hence its maximum degree is at most \(s\) (a neighborhood is independent).

Let \(H=\sum_i\sum_{j\sim i}f(x_i\cdot x_j)\) be the ordered edge weight. In the harmonic inequality give representatives weight 1 and singletons weight \(\alpha=s/q>0\), and discard nonpositive terms. Since \(p+q\alpha=P\), this gives
\[
 c_0P^2\le \tfrac34(p+q\alpha^2)+\alpha^2H,
 \qquad H\ge \tfrac34(q^2/s-q).
\]

## Exact local Gram maxima

Let \(k\) neighbors \(y_i\) of one vertex \(x\) be given, and put \(a_i=-x\cdot y_i\in[1/2,1]\). The local sum is \(\sum_i f(a_i)\). For any vector of nonnegative weights \(w\),
\[
 (w\cdot a)^2\le\left\|\sum_iw_iy_i\right\|^2
 \le w^\mathsf TC_kw,\qquad C_k=(I+J)/2 .
\]
The last inequality uses only \(y_i\cdot y_j\le1/2\). Minimize \(b^\mathsf TC_k^{-1}b\) over \(b\ge a\). At its unique minimizer, \(w=C_k^{-1}b\ge0\) and \(w_i(b_i-a_i)=0\), as follows by the feasible directional derivative in each coordinate. Thus \(w\cdot a=w\cdot b=w^\mathsf TC_kw\), and the displayed inequality implies \(b^\mathsf TC_k^{-1}b\le1\). In particular every \(b_i\le1\) by evaluation of the \(i\)th coordinate on this ellipsoid. The polynomial \(f\) increases on \([1/2,1]\), so it suffices to optimize the larger objective \(\sum_i f(b_i)\) on that ellipsoid intersected with \(b_i\ge1/2\).

For \(k=1\) the maximum is \(3/4\). For \(k=2\), the ellipsoid means one can realize the \(b_i\) as cosines of angles from a unit pole to two unit directions having mutual inner product \(1/2\): take a pair with Gram \(C_2\) and solve for the pole's projection, whose squared norm is \(b^\mathsf TC_2^{-1}b\). Thus the two angles \(\theta,\phi\) to the pole satisfy \(\theta+\phi\ge\pi/3\). The objective is maximal on \(\theta+\phi=\pi/3\); there it is \(5/8+3u/8-u^2/4\) for \(u=\cos(2\theta-\pi/3)\), at most \(49/64\).

For all \(k\ge3\), the exact maximum on the ellipsoid is
\[
 M_k=\frac{(k+1)(k+2)}{8k}.
\]
For the induction, if any \(b_i=1/2\), discard it as it contributes zero. The remaining coordinates lie in the ellipsoid corresponding to the principal submatrix of \(C_k\), as follows by Cauchy–Schwarz applied to linear functionals supported there. The bounds for smaller dimensions are strictly smaller than \(M_k\): \(M_3>49/64\), and \(M_j\) is increasing for \(j\ge3\).

If all \(b_i>1/2\), the ellipsoid constraint is active by coordinatewise monotonicity. Lagrange stationarity for \(2(\sum b_i^2-(\sum b_i)^2/(k+1))=1\) shows each entry is a root of
\[
 4z^3-(1/2+4\lambda)z+4\lambda(\sum b_i)/(k+1)=0 .
\]
The multiplier \(\lambda\) is positive by taking the scalar product of the stationarity equations with \(b\). The cubic has at most two positive roots; if there are two distinct roots the larger has positive derivative. The larger cannot occur twice: the tangent variation \(e_i-e_j\) on two such coordinates has positive second derivative of the Lagrangian (the rank-one all-ones term vanishes on this direction), contradicting the second-order necessary condition.

When all coordinates are equal, the constraint gives \(b_i^2=(k+1)/(2k)\) and sum \(M_k\). Otherwise write \(k-1\) entries as \(t\) and the single larger one as \(rt\), where \(1<r\le2\) because all entries lie in \([1/2,1]\). Put \(E=kr^2-2(k-1)r+2(k-1)\). The constraint gives \(t^2=(k+1)/(2E)\), and the sum is \(F=t^4(r^4+k-1)-\frac14t^2(r^2+k-1)\). With \(u=r-1\), direct expansion gives
\[
 8kE^2(M_k-F)=u^2(k^2-1)\bigl(3k^2-4k-8-2ku+k(k+2)u^2\bigr)>0 .
\]
Indeed \(0<u\le1\) and \(3k^2-6k-8>0\) for \(k\ge3\). This completes the optimization. The equal case is realizable when the ambient space has dimension at least \(k\): take \(k\) unit neighbors with Gram \(C_k\) and take the negative pole in the direction of their sum. The calculation is dimension-independent for the upper bound. It is a local cap estimate of the kind motivated by [Musin's extension of the LP method](https://annals.math.princeton.edu/wp-content/uploads/annals-v168-n1-p01.pdf).

## Exclude the four singleton cases

For \(s=1\), the three-vertex graph with independence number at most 1 would have a triangle. For \(s=2\), its degree is at most 2; hence \(H\le5(49/64)<45/8\), contrary to the weighted bound. For \(s=3\), it has degree at most 3; hence \(H\le7(5/6)<7\).

For \(s=4\) the graph has nine vertices and degree at most four. It cannot be 4-regular: if bipartite one side has at least five vertices, and otherwise a shortest odd cycle has length \(\ell\in\{5,7,9\}\) and is induced. A 4-regular graph would need \(2\ell\) edges from that cycle to its complement, but each of the \(9-\ell\) external vertices has at most \(\lfloor\ell/2\rfloor\) neighbors in the cycle because the graph has no triangles. The resulting upper bound is smaller than \(2\ell\) for each listed \(\ell\). Thus there is one vertex of degree at most three. Consequently
\[
 H\le 8(15/16)+5/6=25/3<135/16,
\]
again contrary to the weighted bound. This proves the claimed ceilings for \(p\ge P-4\) without computation.


## Three additional pair deficits via an odd correction

For \(s=5,6,7\), use the degree-four polynomial
\[
 F(t)=f(t)+\lambda\,t(t^2-1/4)+\mu t,\qquad
 (\lambda,\mu)\in\{(7/20,0),(49/100,0),(49/100,9/500)\},
\]
respectively. The polynomial \(t(t^2-1/4)\) has nonnegative harmonic coefficients in degrees 1 and 3: \(P_3(t)=((n+2)t^3-3t)/(n-1)\) and \(3/(n+2)-1/4>0\). Thus the same positive kernel sum holds for \(F\) with constant \(c_0\). Instead of keeping one representative per pair, now keep both and give each weight \(1/2\). Their odd contributions cancel exactly in all terms involving an antipodal pair (including its own four ordered terms), while the even contribution is unchanged. Only the singleton block sees the modified polynomial. As before retain \(q=2s+1\) singletons and give them weight \(s/q\). Since \(F(1)=\tfrac34(1+\lambda)+\mu\), the same weighted calculation now gives
\[
 \frac{1}{q}\sum_{i\ne j \text{ singletons}}F(x_i\cdot x_j)
  \ \ge\ \frac34(1+1/s-\lambda)-\mu .
\]
The graph of singleton inner products below \(-1/2\) is still triangle-free and has maximum degree at most \(s\). In the \(s=6,7\) steps it has minimum degree at least 2 by induction: for a singleton of degree 0 or 1, add its antipode and discard its one negative neighbor if present. This keeps at least \(2P+1\) points, produces at least \(p+1\) pairs, and violates the preceding deficit case. It preserves the kissing inequalities because the only potential incompatibilities with the new antipode were precisely its negative neighbors, and both signs of every old pair were already present.

The companion [verify-kissing-antipodal-tail.js](verify-kissing-antipodal-tail.js) gives the following exact bounds. In its last column \(B_d\) bounds the sum of \(F(-a_i)\) over the \(d\) neighbors of one vertex; \(d=0\) always has sum zero. The symbol \(\gamma\) bounds \(F(t)\) on the entire nonedge interval \([-1/2,1/2]\).

| Deficit \(s\) | \(\gamma\) | degrees certified | \(1000 B_d\), in the listed degree order |
|---|---:|---|---|
| 5 | \(49/6400\) | 1, 2, 3, 4, 5 | 490, 550, 570, 580, 590 |
| 6 | \(49/4000\) | 2, 3, 4, 5, 6 | 384, 396, 409, 421, 433 |
| 7 | \(9/1000\) | 2, 3, 4, 5, 6, 7 | 363, 372, 381, 390, 399, 408 |

Here is why the verifications are exhaustive. For \(t\in[0,1/2]\), \(F(t)\le\mu/2\). At \(t=-a\), \(a\in[0,1/2]\), \(F(-a)=a(\lambda-a)(1/4-a^2)-\mu a\), which is nonpositive for \(a\ge\lambda\). For \(a\) in each interval of length \(1/65536\) below \(\lambda\), bound the three nonnegative factors by their indicated upper endpoint bounds, and subtract \(\mu\) times the interval's lower endpoint. This directly verifies \(\gamma\). For the cap bound, order the neighbor projections \(a_1\ge\cdots\ge a_d\) in \([1/2,1]\) and split this sorted cubical domain into dyadic boxes. Let \(\ell\) be the lower endpoints of any leading \(j\) coordinates. If \(C_j^{-1}\ell\ge0\) and \(\ell^\top C_j^{-1}\ell>1\), the box is impossible: the nonnegative weight \(w=C_j^{-1}\ell\) would violate \((w\cdot a)^2\le w^\top C_j w\) throughout it. Those checks are exact quadratic integer inequalities. For each remaining box, bound \(F(-a_i)\) by its larger endpoint value because \(F(-a)\) is convex for \(a\in[1/2,1]\), as \(12a^2-\tfrac12-6\lambda a>0\) there for these \(\lambda\). Accept if the objective upper bound is at most \(B_d\), otherwise split the largest remaining interval. No unverified box remains. With denominator 65536, the quadratic operations use integers of absolute value below \(2^{53}\), and the verifier uses BigInt for all quartic comparisons. It checks the exact visit counts, including the largest tree of 136,533 nodes.

A row of degree \(d\) now has total off-diagonal score at most \(B_d+(2s-d)\gamma\). The table gives a strict inequality between this bound and \(\frac34(1+1/s-\lambda)-\mu\) for every allowable \(d\) in each deficit, including \(d=0\) when \(s=5\). This contradicts the required average row score successively for \(s=5,6,7\). Thus \(p\ge P-7\) indeed forces \(|X|\le2P\).

The six-dimensional unrestricted lower bound remains 72; [de Laat–Leijenhorst–de Muinck Keizer](https://arxiv.org/abs/2404.18794) prove the general upper bound 77, and [Tomar's later preprint](https://www.mefyi.com/papers/kissing-numbers-five-seven/) reports an exact rational certificate for 76. The pair condition here is distinct from [specified exact hyperplane sections](https://www.preprints.org/manuscript/202610.0335) and from recent [dimension-five antipodal-pair SDP constraints](https://aixiv.online/abs/2611.02115). A targeted prior-art search did not establish priority for these specific dimension-six and -seven thresholds.
