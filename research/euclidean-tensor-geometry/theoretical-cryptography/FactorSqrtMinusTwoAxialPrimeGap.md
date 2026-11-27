# A real-axis exclusion for maximal \(\mathbb Z[\sqrt{-2}]\) prime components

Let \(R=\mathbb Z[\sqrt{-2}]\) and use the graph on its irreducible elements, counted as elements, with Euclidean radius \(\sqrt6\le D<\sqrt8\). Write \(a+b\sqrt{-2}\) as \((a,b)\). The step set is
\[
 F=\big(\{-2,-1,0,1,2\}\times\{-1,0,1\}\big)\setminus\{(0,0)\}.
\]
Existing bounds for the unrestricted largest component are \(90\le B_D\le197\).

**Results.** If a component has 197 vertices and meets the real axis \(b=0\), then **every** vertex in it has \(|a|>10^{33}\). This is an unconditional statement only for components meeting that axis. It does not improve the unrestricted lower endpoint or affirm that any such component exists. The restriction from rational primes at most 197 and the necessary inert residue modulo 8 has exact first possible distance
\[
 3007922280545518952833377.
\]
This is a congruence candidate, not a prime example.

There is a specific admissible Schinzel-H family of **98 small-coefficient irreducible quadratic polynomials and one linear polynomial** which, if simultaneously prime once at a positive input, gives \(B_D=197\). Minimality of 99 here refers to the number of distinct norm-polynomials of the fixed 197-point shape under any nonconstant one-parameter affine translation, not to the complexity of proving their simultaneous primality.

## 1. Which candidates can meet the real axis?

We import the four residue classes established in the [earlier maximal-component classification](FactorSqrtMinusTwoMaximalPrimeStrip.md). It applies to every actual 197-component, because exceptions to the sieve lie in a closed 90-component. In particular, we do not count the four classes, their unique shape, or the earlier arbitrary-height vertical-strip bound as new here.

Use the [literal 197-point pattern](https://github.com/mxym/math/blob/main/notes/sqrt-minus-two-universal-sieve-barrier/code/connected_shape.json) \(S\) of the original sieve note. In these coordinates its \(a\)-range is \([369,413]\), its \(b\)-range is \([-34,34]\), its unique \(b=0\) point is \((389,0)\), and the remaining 196 points pair under \(b\mapsto-b\). It is enough up to horizontal reflection to use the prior two classes with anchor \(a\bmod Q=455654487987\), where \(Q=742840526010\). Their vertical anchor residues are \(-29\) and \(Q/2-29\). The literal shape has lexicographic anchor \((369,-29)\); the checker verifies that its translate by \((455654487618,0)\) is an entire component of the \(Q\)-sieve, so this is exactly the orientation of those two classes. Their vertical translation coordinates are \(0\) and \(Q/2\) modulo \(Q\). No nonzero permissible vertical translation can give a point on the real axis, since \(|b|\le34\) throughout \(S\).

Thus each actual 197-component meeting the real axis is, up to horizontal reflection, \(S+(h,0)\) for
\[
 h=H+Qk,\qquad H=455654487618,\quad k\in\mathbb Z.
\]
Its closest real-coordinate distance is \(h+369\) if \(h>0\) and \(-h-413\) if \(h<0\); the residue class guarantees these signs consistently throughout the component. All vertices in any such candidate have \(|a|\ge287186037979\), already from the \(Q\)-class. Hence for any rational prime \(p\le997\) there can be no exception to a norm divisibility test from prime norm \(p\) or an inert axis unit multiple of \(p\).

Off the real axis an irreducible has rational-prime norm; a rational integer is irreducible here exactly when its absolute value is a rational prime inert in \(R\), i.e. congruent to 5 or 7 modulo 8. These facts follow from norm-Euclideanity and the splitting character for \(-2\). Consequently the axis imposes \(|h+389|\bmod 8\in\{5,7\}\), and the local condition at \(p\le997\) is \(h\bmod p\in L_p\), where
\[
 L_p=\{r\bmod p:\ r+389\ne0,\ 
             (r+a)^2+2b^2\ne0\text{ for every }(a,b)\in S,\ b>0\}.
\]
All entries here are considered in \(\mathbf F_p\), including \(r+389\). The other sign of each \(b\) has identical norm.

## 2. Exact restricted range exclusion

The accompanying checker computes \(L_p\) in two different ways, by literal polynomial values and by taking the complement of the explicit roots \(-a+b\sqrt{-2}\) in \(\mathbf F_p\) (with root \(-a\) when \(b=0\bmod p\)). The axis term forbids \(-389\). In both cases \(Q\)'s prime divisors are already satisfied by \(H\).

For seven thin primes the counts are:
\[
\begin{array}{c|rrrrrrr}
p&7&73&83&89&97&107&113\\ \hline
|L_p|&1&1&3&7&9&10&15.
\end{array}
\]
With \(k=(h-H)/Q\), the resulting CRT seed consists of 28,350 classes modulo \(m=4427136928039\). For the first possible distance using primes through 197, check the two periods \([-m,m-1]\) by retrieving \(k=r-m\) and \(k=r\) for each CRT residue \(r\). After testing the required modulo-8 rule, 28,525 admissible-sign indices are tested at the remaining primes through 197. Exactly one passes, \(k=4049216723139\). Both exterior tails have strictly larger distances. This verifies the stated exact minimum for this finite congruence condition.

To exclude distances at most \(R_0=10^{33}\), it is necessary and sufficient at the coordinate level to test
\[
 \left\lceil\frac{-R_0-H-413}{Q}\right\rceil
 \ \le k\le\
 \left\lfloor\frac{R_0-H-369}{Q}\right\rfloor
\]
for the intersection of the candidate's 44-wide real range with \([-R_0,R_0]\). Incorporate 131 and 137 (each with 21 permitted residues) into the CRT seed; this gives \(28\,350\cdot21^2=12\,502\,350\) classes modulo \(M=79453826447515933\). For every such residue \(k_0\in[0,M)\), write \(k=k_0+Mj\). The quotient \(j\) ranges from \(-16943\) to \(16942\), with an exact clip on \(k\) at the ends. For each remaining test prime \(p\), membership depends only on \(k_0\bmod p\) and \(j\bmod p\); to encode permitted \(j\)'s take the mask of positions
\[
 j\equiv M^{-1}(u-k_0)\pmod p,\qquad
 u\in Q^{-1}(L_p-H)\subset\mathbb F_p .
\]
Intersect the exact bitmaps for the nine primes \(139,179,163,193,211,227,233,251,241\), clip the range, and test the modulo-8 rule and every remaining prime \(p\le997\). The bitmaps retain 9,230,230 candidate indices before clipping, 9,230,213 within the interval, and 4,617,134 after the inert residue rule. There are no surviving indices. This computation is a modular exclusion, not a failed search for primality. Every necessary congruence is checked on every retained residue or quotient. The checker also verifies its bitmap expression by direct modular evaluations for the entire quotient window at several residues of each bitmap prime.

Run `python3 -B verify_factor_sqrt_minus_two_axial_gap.py` or the same command with `-O`. The companion includes the pinned 197 coordinates, uses integers and rational numbers only, and requires no solver or external packages. The full range may take several minutes; the `--short` option replays the same construction through \(10^{29}\) with its own expected counts.

## 3. A smaller conditional family, not a witness

For positive integers \(n\) set \(h=8n\). With \(S^+=\{(a,b)\in S:b>0\}\), the family is explicitly
\[
 g_0(n)=8n+389,\qquad
 g_{a,b}(n)=(8n+a)^2+2b^2\quad((a,b)\in S^+).
\]
There are 98 quadratics; each has negative discriminant and all are distinct (compare the linear and constant coefficients). Coefficients are all less than 200,000 in absolute value. The linear term, if prime, is \(5\bmod8\) and hence inert. The quadratic values provide all 196 remaining irreducibles in mirror pairs. Strictly positive rational-prime values give a connected 197-point set, necessarily a full component by the known upper bound. One such input would settle the unrestricted maximum at 197.

The product has no fixed rational prime divisor. At \(p=2\), every polynomial is odd. At odd \(p\le197\), multiplication by 8 is invertible and the exact sets \(L_p\) are nonempty. At \(p>197\), the product has nonzero leading coefficient and degree \(1+2\cdot98=197<p\). Thus [Schinzel's Hypothesis H](https://doi.org/10.4064/aa-4-3-185-208) for this smaller family would give infinitely many actual 197-components meeting the real axis. This differs from the earlier 197-quadratic, large-coefficient conditional construction, which allowed arbitrary vertical positions. The hypothesis does not make the first congruence candidate in §2 prime.

For completeness, under any nonconstant affine translation \(z\mapsto z+w+nv\) in the coefficient plane, the polynomial \(N(z+w+nv)\) determines both the inner product of \(z+w\) with \(v\) and the squared norm of \(z+w\), for the quadratic form \(a^2+2b^2\). The intersection of a line perpendicular to \(v\) and a fixed-norm ellipse contains at most two points. Thus a class of coincident norm-polynomials has size at most two, and a 197-point fixed shape needs at least 99 distinct norm-polynomials in any such representation. The real-axis mirror pairing attains this bound, with the one square norm replaced by the appropriate linear inert-prime condition.

This is a refinement for one symmetry location of the \(\mathbb Z[\sqrt{-2}]\) graph, not a claim about general Gaussian moats or the true unrestricted maximum. Related methods are [Prasad's imaginary quadratic walks](https://arxiv.org/abs/1412.2310) and [OpenAI's Gaussian moat preprint](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Bounded-Step-Walks-on-Gaussian-Primes-September-26-2026). Dilation-allowing [number-field prime constellation theorems](https://arxiv.org/abs/2012.15669) do not supply the fixed unit-dilation realization used here.
