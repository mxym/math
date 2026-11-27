# The largest unique Walsh-support cardinality is 21

## 1. The question and its quantifiers

Write \(V_n=\mathbb F_2^n\) and
\[
 \widehat f(u)=2^{-n}\sum_{x\in V_n}(-1)^{f(x)+u\cdot x},
 \qquad S_f=\{u:\widehat f(u)\ne0\}.
\]
A cardinality \(r\) is *admissible* if \(|S_f|=r\) for a Boolean function \(f:V_n\to\mathbb F_2\) in some finite \(n\ge1\); affine/constant functions are allowed, and give exactly \(r=1\). We count \(r\) as *unique* if it is admissible and any two such supports are related by an affine bijection of their affine hulls mapping one set onto the other. This is the across-dimensions convention of Jauberty–Méaux (JM), Definition 8. It is not EA equivalence of Boolean functions themselves. An invertible affine change of input variables and the addition of an affine Boolean function map the Walsh support by an affine isomorphism, so EA equivalence implies support equivalence but the implication need not be reversed.

**Theorem.** The largest unique admissible cardinality is \(21\). Every Walsh support of cardinality \(21\) has affine dimension \(5\) and the support of the representative specified in [RESULTS.txt](RESULTS.txt) is a model for its affine shape. For each integer \(r\ge22\), there are at least two inequivalent Walsh-support shapes of that cardinality. Equivalently, for each \(r\ge22\) there is \(N(r)\) such that the two shapes are realized in every ambient dimension \(n\ge N(r)\). No claim is made that both shapes fit in the smallest ambient dimension where \(r\) is attainable.

The target is the first Open Question in §8 of the [version of JM pinned here](https://opencryptology.org/2025/1651/versions/20260428T172000Z.pdf). See [UPSTREAM.md](UPSTREAM.md) for exact dependencies and literature scope.

## 2. Two general operations

**Reduction and padding.** A modulation \(f(x)\mapsto f(x)+a\cdot x\) translates \(S_f\) by \(a\), so we can first put the affine hull through \(0\). Change linear input coordinates so the resulting spectral span of dimension \(d\) is the first \(d\) frequency coordinates. Fourier inversion now shows \((-1)^{f(x)}\) is a function only of the first \(d\) input coordinates. Thus the Boolean function is EA-equivalent to a function on \(d\) variables padded by unused coordinates. The normalized magnitudes and affine shape do not change under padding or this reduction. This is the property of reduction from JM Theorem 2 used here (and also proves it in the form needed here).

**Joining.** For \(h(x,0)=f(x)\), \(h(x,1)=g(x)\) on \(n+1\) input variables,
\(\widehat h(u,b)=(\widehat f(u)+(-1)^b\widehat g(u))/2\).
Write \(s=|S_f|\le t=|S_g|\), \(k=|S_f\cap S_g|\), and let \(\xi\) count the shared frequencies with equal absolute normalized coefficients. Each frequency \(u\) in the union gives a full two-point fiber unless it is counted by \(\xi\), in which case one point of that fiber remains. In particular the support projects onto the union and
\[
 |S_h|=2(s+t)-2k-\xi,\qquad 0\le\xi\le k\le s.
\]
This is the joining identity of JM Theorem 1 in §3 (interchanging \(f,g\) when necessary does not alter the sizes). JM Lemma 1 also rules out \(s<t,\xi=s\) and \(s=t=k,\xi=k-1\): in the first case \(g\) would have the same sum of squared magnitudes as \(f\) on all of \(S_f\), plus additional nonzero terms; in the second case only one squared magnitude differs. Both contradict Parseval, which gives total \(1\) for each function. For any \(n>1\) the restriction on the last input bit gives such a join.

If \(k>0\), the affine intersection of the two support hulls has dimension at least \(\lceil\log_2 k\rceil\), since it contains \(k\) distinct points. Thus, if the hull dimensions are \(d_s,d_t\), the union has affine dimension at most \(d_s+d_t-\lceil\log_2 k\rceil\). The new support has dimension at most that bound plus one. Conversely, if some \(u\) has a full fiber in \(S_h\), the affine dimension of \(S_h\) is exactly \(1+\dim\operatorname{aff}(S_f\cup S_g)\): the projection maps affinely onto the union hull and the kernel in its direction space has dimension one.

## 3. Uniqueness at 21

### Six-variable starting data

JM §5, Table 1 reports one EA class for size \(21\) and one for size \(18\) among six-variable functions. We replay the independent complete catalogue of Langevin (classified under \(\operatorname{AGL}(6,2)\) modulo \(RM(1,6)\), exactly EA), obtaining one representative of each size and affine dimension \(5\) for each. See the exact record locators, Walsh scans and byte checks in [RESULTS.txt](RESULTS.txt). This establishes the base for all \(n\le6\) by padding. The scan also gives the size-\(18\) nonzero absolute *normalized* magnitudes
\[
        14\text{ of }1/8,\quad 2\text{ of }3/8,\quad 2\text{ of }1/2 .
\]
These magnitudes hold for all \(n\) by the size-\(18\) dimension result of JM Appendix A.4 and reduction/padding to six variables. Using a unique affine support shape alone would not justify those magnitudes; the six-variable EA classification does.

### Exhaustive joining cases

Take \(n>6\) and suppose the size-\(21\) result holds up to \(n-1\). Write \(f,g\) for the restrictions of a size-\(21\) function. The join formula gives \(21\ge2t-s\ge t\). If \(t=21\), necessarily \(s=t=k=\xi=21\), since equality forces \(s=t\) and \(2k+\xi=3s\). The two support sets are equal, and by induction have affine hull dimension \(5\); the joined support therefore has affine dimension at most \(6\).

If \(t<21\), JM §6 Corollary 8 eliminates the twelve disallowed sizes below \(20\) (and Parseval eliminates zero support). The only candidate individual sizes are \(1,4,8,10,13,16,18,20\). All integer tuples passing the join cardinality equation and the bounds on \(k\) and \(\xi\) are listed below, including the one excluded by the Parseval conditions. The table lists **arithmetic candidates before any geometric constraints**, not asserted realizations.

| \(s,t\) | all \(k,\xi\) | upper bound on joined affine dimension or exclusion |
|---|---|---|
| \(4,8\) | \((1,1)\) | \(6\) |
| \(4,10\) | \((3,1)\) | \(5\) |
| \(8,8\) | \((4,3),(5,1)\) | \(5,4\) |
| \(8,10\) | \((5,5),(6,3),(7,1)\) | \(5,5,5\) |
| \(8,13\) | \((7,7),(8,5)\) | \(6,6\) |
| \(10,10\) | \((7,5),(8,3),(9,1)\) | \(6,6,5\) |
| \(10,13\) | \((9,7),(10,5)\) | \(6,6\) |
| \(13,13\) | \((11,9),(12,7),(13,5)\) | \(6,6,6\), argument below |
| \(13,16\) | \((13,11)\) | impossible, argument below |
| \(16,16\) | \((15,13),(16,11)\) | \(6,5\), argument below |
| \(16,18\) | \((16,15)\) | \(6\) or impossible, argument below |
| \(18,18\) | \((17,17),(18,15)\) | \(6,6\) |
| \(20,20\) | \((20,19)\) | impossible by JM §3 Lemma 1: \(s=t=k,\xi=k-1\) |

For exhaustiveness, for each ordered pair \(s\le t\) from the eight inputs above, run \(k=0,\ldots,s\), compute \(\xi=2(s+t)-2k-21\), retain exactly \(0\le\xi\le k\), and delete the two Parseval exclusions. There are 24 arithmetic proper tuples, of which 23 survive the Parseval exclusions; all have \(k>0\). Including the same-size \((21,21,21,21)\) case above, the raw arithmetic total is 25. The included verifier enumerates them from scratch. In the regular rows, substitute the affine dimensions \(2,3,4,5,5\) for sizes \(4,8,10,13,18\) into the intersection/union bound from §2. The dimension inputs are JM §2 Property 6 (sizes 4 and 8), §6 Lemma 4 / Theorem 3 (size 10), §6 Lemma 5 / Theorem 4 (size 13), and Appendix A.4 (size 18).

* **\(s=t=13\).** By JM Theorem 4 a size-\(13\) support is a union of two affine 3-flats meeting in an affine line, with one point of that line removed. Any 4-flat in the support hull meets it in at most nine points. If the 4-flat contains neither 3-flat, its intersections with them have at most four points each. If it contains one 3-flat, it cannot contain the other (the pair spans five dimensions); the other contributes at most four points, with both points of the common line already counted, and the removed point is in the 4-flat. The bound is then \(8+4-2-1=9\). Different size-\(13\) hulls meet, if at all, in a proper affine subspace of each, contained in a 4-flat. This contradicts \(k\ge11\); hence the hulls are equal and the joined dimension is at most \(6\).
* **\(s=13,t=16\).** Here \(k=13,\xi=11\). The size-\(16\) function has either constant absolute nonzero magnitude \(1/4\) (plateaued, also by Parseval) or a four-dimensional support hull (JM §6 Proposition 15). The latter hull cannot contain the five-dimensional size-\(13\) support. In the plateaued case, the size-\(13\) function has twelve coefficients of absolute magnitude \(1/4\) and one of \(1/2\) (JM Theorem 4), giving \(\xi=12\), not \(11\).
* **\(s=t=16\).** In both rows \(\xi<k\). Both functions cannot be plateaued, since all their nonzero absolute normalized magnitudes would be \(1/4\). One has hull dimension \(4\) by JM Proposition 15. Since \(k\ge15\), the other support adds at most one new point to the union, and when \(k=16\) it adds none. This bounds the joined dimension by \(6\) for \(k=15\) and by \(5\) for \(k=16\).
* **\(s=16,t=18\).** With \(k=16\), the size-\(16\) support is contained in the size-\(18\) support, so the joined dimension is at most \(6\). More specifically, its plateaued subcase is impossible: the size-\(18\) magnitude list has no \(1/4\), which would give \(\xi=0\) instead of \(15\). The dimension bound, and hence the theorem, does not need this extra exclusion or the size-\(18\) magnitude data.

This completes the dimension bound of six in every case. By reduction and padding any joined function is now EA-equivalent, after removing or adding dummy variables, to a six-variable function of size \(21\). The base calculation means that all such support shapes are equivalent and their dimension is five. Induction proves uniqueness in every ambient dimension.

## 4. Two shapes at every larger cardinality

### Exact finite certificate: \(22\le r\le86\)

The file [witnesses.json](witnesses.json) gives two truth tables for each of the 65 sizes. Bit \(i\) of its hexadecimal integer is \(f(i)\) with the binary digits of \(i\) as input coordinates, least significant coordinate first. An item \([n,h,d,E]\) gives the dimension of the input, the table, and the following two affine invariants of its support \(S\):
\[
 d=\dim\operatorname{aff}(S),\qquad
 E=\sum_{u\ne0}\binom{m_S(u)}{2},\quad
 m_S(u)=|\{\{x,y\}\subseteq S:x\ne y,\ x+y=u\}|.
\]
Every affine support isomorphism maps differences by its invertible linear part, hence permutes the multiplicities \(m_S(u)\) on the direction spaces. Both invariants are therefore preserved even between different ambient dimensions. A pair of distinct unordered pairs contributing to \(E\) has no common element (otherwise the two pairs are the same) and the four distinct points sum to zero. Every such affine 2-plane contributes three pairings. Thus \(E\) is also three times the number of contained affine 2-planes, an independent way to compute it. The verifier derives each support from the full integer Walsh transform, checks its cardinality, and checks that the two invariant vectors differ. It checks every witness again with direct character sums, explicit affine span closure and 4-set counting instead of the fast algorithms. Duplicating a valid table with the correct cardinality is a negative control; this must fail on the invariants, and does. Each certificate uses at most seven variables.

### A nonflat seed at every needed size

For every \(s\ge20\) there is a Boolean function with support of size \(s\): take \(n\ge7\) such that \(2^n\ge s\) and use JM §7 Theorem 5. If \(s\) is not a power of two, its support cannot be an affine flat. If \(s\) is a power of two, JM §7 Lemma 7 guarantees a support of size \(2^j\) which is not an affine flat for \(j\ge4\) in sufficiently many variables. Thus we may always start with a support \(S\) of size \(s\), with \(S\ne V=\operatorname{aff}S\), and modulate so that \(V\) is a vector space. Enlarge the ambient space when needed by padding. Since \(f\) is not affine, all normalized magnitudes in \(S\) are strictly smaller than \(1\): equality in the character sum requires that character times \((-1)^f\) be constant.

### Even sizes

Take even \(r\ge42\) and \(s=(r-2)/2\ge20\). Join \(f\) with an affine function supported on the singleton \(\{a\}\), using either \(a\in V\setminus S\) or \(a\notin V\). The supports of the two restrictions are disjoint in either case, so the result has support
\((S\cup\{a\})\times\mathbb F_2\) of size \(r\). Its affine dimension is \(\dim V+1\) in the first choice and \(\dim V+2\) in the second.

### Odd sizes

Every odd \(r\ge87\) is either \(4s+7\) or \(4s+9\) with \(s\ge20\). First use the preceding disjoint join with \(a\notin V\), giving
\[
 P=(S\cup\{a\})\times\mathbb F_2,\qquad
 L=\operatorname{aff}P=(V+\langle a\rangle)\times\mathbb F_2 .
\]
Only \((a,0),(a,1)\) have absolute normalized magnitude \(1/2\) in \(P\); the other magnitudes are smaller. Write \(b=(a,0)\). A quadratic \(g\) can have any prescribed affine 2-flat \(H\) as its support and all four magnitudes \(1/2\): take the product of two independent linear input parities, whose support is the linear span of their frequency vectors, and modulate by a suitable character (JM Property 6 also supplies this fact). We choose \(H\) in the slice with first join coordinate \(0\); then in \(P\cap H\) the only possible matching magnitude is at \(b\). In the constructions below \(b\in H\), so always \(\xi=1\).

* For \(r=4s+9\), want \(k=1\). Write \(H=b+\langle u,v\rangle\), using directions with join coordinate \(0\). First take a nonzero \(u\) from \(V\times\{0\}\) and \(v\) outside \(L\). Then \(b+u\notin P\) and points with direction \(v\) are outside \(L\); only \(b\) is shared, and the hull of \(P\cup H\) has dimension \(\dim L+1\). For the second choice take \(u,v\) independent modulo \(L\), still with join coordinate zero by padding original variables. Again only \(b\) is shared and the union hull has dimension \(\dim L+2\).
* For \(r=4s+7\), want \(k=2\). Pick \(p\in S\) and take \(u=b+(p,0)\). First take \(v=(t+p,0)\) for \(t\in V\setminus S\). Then \(b+u=(p,0)\) is shared but \(b+v\) is a point in the other \(V\)-coset distinct from \(b\), and \(b+u+v=(t,0)\) is outside \(P\). Here \(u,v\) are independent and \(H\subset L\), so the union hull has dimension \(\dim L\). Second take \(v\) outside \(L\) with join coordinate zero; the same two points are shared and the hull grows to dimension \(\dim L+1\).

In either case join the function with support \(P\) to the quadratic with support \(H\) on a new bit. The resulting size is \(2((2s+2)+4)-2k-1=4s+11-2k\), as wanted. A point of \(P\setminus H\) exists and gives a full fiber; §2 shows the new affine dimension is exactly the union hull dimension plus one. The two choices therefore give inequivalent shapes. The construction works in a common ambient space for the two choices, with further padding preserving the shapes.

The finite certificate and these two constructions give two shapes at every integer \(r\ge22\). Together with the size-\(21\) induction this proves the theorem. The proof is analytic apart from the stated finite truth-table certificate and the six-variable EA base classification; it does not infer universal uniqueness from experimental searches in growing dimensions.
