# Two dense spectral cardinalities excluded in \(\mathbb F_{13}^{3}\)

**Claim.** Neither \(104=8\cdot13\) nor \(117=9\cdot13\) is the size of a spectral subset of \(\mathbb F_{13}^{3}\). The only remaining candidate spectral sizes that would contradict Fuglede in this group are \(26,39,52,65,78,91\); none is excluded by the present claim.

The projective incidence and moment mechanism follows Ferguson and Iosevich, [arXiv:2610.30712v1](https://arxiv.org/html/2610.30712v1), Lemmas 8.2 and 8.5 and Proposition 13.1. Their \(p=11\) direction certificates are not used. The new input is a normalized exact \(\mathbb F_{13}^{2}\) census, combined with a bootstrap on line caps. The elementary deductions are included so that the odd-prime applicability is explicit. No publication priority is asserted.

## Uniform normals, caps, and their bootstrap

Put \(p=13\), let \((E,A)\) be a spectral pair of size \(mp\), and let \(D(B)\) be the set of projective directions of nonzero differences of \(B\). Let \(U_B\) consist of projective normals for which all \(p\) affine planes perpendicular to the normal contain exactly \(m\) points of \(B\). A Fourier zero implies equal occupancy by the irreducibility of the prime cyclotomic polynomial. The square character matrix is unitary after dividing by \(\sqrt{mp}\), so its row and column orthogonality give \(D(A)\subseteq U_E\) and \(D(E)\subseteq U_A\).

For any affine line \(\ell\) with \(a\) points of \(B\), the occupancies of the \(p+1\) planes through \(\ell\) sum to \(mp+pa\): each point outside \(\ell\) is counted once and each on \(\ell\) is counted \(p+1\) times. As \(0<m<p\), this sum cannot equal \((p+1)m\), so \(U_B\) cannot contain a full projective line. An affine plane with \(p+1\) points determines all its \(p+1\) tangent directions, since each fixed direction partitions it into only \(p\) parallel lines. This would give a full projective line in its partner's \(U\), so all affine plane occupancies are at most \(p\).

For a given affine line of direction \(d\), at least one normal on \(d^\perp\) is uniform: the partner has more than \(p\) points, so two have equal dot product with \(d\). The plane pencil has at least one occupancy \(m\) and at most \(p\) for every other plane. This gives \(mp+pa\le m+p^2\), and hence \(a\le p-m\). More generally, if every projective line meets \(U_B\) at least \(r\) times, then
\[
 a\le \left\lfloor\frac{rm+(p+1-r)p-mp}{p}\right\rfloor.
\]
This bound uses \(m<p\), so that each additional uniform plane reduces the upper estimate.

Fix any two-dimensional linear plane \(P\). The \(p\) translates of \(P\) partition \(A\), so one slice has at least \(m\) points. Choose exactly \(m\) of them; their difference directions belong to \(\mathbb P(P)\cap U_E\), and they inherit the line cap. Exchange the partners for the same conclusion for \(U_A\).

The exact planar verifier gives these statements:
1. An eight-point set of line cap five in \(\mathbb F_{13}^{2}\) determines at least six directions.
2. An eight-point set of line cap three determines at least eight directions.
3. A nine-point set of line cap four determines at least eight directions.

All these sets are noncollinear by their caps. Normalize an ordered noncollinear triple by an affine invertible map to \((0,0),(1,0),(0,1)\). If a set had at most the indicated forbidden number of directions, its set of slopes would extend to a mask of that exact size containing \(0,-1,\infty\). The verifier tries every such mask and every increasing extension of the fixed triple. Each candidate is already compatible with each chosen point in the mask; testing any occupied line through the candidate prevents exactly the line-cap violations. The target counts are zero, with respective mask counts \(55,330,330\) and visited-node counts \(880,40771,63253\). Run [`verify-fuglede-f13-dense.js`](verify-fuglede-f13-dense.js) with Node; it requires no dependencies.

For \(m=8\) the initial cap is five, so the first statement gives \(r=6\). The pencil bound then yields \(a\le\lfloor(48+104-104)/13\rfloor=3\). The second statement improves \(r\) to eight. For \(m=9\) the initial cap is four and the third statement directly gives \(r=8\). Thus both cases force between eight and thirteen uniform normals on every projective line.

## Degree-ten rigidity

Suppose a nonzero form of degree at most ten vanishes on \(U_B\), and multiply by a suitable power of a nonzero linear form to assume degree exactly ten. Let \(N=|U_B|\) and \(n_L=|U_B\cap L|\) for each projective line \(L\). A line not dividing the form contains at most ten zeros. Thus \((n_L-8)(n_L-10)\le0\) for nonfactor lines, while for each of at most ten factor lines it is at most \((13-8)(13-10)=15\). Hence the total is at most \(150\). On the other hand, the \(183\) projective lines satisfy
\[
 \sum_L n_L=14N,\quad \sum_L n_L^2=N^2+13N,\quad
 \sum_L(n_L-8)(n_L-10)=N^2-239N+14640\ge360,
\]
the last inequality holding for every integer \(N\). This contradiction proves rigidity.

For \(1\le j\le10\) the moment form \(M_j(v)=\sum_{x\in B}(v\cdot x)^j\) vanishes on \(U_B\), because each field value occurs \(m\) times and \(\sum_{t\in\mathbb F_{13}}t^j=0\) in this range. Thus \(M_j\) is the zero polynomial for all these \(j\). The zero moment also vanishes since \(|B|=13m\).

## Moment conclusion and contradiction

At any normal let \(n_t\) be the integer plane occupancy at level \(t\). The moments imply that \((n_t\bmod 13)_t\) is orthogonal over \(\mathbb F_{13}\) to the evaluation vectors of \(1,t,\dots,t^{10}\). The latter are independent and their annihilator is exactly the span of evaluations of \(1,t\), by field power sums. Hence \(n_t\equiv at+b\pmod{13}\).

If \(a\ne0\), the residues run through all thirteen classes exactly once. Since \(0\le n_t\le13\), the sum is \(78\) or \(91\), depending on whether the one zero residue is represented by \(0\) or \(13\). This is impossible for \(m=8,9\). If \(a=0\), the profile is either the constant \(m\) profile, or a profile with \(m\) entries equal to \(13\) and the rest zero. Fix any secant line of \(B\) with \(c\ge2\) points. Its fourteen incident planes are nonempty, so each contains \(m\) or \(13\) points. If \(s\) of those planes contain \(m\), the pencil gives \((13-m)s=13(14-m-c)\). Since \(13\) divides \(s\), the only possibilities are \(s=0\) and \(s=13\). These give \(c=14-m>13-m\) or \(c=1\), respectively, both impossible.

Finally the standard finite-field reductions in Ferguson–Iosevich, Proposition 8.1 and Lemma 8.2, leave only sizes \(13m\), \(2\le m\le12\), as possible spectral failures of Fuglede. The lower threshold in [Malikiosis, Theorem 1.4](https://arxiv.org/abs/2212.13592) is \(169-12\sqrt{13}<130\), excluding \(m=10,11,12\). The present argument further excludes \(m=8,9\), not the remaining six cardinalities.

### Comparison with the earlier linear-programming bound

[Malikiosis, §6 and (6.1)](https://arxiv.org/html/2212.13592#S6) gives a stronger conditional exclusion whenever the nonzero Fourier support is a three-fold blocking set. Its threshold at p=13 is below 104. The parallel-plane alternative in the same section is not excluded by that conditional estimate; the incidence and moment proof above does not require the three-fold hypothesis and covers either case.
