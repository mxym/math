# Packing under determinant-one archimedean twists of cyclotomic root ideals

Let \(m>2\) be a reduced cyclotomic conductor (odd or divisible by four), \(K=\mathbb Q(\zeta_m)\), and
\[
 I=\left(\prod_{\substack{p\mid m\\p\text{ odd}}}(1-\zeta_p)\right)\mathcal O_K .
\]
For a complex place \(v\) of \(K\), write \(\sigma_v\) for either embedding of the conjugate pair. For real log weights \(a_v\) with \(\sum_v a_v=0\), consider
\[
 M(a)=\min_{x\in I\setminus\{0\}} 2\sum_v e^{a_v}|\sigma_v(x)|^2 .
\]
The constraint on log weights fixes the covolume: each of the two real coordinates at \(v\) is multiplied by \(e^{a_v/2}\). Thus maximizing \(M\) is exactly maximizing the squared packing radius at fixed covolume for this ideal and these twists. We only consider this geometric problem, not an algorithm for finding short vectors or a security claim.

**Result.** The untwisted point on this archimedean space is a strict local maximum for an odd prime conductor greater than three, a strict local minimum when there is one place type but more than one place, and a saddle otherwise (apart from the zero-dimensional cases). The place types are the independent signed residues modulo the odd primes dividing \(m\). The first variation is *entirely* determined by the mean log weight in each type; a nonzero change invisible to those means improves the minimum at second order. The maximum in a small log-\(\ell_\infty\) box has an exact formula. For an even number of places in each type it holds on an explicit, dimension-independent interval, and yields an improvement of at least \(3/(2\sqrt 2)\) in the squared minimum whenever there are at least two odd primes. For an odd number greater than one in each type there is another explicit dimension-independent achievable gain.

## 1. The two lowest unweighted shells

Write
\[
 m=2^b\prod_{p\text{ odd}}p^{a_p},\qquad
 T=\varphi(2^b)\prod_pp^{a_p},\qquad
 J=\varphi(2^b)\prod_pp^{a_p-1};
\]
here \(b=0\) or \(b\ge2\), and \(k\) denotes the number of odd primes. Under the trace metric, \(I\) is isometric to \(\sqrt T\) times an orthogonal sum of \(J\) copies of \(\bigotimes_p A_{p-1}\). The empty tensor is the rank-one lattice \(\mathbb Z\).

Indeed for an odd prime power \(p^a\), the trace of \(\zeta_{p^a}^j\) is zero unless \(p^{a-1}\mid j\); on those powers it is \(p^{a-1}\operatorname{Tr}_{\mathbb Q(\zeta_p)/\mathbb Q}(\zeta_p^{j/p^{a-1}})\). This follows by first summing all unit lifts of a nonzero residue modulo \(p\). Hence
\[
 \mathbb Z[\zeta_{p^a}]
 =\bigoplus_{j=0}^{p^{a-1}-1}\zeta_{p^a}^j\mathbb Z[\zeta_p]
\]
orthogonally, in the larger trace metric. Each copy of \((1-\zeta_p)\mathbb Z[\zeta_p]\) is a scaled root lattice: \(\zeta_p^u\mapsto\sqrt p(e_u-\mathbf1/p)\) is the trace isometry, and \((1-\zeta_p)\zeta_p^u\) maps to \(\sqrt p(e_u-e_{u+1})\). Traces add the factor \(p^{a-1}\) to squared norms. For a power of two the standard monomials are orthogonal with squared length \(\varphi(2^b)\). The coprime prime-power integer rings tensor integrally to \(\mathcal O_K\) because the roots generate one another and the ranks agree. Independence of embeddings makes their trace forms tensor as well.

The integral realization of the odd tensor consists of arrays with zero sum on every coordinate line. Their shortest nonzero vectors are exactly signed elementary boxes, namely tensors of roots \(e_i-e_j\), with squared norm \(2^k\). For \(k\ge2\) the next shell has squared norm \(3\cdot2^{k-1}\). To prove these assertions, any nonzero tensor has at least two nonzero slices in each coordinate direction, and those slices are zero-line-sum tensors in one fewer direction. Induction gives their squared norm at least \(2^{k-1}\). If the full tensor has squared norm less than \(3\cdot2^{k-1}\), it has exactly two nonzero slices in every direction, so it is supported on a product of pairs. Zero line sums force it to be an integer multiple of the alternating elementary box; its smallest amplitude is one. The next bound is attained by a simple six-cycle on any three rows and three columns, tensored with elementary roots in the remaining directions. For \(k=1\) the next squared norm is at least four because integer squared norm and coordinate sum have the same parity; for \(k=0\) this follows directly on the line. Using multiple orthogonal copies cannot give a squared norm less than twice the first shell.

Consequently \(M(0)=T2^k\). All vectors at this value lie in single copies. In field notation, their absolute values in each embedding are those of
\[
 \prod_{p\text{ odd}}(1-\zeta_p^{d_p}),\qquad d_p\not\equiv0\pmod p ;
\]
all phases from roots of unity have modulus one. Every vector outside this shell has squared norm at least \(\beta M(0)\), where
\[
 \beta=\tfrac32 \text{ if }k\ge2,\qquad \beta=2\text{ if }k<2 .
 \tag{1}
\]
If \(\|a\|_\infty\le t\), every squared norm changes by a factor in \([e^{-t},e^t]\), so for sufficiently small \(t\) only the untwisted first shell can compete. We also use the lower bound \(e^{-t}\beta M(0)\) outside the first shell at explicit finite \(t\).

## 2. Exactly which directions are visible to first order

Let \(A=(\mathbb Z/m)^\times/\{\pm1\}\), the set of complex places, and
\[
 Q=\prod_{p\text{ odd}}(\mathbb Z/p)^\times/\{\pm1\},\qquad
 \pi:A\longrightarrow Q .
\]
Write \(B=|Q|\) for the number of place types and \(D=|A|/B\) for the number of places of each type; the map is surjective, including when \(Q\) is the trivial group. For a given weight vector \(a\), let \(a^{\mathrm{av}}_c=D^{-1}\sum_{\pi(v)=c}a_v\).

For first-shell vector type \(d\in Q\), the normalized squared norm equals a positive weighted average \(\sum_{c\in Q}\omega_d(c)\overline{e^a}_c\), where
\[
 \overline{e^a}_c=\frac1D\sum_{\pi(v)=c} e^{a_v},
 \qquad
 \omega_d(c)=
 \frac{\prod_{p\text{ odd}}[2-2\cos(2\pi d_pc_p/p)]}
      {\displaystyle\sum_{c'\in Q}\prod_{p\text{ odd}}[2-2\cos(2\pi d_pc'_p/p)]}.
 \tag{2}
\]
The averages of \(\omega_d(c)\) over \(d\) are \(1/B\) for every \(c\), by translation. The \(B\)-by-\(B\) matrix of these averages is invertible. It is a tensor of finite group convolution matrices up to index inversion. For each odd prime factor the Fourier coefficients on the trivial character are positive. For an even nontrivial character \(\chi\) modulo \(p\), the coefficient on the full unit group is \(-2\sum_{u\ne0}\overline{\chi(u)}e^{2\pi i u/p}\), nonzero because the Gauss sum has magnitude \(\sqrt p\); passage to the quotient divides the sum by two. The elementary magnitude computation expands the square and changes variables \(u=tv\): the inner sum over \(v\ne0\) is \(p-1\) when \(t=1\), and \(-1\) otherwise. This proves invertibility for each factor and hence for (2).

Let \(h\) be any fixed mean-zero direction in log weights. If \(h^{\mathrm{av}}\ne0\), the derivatives \(\sum_c\omega_d(c)h^{\mathrm{av}}_c\) are not all zero and average to zero. At least one is negative. Therefore \(M(sh)<M(0)\) for small \(s>0\), with a strictly negative first derivative. If \(h^{\mathrm{av}}=0\) and \(h\ne0\), all first derivatives vanish. Every second derivative is a strictly positive weighted average of the squares of \(h_v\), since every entry of every weight vector is positive. Hence \(M(sh)>M(0)\) for small \(s\ne0\). With only visible directions (\(D=1\)) the first estimate is uniform on the compact unit sphere of mean-zero directions; with only invisible directions (\(B=1\)) the second estimate is uniform by positivity and the finite set of types. This proves the strict local maximum for \(D=1<B\), strict local minimum for \(B=1<D\), and saddle for \(B,D>1\); \(B=D=1\) is zero-dimensional. In particular:
- For prime \(m=p\ge5\) we have \(D=1<B\).
- For \(m\) with at least two odd prime factors both \(B,D>1\).
- For an odd prime power \(p^a\), \(a\ge2\), \(D=p^{a-1}\), with strict local minimum for \(p=3\) and a saddle for \(p\ge5\).
The rule in terms of \(B,D\) also covers even conductors; for example powers of two \(m\ge8\) have \(B=1<D\).

## 3. Exact small-box optimum and explicit attained gains

Set
\[
 F(t)=\max_{\sum_v a_v=0,\ \|a\|_\infty\le t} M(a)/M(0).
\]
For finite \(t\) the maximum exists. On this compact box a single first-shell vector bounds \(M(a)\le e^t M(0)\); any competing untwisted vector has norm at most \(e^{2t}M(0)\) by form comparison, hence there are finitely many to consider.

### Even \(D\)

For all
\[
 0\le t\le \frac12\log(2\beta-1),\qquad F(t)=\cosh t .
 \tag{3}
\]
For the upper bound, the minimum over first-shell vectors is at most their average over types, namely \(|A|^{-1}\sum_v e^{a_v}\). The secant bound on \(e^a\) over \([-t,t]\) and \(\sum_v a_v=0\) bound this average by \(\cosh t\), even for larger \(t\). For the lower bound put half of the \(a_v\) in each type at \(t\), and the other half at \(-t\). Then exactly every first-shell vector has squared norm \(M(0)\cosh t\). By (1) the other vectors cannot undercut it if \(e^t\cosh t=(e^{2t}+1)/2\le\beta\). Moreover for \(t>0\) throughout this interval the stated per-type balancing condition characterizes the maximizing weights: equality in the secant requires every weight at an endpoint, and equality of the average and minimum requires that all first-shell types have the same squared norm. By invertibility in (2), all fiber averages of \(e^a\) are then equal, forcing balance in each type.

If there are at least two odd primes, \(D\) is even, since \(D=2^{k-1}\varphi(2^b)\prod_p p^{a_p-1}\) when \(k\ge1\). Taking \(t=\frac12\log2\) gives exactly \(3/(2\sqrt2)>1.06\) as the maximal factor within that box. In the even-\(D\) cases with \(k<2\), taking \(t=\frac12\log3\) gives \(2/\sqrt3\).

### Odd \(D\)

For each fixed conductor and sufficiently small \(t\),
\[
 F(t)=\frac{(D-1)\cosh t+1}{D}.
 \tag{4}
\]
A candidate uses \((D-1)/2\) entries at each endpoint and one zero in every type. Every first-shell vector reaches the right side, and other vectors cannot undercut it for small \(t\).

For the converse, consider any maximizing weight and let \(s_c=\sum_{\pi(v)=c}a_v\), so \(\sum_c s_c=0\). If \(B>1\), the linear fact used in §2 and compactness give a constant \(\eta>0\), for this fixed conductor, such that
\[
 \min_d\sum_c\omega_d(c)s_c\le-\eta\|s\|_\infty .
\]
Since the candidate is at least one, the expansion \(e^a=1+a+O(t^2)\) in all first-shell forms implies \(\|s\|_\infty=O(t^2)\) at a maximizing weight. When \(B=1\) the sole \(s\) is zero directly. In either case, for small \(t>0\) all \(|s_c|<t\). On a \(D\)-tuple of log weights in \([-t,t]\) of fixed sum \(s_c\), the maximum of the sum of exponentials is attained at a vertex, with at most one coordinate not at an endpoint. As \(D\) is odd and \(|s_c|<t\), the endpoints must occur equally often, leaving the final entry \(s_c\). Thus the optimal average on type \(c\) is at most \(((D-1)\cosh t+e^{s_c})/D\). Insertion into (2) and \(\min_d\sum_c\omega_d(c)(e^{s_c}-1)\le-\eta\|s\|_\infty+O(\|s\|_\infty^2)\) show no nonzero \(s\) can match the candidate. This proves (4) and, by strict convexity on each fiber and strict positivity of all weights, also characterizes maximizers, up to permuting places within each type. The case \(D=1\) gives \(F(t)=1\) near zero.

For odd \(D>1\) the only reduced conductors in this family are odd prime powers with exponent at least two. Here \(\beta=2\). At the explicit \(t=\frac12\log3\), without needing the small-box optimality claim at that \(t\), the same balanced-with-one-zero construction is valid because its first-shell factor is at most \(\cosh t\le2e^{-t}\). It guarantees
\[
 F(t)\ \ge\ 1+\frac{D-1}{D}\left(\frac{2}{\sqrt3}-1\right)
          \ \ge\ 1+\frac23\left(\frac{2}{\sqrt3}-1\right)>1.10 .
\]
Thus improvement is not merely infinitesimal. No global unrestricted optimizer is claimed.

## Literature and checks

[For the Hermite–Humbert framework](https://www.numdam.org/item/10.24033/bsmf.2571.pdf), the general extremality criterion is formulated in terms of perfection and eutaxy. The present calculation specializes to rank-one archimedean twists, exhibits the exact kernel of first variations, and solves the small log-box optimization for this family; it does not assert a new general perfection criterion. [Arakelov-modular lattices over CM fields](https://arxiv.org/abs/1609.03134) study ideal lattices with algebraically specified forms under a distinct modularity objective. The canonical tensor identification used here is standard prime-power trace arithmetic and is independent from the new place-type calculation.

The audit makes 8,297 exact assertions (including even finite-character matrix ranks over finite fields, the two tensor shells in fixed toy dimensions, and equal-size place fibers), and 380 numerical arithmetic assertions on the tied first-shell energies. It does not search for a lattice vector in a system or rely on numerical optimization.
