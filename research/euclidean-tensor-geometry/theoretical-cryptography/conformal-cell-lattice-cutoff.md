# Conformal-cell truncation for lattice laws of sparse linear energies

**Scope.** This is a reusable relative truncation theorem for a fully specified forward probability law. It does not infer unknown coefficients, compute a decoding, or claim an algorithm for Ring-LWE.

Let \(A\) be a supplied \(m\times n\) integer matrix with rows \(a_j\), and \(\theta\in\mathbb Q^n\). Consider on \(\mathbb Z^n-\theta\) the energy
\[
       E(y)=\sum_{j=1}^m f_j(a_j^\mathsf T y)
\]
with even convex potentials \(f_j:\mathbb R\to[0,\infty)\) satisfying \(f_j(0)=0\), and suppose \(Z=\sum_y e^{-E(y)}<\infty\). Augment the matrix by the coordinate rows, \(M=\binom{A}{I_n}\). Cut \(\mathbb R^n\) into sign cones by the row hyperplanes of \(M\), including their faces. Let the supplied integer \(C\ge1\) bound the maximum coordinate magnitude of the primitive integer generator of every extreme ray in every such cone. For positive integers \(h\), write
\[
 K_C(h)=\min\{E(hz):z\in\mathbb Z^n,\ 0<\|z\|_\infty\le C\}.
\]
Using the minimum over primitive rays instead only strengthens the bound.

**Relative cutoff.** On this shifted lattice,
\[
       \frac{\sum_{\|y\|_\infty>nCh}e^{-E(y)}}{Z}
                        \le n\,e^{-K_C(h)}.               \tag{1}
\]
The same relative statement holds on any nonempty subset of the shifted integer lattice invariant under subtracting the particular conformal integer shifts in the proof. In particular it holds with supplied coordinate residues modulo \(q\) when \(h\) is a multiple of \(q\), without changing the constant of the bound.

**Bit-complexity consequence.** Suppose \(f_j(t)=w_jt^2\) with positive binary rational weights and \(\operatorname{rank} A=n\). If a fixed-width tree decomposition of the primal support graph is supplied, \(\log Z\) can be approximated to additive error \(\varepsilon\) deterministically in time polynomial in the input bit length, \(C\), \(1/K_C(1)\), and \(\log(1/\varepsilon)\). No numerical upper bound on the weights, or even on the entries of \(A\) when the ray bound \(C\) remains small, is required. A supplied positive lower bound for \(K_C(1)\) suffices, or the least positive weight can be used. In particular it is polynomial in the input bits and precision bits when \(A\) is totally unimodular and the active weights are positive integers, or when the relevant bounds are numerically polynomial. The local factors may involve three or more coordinates.

## 1. Preserve the cell, not just the sign cone

For a sign vector \(\sigma\) attained by \(My\), the associated closed cone consists of \(u\) satisfying \(\sigma_i(Mu)_i\ge0\) for \(\sigma_i\ne0\) and \((Mu)_i=0\) for \(\sigma_i=0\). It is pointed because the coordinate rows were included. Every extreme ray has a primitive integer generator. Fix in advance a simplicial subdivision of each such cone using only its extreme rays. For instance intersect it with \(\sum_i\operatorname{sgn}(y_i)u_i=1\) on its nonzero part, a well-defined positive functional for the chosen sign pattern, triangulate this bounded polytope with its own vertices, and cone the triangulation back from zero. No enumeration of sign cones or triangulations is required by the numerical algorithm.

Each \(y\ne0\) is in the relative interior of a unique cell of the subdivision for its sign pattern. Let \(z_1,\ldots,z_s\), \(s\le n\), be that cell's primitive rays. They are linearly independent, and \(y=\sum_i\alpha_i z_i\) with all \(\alpha_i>0\). If \(\|y\|_\infty>nCh\), some \(\alpha_i>h\), since
\(\|y\|_\infty\le C\sum_i \alpha_i\). Choose one such ray by any fixed rule and set \(y'=y-hz_i\). This remains a point of the same shifted lattice, with the same sign pattern for \(My'\), because all row values of the rays conform and all coefficients are still positive. It also lies in the **same relative-interior simplicial cell**, not only in the same sign cone.

For any row \(a_j\), if \(a_j^\mathsf T z_i\ne0\) then \(a_j^\mathsf T y\) has that sign and magnitude at least \(h|a_j^\mathsf Tz_i|\). For \(t\ge s\ge0\), convexity and \(f(0)=0\) imply \(f(t)-f(t-s)\ge f(s)\), by monotonicity of increments of fixed length. Evenness treats both signs. Hence
\[
                E(y)-E(y')\ge E(hz_i)\ge K_C(h).
\]
From \(y'\) its sign cone and relative-interior cell are determined. Every preimage differs from it by \(h\) times one of that cell's at most \(n\) rays. This is why no exponential direction count is paid, even in a cone with many extreme rays. Summing the pointwise inequality with multiplicity at most \(n\) proves (1). On the stated residue domains, \(hz_i\) has every coordinate divisible by \(q\), so the same proof uses the restricted normalizer instead of \(Z\).

Existence of a conformal real decomposition without cancellation is classical. The reusable counting step here is to choose a common subdivision and move **within the same cell** so that the inverse-image multiplicity is bounded. An arbitrary choice of a fresh conformal decomposition separately at every \(y\) would not justify this multiplicity bound.

## 2. Checking usable ray bounds

At a ray of a sign cone, the rows of \(M\) vanishing on that ray span rank \(n-1\). Otherwise a linearly independent perturbation in their common kernel would give a pair of small opposite perturbations through the ray satisfying all strict inequalities, contrary to extremality. Pick \(n-1\) independent zero rows. The vector of their signed \((n-1)\)-minors generates the one-dimensional kernel, and dividing its coordinates by their greatest common divisor gives the primitive ray, up to sign. Thus any bound on the absolute \((n-1)\)-minors suffices for \(C\). A bound on full \(n\)-minors of \(M\) also suffices, because every such smaller minor can be extended by coordinate rows in the missing columns; any duplicates would only occur for a zero minor. If \(A\) is totally unimodular, so is \(\binom A{I_n}\), and \(C=1\). At \(n=1\) use the empty minor 1.

This is only sufficient and a small primitive-ray bound may survive a large full-minor bound. For example for signed graph forms \(y_i\), \(y_i-s_{ij}y_j\), the active homogeneous equations impose only zeros and signed equalities. Their solution has one scalar per free sign-compatible component; an inconsistent sign-cycle component or a component pinned to zero is fixed to zero. A one-dimensional kernel therefore has primitive generator in \(\{0,\pm1\}^n\). This recovers the former signed-graph relative tail with a cutoff radius \(nh\), half the radius of its direct gap proof, while keeping the same ternary-energy parameter and multiplicity \(n\).

There are multi-coordinate examples not of graph-difference type. A matrix whose rows are indicators of intervals in a line is totally unimodular by the consecutive-ones criterion applied to its transpose. Fixed-width intervals have bounded primal graph width, and full rank holds, for example, if all singleton rows are also present with positive weights. Arbitrarily stiff penalties \(w_j(y_i+y_{i+1}+y_{i+2})^2\) can thus be present. Multiplying a row by a nonzero integer does not change its hyperplane or the set of feasible primitive-ray sizes; for quadratic potentials it simply changes the weight by a positive square factor. The method needs a real structural ray-size promise, not a bound on all individual arithmetic entries.

## 3. From relative cutoff to a finite positive calculation

In the quadratic case \(K_C(h)=h^2K_C(1)\). Positive definiteness implies \(K_C(1)>0\), and since \(A\) and \(z\) are integral, any nonzero \(z\) hits an active squared linear form of magnitude at least one. This gives \(K_C(1)\ge\min_j w_j\). Alternatively \(K_C(1)\) can be computed by fixed-width min-sum dynamic programming on labels \(\{-C,\ldots,C\}\): minimize over the \(n\) choices of a designated coordinate constrained nonzero. The primal graph joins all coordinates appearing in a row. Their set is a clique and is contained in one bag, by the running-intersection property and the Helly property of subtrees of a tree. Each row weight is therefore a local factor of the bounded-width recurrence.

Take \(h\ge1\) such that \(h^2 K_C(1)\ge\lceil\log_2(8n/\varepsilon)\rceil\), with a lower bound if desired. Then the box of radius \(nCh\) contains \(1-\varepsilon/8\) of the exact mass. Its alphabet has numerical size polynomial in the stated quantities. At fixed residue modulus take the next multiple of \(q\), preserving the relative numerator cutoff. To compute the box normalizer, use log-domain sum-product on the supplied decomposition, exactly as for the signed-graph case; arithmetic details are repeated briefly here because large matrix entries are permitted. The local log weight \(-w_j(a_j^\mathsf T y)^2\) is a rational of polynomial bit length. At each message subtract the maximum of the finitely many log entries before exponentiating in a log-sum-exp, drop terms below a cutoff \(O(\log(k/\delta))\) in magnitude for \(k\) summands and target accuracy \(\delta\), and use elementary real approximations on the remaining bounded arguments. The normalized sum is at least one. The log-sum-exp is 1-Lipschitz in maximum log-input error, so inducting up the tree with a per-bag error \(\varepsilon/(8\,\#\mathrm{bags})\) makes accumulated arithmetic error \(O(\varepsilon)\). Passing from the box normalizer to the full normalizer changes the logarithm by at most \(\varepsilon/4\), leaving room for the desired output tolerance. Both the local bit lengths and the log magnitudes' integer bit lengths are polynomial, regardless of the numerical upper stiffness.

No direction or cone is enumerated by this algorithm. The geometry supplies a finite cutoff for a known positive sum; the only combinatorial state in the numerical calculation is a bag assignment. In particular no lattice point with a prescribed noisy observation is being found.

## Prior work

[Rockafellar, *The Elementary Vectors of a Subspace*](https://sites.math.washington.edu/~rtr/papers/rtr020-ElemVectors.pdf) and [Müller–Regensburger, *Elementary Vectors and Conformal Sums in Polyhedral Geometry*](https://arxiv.org/abs/1512.00267) give the conformal decomposition viewpoint. The determinant bound for primitive rays is the standard cofactor argument, and the consecutive-ones and bag-elimination steps are standard. The additional assertion here is the common-cell preimage estimate (1) for a **partition sum**, and its precision consequence. Existing directed discrete midpoint convexity and proximity results for two-separable objectives concern minima rather than such partition tails; the bounded-local-alphabet step proved here also applies when a row has several arguments. The earlier signed-graph result has a more elementary dedicated proof for an important special class; this extension does not turn a general negacyclic multiplier matrix into a small-ray or low-width instance.
