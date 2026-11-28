# Relative truncation of stiff lattice Gaussians on signed graphs

**Scope.** A forward normalizer and probability theorem for a fully supplied discrete Gaussian on an explicitly described graph. There is no observation with a hidden signal, lattice decoding procedure, or Ring-LWE solving claim.

Let \(G=(V,E)\), \(|V|=n\ge1\), be given. Let \(w_{ij}\ge0\) and \(\lambda_i\ge0\) be binary rational edge and pin weights, \(s_{ij}\in\{\pm1\}\) supplied edge signs, and \(\theta\in\mathbb Q^n\) a supplied shift. Write \(y=x-\theta\) and
\[
  E(y)=\sum_i\lambda_i y_i^2+
           \sum_{ij\in E}w_{ij}(y_i-s_{ij}y_j)^2,\qquad
  Z=\sum_{x\in\mathbb Z^n}e^{-E(x-\theta)}.
\]
Define the ternary shift cost
\[
       \kappa=\min_{z\in\{0,\pm1\}^n\setminus\{0\}} E(z).
\]
Assume \(\kappa>0\). This is equivalent to positive definiteness: each zero-energy real vector has \(y_i=0\) at positive pins and \(y_i=s_{ij}y_j\) across positive edges. A nonzero such vector has a whole nonzero component of equal magnitudes, from which one obtains a nonzero ternary zero-energy vector by dividing by that magnitude and setting other components to zero. The numerical upper sizes of the weights are unrestricted.

**Theorem.** For every positive integer \(h\), the tail outside \(\|x-\theta\|_\infty\le 2nh\) has relative mass at most \(n e^{-\kappa h^2}\). If a tree decomposition of fixed width is supplied, \(\log Z\) can be approximated to rational additive error \(\varepsilon\) deterministically in time polynomial in the input bit length, \(1/\kappa\) (or a supplied inverse-polynomial lower bound for \(\kappa\)), and \(\log(1/\varepsilon)\). This remains true even when some weights have exponentially large numerical values. At fixed \(q\) the same algorithm gives log-relative probabilities of coordinate residue constraints modulo \(q\). In particular it is bit-polynomial for positive-definite integer weights at fixed width.

This covers every symmetric diagonally dominant positive-definite rational precision matrix, since one can write its off-diagonal entry as \(-s_{ij}w_{ij}\) and its diagonal surplus as \(\lambda_i\). A sign gauge is not needed: cycles may be frustrated, meaning their signs cannot all be made positive by flipping coordinate signs.

## 1. An upper-scale-independent relative cutoff

Consider any \(y\in\mathbb Z^n-\theta\) with \(t=\max_i |y_i|>2nh\). Start at \(t/2\) and list the distinct magnitudes strictly above \(t/2\), ending at \(t\). There are at most \(n\) gaps and total length \(t/2\); hence one gap is greater than \(h\). Let \(S\) be the vertices at or above its upper endpoint. All \(|y_i|\) in \(S\) exceed \(h\), and \(|y_i|-|y_j|>h\) for \(i\in S,j\notin S\). Define \(z_i=\operatorname{sgn}(y_i)\mathbf1_{\{i\in S\}}\), and translate to \(y'=y-hz\). Tie breaking can be fixed deterministically; no optimal lattice point is involved.

For a pin term being moved, \(y_i\) and \(z_i\) have the same sign and \(|y_i|\ge h|z_i|\). On any edge with \(z_i-s_{ij}z_j\ne0\), the signed difference \(y_i-s_{ij}y_j\) has the same sign as \(z_i-s_{ij}z_j\) and magnitude at least \(h|z_i-s_{ij}z_j|\). For a cut edge this follows from the gap; for an internal edge with nonzero signed shift it follows because the two magnitudes add and are both greater than \(h\). All other edge terms are unchanged. Consequently, term by term from \(a^2-(a-hb)^2\ge h^2b^2\) when \(ab\ge h b^2\),
\[
                              E(y)-E(y')\ge h^2 E(z)\ge\kappa h^2.       \tag{1}
\]
In \(y'\), the upper layer remains strictly above its complement **in absolute magnitude**, since it lost only \(h\), and its signs are unchanged. Thus \(S\) is a nonempty upper segment in the ordered magnitudes of \(y'\), with at most \(n\) choices, and each choice recovers \(z\) and its preimage. Summing (1) over all tails of either sign, with a single map, proves the stated estimate. The argument never divides by a crude lower bound involving the maximum precision or a large nearest-vector energy.

The least positive local weight is always a lower bound for \(\kappa\) when the form is positive definite: at least one of a nonzero ternary vector's integer squares has a positive weight. Thus \(\kappa\ge1\) for integer weights. On a supplied bounded-width tree decomposition, \(\kappa\) itself can be computed using the finite-domain recurrence in §2 with min in place of the log-sum-exp and just the three labels \(0,\pm1\), taking the least over the \(n\) choices of a designated vertex required to be nonzero. This is exact finite optimization on supplied ternary energies. In the sign-compatible case, a diagonal sign change makes all signs positive, and \(\kappa\) equals the minimum nonempty ground-cut capacity with the given pin capacities: a constant sign on the selected support makes every internal term zero.

The same limit-of-alphabet argument works for even convex pin potentials \(f_i\) and signed-difference potentials \(g_{ij}\), with value zero at the origin. Associate the ternary capacity
\[
 \kappa(h)=\min_{z\in\{0,\pm1\}^n\setminus\{0\}}
     \left[\sum_i f_i(hz_i)+\sum_{ij}g_{ij}(h(z_i-s_{ij}z_j))\right].
\]
At a signed difference of magnitude \(t\ge a\ge0\), convexity gives \(g(t)-g(t-a)\ge g(a)\), and similarly for pins. The same single map proves a relative tail of \(n e^{-\kappa(h)}\) whenever the normalizer is finite. This is a probabilistic cutoff statement; computational bounds would require growth and precision access for the chosen potentials.

For a coordinate residue cylinder \(x_i\equiv a_i\bmod q\) on some set of indices, take \(h\) to be a multiple of \(q\). The same map preserves every such constraint, and controls the relative tail even with respect to the possibly smaller restricted normalizer. No extrapolation to large binary moduli is claimed.

## 2. Dynamic programming at arbitrary binary stiffness

Reduce \(\theta_i\) modulo integers and translate any supplied residues by the same amount. For \(0<\varepsilon\le1\), let \(l=\lceil\log_2(8n/\varepsilon)\rceil\), and take \(h\ge1\) with \(\kappa h^2\ge l\), using a lower bound for \(\kappa\) if necessary. In the residue case round \(h\) upward to a multiple of \(q\). The exact tail bound is then at most \((\varepsilon/8)Z\). The retained domain of each coordinate, \(x_i\in\mathbb Z\) with \(|x_i-\theta_i|\le2nh\) (and any prescribed residue), has \(O(nh+1)\) explicit entries. Its size is polynomial in \(n,1/\kappa,\log(1/\varepsilon)\) for fixed \(q\). Each is nonempty since \(h\ge1\), or \(h\ge q\) in the restricted case.

Root the supplied tree decomposition. Assign each unary and each edge term to one bag that contains its scope. Let \(E_v\) be the sum of the terms assigned to bag \(B_v\), and let \(S_v=B_v\cap B_{\mathrm{parent}(v)}\), with an empty separator for the root. Subtree messages are, in the ordinary positive sum-product convention,
\[
 M_v(x_{S_v})=\sum_{x_{B_v\setminus S_v}}
        e^{-E_v(x_{B_v}-\theta_{B_v})}
                 \prod_{w\ {\rm child\ of}\ v} M_w(x_{S_w}) .
\]
The running intersection property ensures that for fixed separator labels the variables in distinct child subtrees beyond the parent bag are disjoint. Thus this recurrence sums each configuration once and each energy term once. The root value is the box normalizer, and the number of label operations is polynomial for fixed width.

Use logarithms to avoid writing weights whose expansion would require bit length proportional to the numerical stiffness. Every local log weight is a binary rational of polynomial bit length (possibly very large in magnitude). Each message update first adds child log weights and a local log weight, then takes a log-sum-exp of a polynomial-sized list. The latter is 1-Lipschitz for the maximum error of its log inputs. A per-node arithmetic tolerance \(\delta\) after its local update gives by induction an error at most \(\delta\) times its subtree's number of nodes. Take \(\delta=\varepsilon/(8m)\) for \(m\) bags.

The local bit arithmetic is elementary and uniform: subtract the largest input \(M\) from all entries, retain the term 1, and drop arguments less than \(-\lceil\log_2(8k/\delta)\rceil\) for a list of length \(k\). Their total omitted exponential mass is at most \(\delta/8\). Evaluate exponentials of the remaining bounded arguments and the logarithm of their positive sum to sufficiently many binary places, using Taylor series with range reduction; since their normalized sum is at least 1, an absolute error \(\delta/8\) in the sum is sufficient. Adding back \(M\) only requires the bit length of a log value, not its exponential. All intermediate log magnitudes are bounded by the sum of local absolute energy magnitudes plus \(n\log(4nh+2)\), so their integer parts use polynomially many bits. Dyadic rounding within the tolerance keeps fractional lengths polynomial as well. This proves the claimed dependence on **bit** precision rather than \(1/\varepsilon\).

The exact log difference between the full and box normalizers is at most \(-\log(1-\varepsilon/8)\le\varepsilon/4\). Combining it with the arithmetic error gives the stated \(\log Z\) approximation. Applying the result with smaller error to numerator and denominator gives a log-relative estimate of each supplied cylinder probability. None of these computations identifies a lattice mode or reproduces an inverse observation model.

## 3. Why arbitrary graph width would be a substantive extension

There is an approximation-preserving embedding of any ferromagnetic Ising partition function with arbitrary, possibly inconsistent local fields into this positive pinned Gaussian family if graph width is unrestricted. This is a qualitative closure observation and not a hardness conjecture about a lattice scheme.

Given nonnegative rational couplings \(J_{ij}\) and rational fields \(h_i\), choose \(w_{ij}=2J_{ij}\) and a common pin \(\beta>0\). Write the matrix \(Q=\beta I+L_w\) and solve \(Q b=h\) over the rationals, setting \(\theta=\frac12\mathbf1+b\). The maximum principle at a coordinate of largest \(|b_i|\) gives \(\|b\|_\infty\le\|h\|_\infty/\beta\). Choose \(\beta\ge \max(4\|h\|_\infty,\,1)\) so that \(\theta_i\in[1/4,3/4]\). On binary \(x\), putting \(\sigma=2x-\mathbf1\) gives
\[
 e^{-E(x-\theta)}
   =\exp[-\operatorname{tr}(Q)/4-b^\mathsf TQb]\,
      \exp\left[\sum_{ij}J_{ij}\sigma_i\sigma_j+
                       \sum_i h_i\sigma_i\right].                       \tag{2}
\]

The binary box also captures the full sum when \(\beta\) is increased. Clip each integer coordinate to \([0,1]\). For a pair the new integer difference has the same sign or is zero, and no larger magnitude. Since \(|\theta_i-\theta_j|\le1/2\), the absolute residual \(|d-(\theta_i-\theta_j)|\) is nondecreasing on nonnegative integers \(d\) and nondecreasing away from 0 on nonpositive integers. Thus clipping does not increase an edge energy. For a coordinate \(k\ge1\) integer steps outside \([0,1]\), its pin energy loss upon clipping is at least \(\beta k^2\). For a fixed binary image and a given coordinate, its fiber has just the outward half-line plus the endpoint. Summing on these fibers gives
\[
   Z_{\rm bin}\le Z\le Z_{\rm bin}
         \left(1+\sum_{k\ge1}e^{-\beta k^2}\right)^n
     \le Z_{\rm bin}(1+2e^{-\beta})^n,\qquad \beta\ge1 .
\]
Taking \(\beta\ge\log(8n/\varepsilon)\) too makes the full-to-binary log error less than \(\varepsilon/4\). The logarithm of the correction factor in (2) is rational in the supplied parameters and computable exactly. For the positive rational weight presentation of Ising, approximate each logarithmic coupling and field by rational numbers to \(O(\varepsilon/(n+|E|+1))\), keeping the couplings nonnegative; the pointwise spin log error bounds the resulting normalization error. This converts the embedding to the usual relative-approximation convention. Hence a fully polynomial oracle without the width requirement would also approximate counting bipartite independent sets via the [Goldberg–Jerrum equivalence](https://doi.org/10.1017/S096354830600767X). This is an approximation-preserving implication, not a proof that such approximation is impossible.

## 4. A genuinely negacyclic example

Let \(P\) be the signed coordinate cycle, i.e. multiplication by \(X\) on coefficients in \(\mathbb R[X]/(X^n+1)\). For \(n\ge3\), the form \(w\|(I-P)y\|_2^2\) with \(w>0\) is
\[
      w\sum_{i=1}^{n-1}(y_i-y_{i-1})^2+w(y_0+y_{n-1})^2.
\]
There are no pins and precisely one negative wrap edge: it cannot be removed by a sign gauge. The quadratic form is positive definite, as \(P^n=-I\) rules out a nonzero fixed vector. Here \(\kappa=2w\): every nonempty proper ternary support contributes at least two cut edges, a singleton attains \(2w\), and an all-supported sign vector must disagree on at least one edge of the twisted cycle, costing \(4w\). Thus the treewidth-two recurrence applies even for arbitrarily stiff \(w\) in binary, with a lower cutoff scale expressed by \(2w\), not the much smaller minimum eigenvalue on the real space. The known forward law in this example is one special precision form, not a property of a generic Ring-LWE inference instance.

## Prior work and comparison

The energy class itself is standard in discrete convex analysis: [Tamura–Tsurumi, *Directed discrete midpoint convexity*](https://doi.org/10.1007/s13160-020-00416-0), Theorems 4 and 9, cover two-separable convex functions and characterize diagonally dominant quadratics, with scaling and proximity results for minimization. The relative partition-tail estimate here is about mass, not the location of a minimizer. The bounded-width finite-domain recurrence is standard, e.g. [Dechter, *Bucket Elimination*](https://arxiv.org/abs/1302.3572). The role of (1) and the (n)-preimage argument is to make the integer alphabet finite with **relative** accuracy and without dependence on the numerical upper scale. The diagonal-plus-low-rank mesh theorem in the companion note has an entirely different structural promise and a numerical magnitude bound; the weak-coupling bounded-degree note allows unbounded treewidth but assumes weak edge weights. Here the large edge regime is allowed, and graph width is fixed. [Barvinok, *Computing the Theta Series*](https://www.theoryofcomputing.org/articles/v022a009/), §2.1, analyzes randomized near-spectral and deterministic smooth cases rather than this sign/cut promise. These distinctions are about a supplied known Gaussian model, and do not assert that a standard random Ring-LWE instance admits such a precision matrix or tree decomposition.
