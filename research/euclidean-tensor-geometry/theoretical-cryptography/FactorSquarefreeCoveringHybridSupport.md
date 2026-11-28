# Local support of squarefree distinct covering systems of minimum seven

Let \(Q\) be the least common multiple of the moduli in a finite distinct covering system of the integers. A modulus support is the set of prime factors of that modulus.

**Theorem.** Suppose all moduli are squarefree and at least seven. Then:

* Every prime up to **31** divides \(Q\).
* At least **15, 21, 36, 58, 78, 92, 115, 131** prime divisors of \(Q\) are at most **53, 89, 211, 461, 811, 1153, 2083, 3821**, respectively.
* At least one of the actual moduli **10 or 15** occurs. At least four of **\(10,14,15,21,30,35,42\)** occur.

These are necessary restrictions on a possible system. By [Dai–Li–Li–Yi, Theorem 1.3(ii)](https://arxiv.org/abs/2611.15110), such a system must also contain modulus 7. Their conclusion is that the minimum is at most 7, not that a minimum-7 example exists. The previous [prime-support note](FactorSquarefreeCoveringPrimeSupport.md) gave the necessary primes \(2,3,5,7\) and a lower bound of 142 prime divisors without a small-prime cutoff. The present profile bounds impose local abundance, rather than implying 131 is a replacement for that global count. We do not settle the existence of a minimum-7 system.

The certificate combines a joint finite prefix and an independent analytic tail. The combination matters: a valid tail is first obtained as an increasing directionally convex *vector* functional; only then is its value on the scalar comparison states bounded by a cubic polynomial.

## 1. The exact squarefree comparison

Use the CRT product, introducing a class at its greatest prime \(p\). Given the previous coordinates, write \(\alpha\) for the uniform fraction of the \(p\)-coordinate hit by the newly introduced classes. Choose a fixed \(0\le\delta_p\le1/2\) and write \(c=1/(1-\delta_p)\), \(g(a)=c(a-\delta_p)_+\), and \(\kappa(a)=1/(1-\min(a,\delta_p))\). Give the covered slice mass \(g(\alpha)\), uniformly inside and outside the covered part. This preserves the earlier marginal, and the conditional mass of each residue is at most \(\kappa(\alpha)/p\). Thus the sum of the resulting stage masses is at least one for a cover.

For a continuation functional \(\Phi\) of the vector of remaining support counts, let \(A_0,A_1\) consist of the columns of counts omitting and containing \(p\), the latter with \(p\) deleted. If \(\Phi\) is increasing and directionally convex, the conditional expectation is at most
\[
 V_{\kappa(a)}=\Phi(A_0)+\frac{\kappa(a)}p\bigl(\Phi(A_0+A_1)-\Phi(A_0)\bigr),
\]
where \(a\) is the number of eligible singleton counts for \(p\) divided by \(p\), which upper-bounds \(\alpha\). This follows by telescoping the increments of \(\Phi\) and bounding the probability of each active term by \(\kappa(a)/p\). The joint repair in [Dai–Li–Li–Yi, Lemma 3.2](https://arxiv.org/pdf/2611.15110), at \(\vartheta=1/c\), gives the increasing directionally convex upper functional \(g(a)+\max\{V_{\kappa(a)},\,V_c-(c-\kappa(a))/c\}\). For a formal upper count \(a>1\) it remains valid by the same algebra: throughout \(a\ge\delta_p\), \(\kappa=c\) and \(g\) is affine.

Taking all admissible supports gives a monotone upper bound because each actual full support contributes at most one class. In the completed comparison a previous prime is either fully active or fully inactive. With \(t\) the number of subsets of active predecessors, the two continuations have \(t\) and \(2t\), and the singleton count \(pa\) is \(0\) for \(p=2,3\), \(t-1\) for \(p=5\), and \(t\) for \(p\ge7\). The missing \(1\) at \(p=5\) excludes modulus 5; the 7 class itself is not silently excluded. Thus for an upper continuation \(H\) we use
\[
  (T_p H)(t)=g(a)+H(t)+
      \max\left\{\kappa(a)D,\ cD-\frac{c-\kappa(a)}c\right\},\qquad
      D=\frac{H(2t)-H(t)}p .
  \tag{1}
\]
Both branches are convex combinations of the two values of \(H\), plus fixed scalar terms. In particular the evaluation on these completed states is pointwise monotone in \(H\).

## 2. Combining a joint prefix with an infinite tail

Take the prefix through the \(N=12000\)-th absolute prime \(p_N\). Consider any finite support, even one whose largest prime is much greater than \(p_N\). At every stage after \(p_N\), use \(\delta=1/2\) and the weaker comparison \(g(a)+V_c\) on support vectors, rather than the repaired joint operator. This is an increasing directionally convex functional of the whole finite input vector: \(g\) is an increasing convex function of a nonnegative linear form, and \(V_c\) is a constant positive mixture of compositions of the continuation with nonnegative linear maps. Induction from zero at the last coordinate therefore makes it a valid continuation for applying the joint vector operator through the prefix.

On any completed prefix state \(t\), all later admissibility conditions are vacuous and the weaker tail is a scalar process. If \(X\) denotes the current state, it doubles at each prime \(p>p_N\) with probability \(2/p\), independently. Its stage contribution is bounded by
\[
 \frac2p\,{\mathbb E}(X-p/2)_+
       \ \le\ \frac{32}{27p^3}{\mathbb E}X^3 ,
\]
using \((x-A)_+\le4x^3/(27A^2)\) for \(x\ge0\). The third moment grows by the factor \(1+14/p\). For all prime indices \(j>N\), [Dusart's bound](https://doi.org/10.1090/S0025-5718-99-01037-6) gives \(p_j>10j\), since \(\log j>9\) and \(\log\log j>2\). The moment just before index \(j\) is at most \(t^3(j/N)^{7/5}\), whether some of those primes are omitted or not. Therefore all tail stages together cost at most
\[
  \frac{32t^3}{27\cdot10^3N^{7/5}}\sum_{j>N} j^{-8/5}
       \ \le\ \frac{32t^3}{16200N^2}.
  \tag{2}
\]
For each finite full-vector comparison, (2) bounds its weaker tail at all completed prefix states. We **do not** need to extend the cubic in the scalar \(t\) to a directionally convex function of arbitrary support vectors. The exact weaker tail before that replacement already has the required property; pointwise monotonicity of (1) then allows the cubic inside the scalar computation. This distinction lets the finite prefix exploit the sharper conditional caps without a limiting vector argument.

## 3. Ordered prime profiles and early missing moduli

For fixed \(\delta\), \(t\), and increasing continuation \(H\), the two branches in (1) both decrease when an available prime at least 7 is increased. Indeed, \(a=t/p\), \(g(a)\), \(\kappa(a)\) and \(D\) decrease, while \(c-\kappa(a)\) increases. This argument uses the same distortion parameter at the matched positions. A finite actual support can be completed with arbitrary available unused primes since including all possible admissible classes is an upper comparison. For fixed forbidden primes, we may therefore work with the entire ordered prime profile skipping the forbidden ones, use (2), and run (1) in the prefix. Alternatively, for any actual ordered list which is coordinatewise at least a given packed comparison list, use the packed list's distortion parameters at each matched position before the same comparison. One may pad a finite list beyond its last prime for this monotone majorization. The upper continuation in the exact comparison is increasing from its vector construction; the scalar computation uses only its values and pointwise upper bounds.

For the abundance tests, the first four primes are known to occur by the previous result (or the present single-prime tests). If at least \(b\) primes are missing among the first \(m\), the coordinatewise smallest packed profile consists of the first \(m-b\) primes, followed by all primes of index \(>m\). To see this, the \(i\)-th surviving prime has at least index \(i\) for \(i\le m-b\); for \(i>m-b\) its index is at least \(m+i-(m-b)\). This packed profile is what is checked; no availability beyond the claimed small cutoff is assumed.

To forbid individual early moduli instead of prime factors, retain an active/inactive bit for each processed prime up to and including the greatest prime in a forbidden modulus. The comparison counts for the later complete supports are still \(t=2^{\#\mathrm{active}}\). At an early stage, the singleton count is exactly the number of subsets of its active predecessors whose product times \(p\) is at least seven **and** is not a forbidden modulus. The two child states append the current prime as inactive or active. This is the same joint vector recursion, only recording the low coordinates needed to compute the exact admissibility masks. In particular, forbidding modulus 10 does not forbid prime 5 or any multiple of 10 of a different modulus.

## 4. Directed-integer replay

The [checker](verify_factor_squarefree_covering_hybrid_support.py) uses the following fixed parameters; \(p\delta\) is in terms of the absolute prime index, and a half entry means \(\delta=1/2\):
 
| Index | \(p\delta\) | Index | \(p\delta\) |
|---|---:|---|---:|
| 1–2 | 0 | 32–50 | 64 |
| 3 | 1 | 51–54 | half |
| 4 | 2 | 55–80 | 128 |
| 5–7 | 4 | 81–97 | half |
| 8–11 | 8 | 98–125 | 256 |
| 12–19 | 16 | 126 onward | half |
| 20–31 | 32 | | |

For the test excluding prime 31 only, additionally choose \(\delta_{37}=8/37,\ \delta_{71}=16/71\). All tests start with (2), process the indicated packed prefix backward, and compare its value at \(t=1\) to one. For \(t\ge2^{18}\) every active prefix stage has \(a\ge\delta_p\); this is checked directly. The continuation on this tail is exactly cubic-affine, \(At^3+Bt+C\), for the scalar comparison starting from (2). The coefficients update by
\[
 A\mapsto A(1+7c/p),\quad
 B\mapsto B(1+c/p)+\mathbf1_{p\ge5}c/p,\quad
 C\mapsto C-\mathbf1_{p\ge5}c(\mathbf1_{p=5}/p+\delta_p).
\]
There are 18 other dyadic states. Each scalar coefficient and value is rounded upward at scale \(10^{42}\). The expectation branches are evaluated as positive mixtures of upper values; the repair penalty is subtracted rounded downward. No sign assumption on the difference of two rounded values is needed, since the mixture is monotone in each. The cubic and affine coefficients also enter the boundary state with nonnegative powers of \(t\).

The largest upper value when omitting one prime through 31 is smaller than 0.999 (for the omitted 31). For the abundance rows, the exact rational upper bounds are below the following upward-rounded decimals:

| Cutoff | Required factors at or below cutoff | Contradiction bound for fewer |
|---:|---:|---:|
| 53 | 15 | 0.995656 |
| 89 | 21 | 0.990494 |
| 211 | 36 | 0.997264 |
| 461 | 58 | 0.999641 |
| 811 | 78 | 0.998943 |
| 1153 | 92 | 0.999477 |
| 2083 | 115 | 0.999736 |
| 3821 | 131 | 0.999946 |

For modulus pair \(\{10,15\}\) the corresponding bound is below 0.998369. For every one of the 35 four-element exclusions from \(\{10,14,15,21,30,35,42\}\) the corresponding bound is below 0.975197. Larger forbidden sets only lower the comparison. In all cases the exact strict inequality excludes the given possibility.

Run `python3 verify_factor_squarefree_covering_hybrid_support.py`. The exact checks use only the Python standard library. They do not decide unrestricted existence or treat any nonsquarefree odd covering system.
