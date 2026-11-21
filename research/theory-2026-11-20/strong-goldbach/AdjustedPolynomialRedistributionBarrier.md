# The bounded-rank absorption necessarily has a signed compensation debt

Use the actual fixed-target \(N=2x\) rows of [AdjustedFirstTaperAllRank.md](AdjustedFirstTaperAllRank.md). On the genuine \(\mathcal Q_i\) profiles write \(w(s,q)=W_s(q)D_B(q)/\log q\), exactly positive, and let \(I_i\) be the actual source densities in (6) of [AdjustedTriprimePositiveBudget.md](AdjustedTriprimePositiveBudget.md). Thus \(I_1>.05097,\ I_2>.03290\) by its rational lower bounds. All averages below divide by \(\sum_{X\le x\le2X} M_{2x}\), not by a pointwise ratio or an unweighted average of ratios.

## 1. Polynomial detector: a genuine lower bound on the remaining signed mass

Let \(E'_j=\Lambda(m)-\log m[A_j(m)/(2j)+(1-1/(2j))G(m)]\) be the actual whole replacement of the first-taper note. Its weighted dyadic signed average tends to zero: the first-taper main is \((I_i+o(1))M_N\) uniformly on the true profile, the flat taper is a whole null, and the actual weighted \(\Lambda(m)\) term has mean \(I_i\). For the last statement use the independent genuine \(n\)-product and weighted reflected \(m\)-prime measures (the latter has ordinary PNT density \(1\) at scale \(X\)), with the central area \(3/2\) in that note. Proper prime powers are negligible. There is no fixed-target prime-pair main assumption.

For \(\epsilon\) used in the original \(Z=x^\epsilon\), on the entire true semiprime reflected slice \(m=pP\) with distinct primes \(p,P>Z\), \(G(m)=1\). The first taper \(A_j(m)\ge0\) by the second finite difference of the convex function \(t\mapsto(1-2t)_+^j\); this is an exact two-factor sign, not a rank-limited arithmetic mean. Thus \(E'_j(m)\le -(1-1/(2j))\log m\) there. The actual unordered semiprime measure with weight \(\log m\) at scale \(X\) has density
\[
 \frac12\int_\epsilon^{1-\epsilon}\frac{da}{a(1-a)}
                           =\log((1-\epsilon)/\epsilon).
\]
Indeed fix the exponent of the smaller prime, and count the other in its true proportional interval by ordinary PNT; equivalently use ordered labels and divide by \(2\). Fixed inner exponent margins in \(X\) give the same limit as the \(x\)-dependent cutoffs. The assumption \(p\ne P\) removes no mass at this scale.

Hence when the positive contribution of \(\Omega(m)\le R_0\), \(R_0\ge2\), is at most \(\xi M_N\) uniformly as in [AdjustedPolynomialRankAbsorption.md](AdjustedPolynomialRankAbsorption.md), the signed **remaining** dyadic average satisfies
\[
 \liminf_{X\to\infty}
 \frac{\sum_{X\le x\le2X}\sum_{\mathcal Q_i,\ \Omega(m)>R_0}
                          w(s,q)E'_j(m)}
      {\sum_{X\le x\le2X}M_{2x}}
 \ \ge\
  (1-\tfrac1{2j})I_i\log((1-\epsilon)/\epsilon)-\xi .
\tag{1}
\]
The bounded-rank positive result remains applicable to \(E'_j\): the pointwise cost of replacing \(C\) by \(C'_U\) is \(O_{R_0}(\log H)\) in those ranks, as already paid by the rough-\(q\) upper bound; the \(A_j\) extension is negligible in absolute sum. For all these dyadic products \(N=n+m\) is automatically even. The possible \((n,m)>1\) deletes power-small mass: any common prime exceeds a fixed positive power of \(X\), with at most \(O(X^2/p^2)\) integer pairs before bounded label and log weights. The area in \((n/X,m/X)\) is \(3/2\), and \(\sum M_{2x}\sim 3X^2/(2\log X)\) as in the earlier notes. This is the actual same-equation average.

This remains meaningful when the support of \(G\) is taken much farther out. In fact the bounded-rank absorption permits **any fixed \(0<\epsilon<1/2\)**, not just the small threshold used in the proof to group factors. Use the same flat taper with exponent \(R_0\), instead of \(R_0-1\), so its signed finite-difference test covers all participating factors even if none exceeds \(Z\). Keep the independent grouping cutoff \(\epsilon_0=1/(200R_0)\) in the true upper sieve (5) of that proof. When \(\epsilon>\epsilon_0\), all \(F\)-primes participate; if \(F=1\) the flat-defect bound is \(O_{R_0}(\rho)\) and (5) gives its weighted cost \(O_{R_0}(\rho M_N)\). If \(F>1\), the participating minimum is an \(F\)-prime, so the same layer integral up to \(\rho\) and reciprocal primes up to \(x^{\epsilon_0}\) give \(O_{R_0,\epsilon}(\rho(1+|\log\rho|)^{R_0-1}M_N)\). All large factors in the upper remain the genuine prime labels counted there. The zero shift uses \(Z<U\) eventually for any fixed \(\epsilon<1/2\), and its flat moment is unchanged. Thus no analytic reason here requires tying \(\epsilon\) to \(\epsilon_0\).

Even with such larger \(Z\), the power taper retains a semiprime debit. For \(R_0\ge3\), take \(\rho<1/(4R_0)\) and \(a_0=2\epsilon/R_0<.45\). On actual reflected semiprimes whose smaller exponent lies strictly between \(a_0\) and \(.45\), the larger factor exceeds \(Z\). With fixed interior margins and \(x\) large, \(u=\log p/\log Z\ge 1.9/R_0\), and
\[
    f_\rho(u)\le \exp[-R_0(u-\rho)]<1/2
\]
when \(u<1\), while \(f_\rho=0\) otherwise. Thus \(G(m)\ge1/2\), and in (1) one still has, instead of its logarithmic term, at least
\[
 \frac12(1-\tfrac1{2j}) I_i
                        \log\frac{.45(1-a_0)}{.55 a_0}.
\tag{2}
\]
For fixed \(\epsilon\) this grows as a positive multiple of \(\log R_0\) when the rank is chosen larger before the asymptotic. It is not a uniform estimate in growing \(R_0\). Taking \(Z\) close to \(x^{.49}\) therefore does not make the entire independent high-rank charge disappear for this high-degree flat power taper.

## 2. A more general rank-two versus rank-three tradeoff

Consider any fixed **size-only half-divisor kernel** \(K\) with \(K(0)=1\), continuous on \([1/4,5/12]\), and use the form
\[
 E_K(m)=\Lambda(m)-(\log m)\sum_{d\mid m,\ d<\sqrt m}
                              \mu(d)K(\log d/\log m).
\]
Suppose its actual \(w\)-weighted whole signed profile has zero dyadic mean, as for \(E'_j\) above. This is an assumption on the paid whole kernel (normally with slope \(-1\) at zero and a justified half-cutoff), not a claim it holds for every continuous \(K\). Suppose further that its limiting coefficient is nonpositive on all semiprime shapes whose smaller exponent belongs to \(J=(1/4,5/12)\), and all triprime shapes whose three exponents belong to \(J\). These are genuine profiles, each populated by the PNT product average on each open neighborhood, not arbitrary fake data on the equation. The pointwise conditions are necessarily
\[
        K(t)\le1\quad(t\in J),\qquad
        K(t_1)+K(t_2)+K(t_3)\le1
             \quad(t_i\in J,\ t_1+t_2+t_3=1).
\tag{3}
\]
Indeed the semiprime has just the smaller prime below the midpoint, and the triprime has all three singles but no pair below it.

To integrate (3), let \(V\) be uniform on \((0,1/2)\), randomly permute \((V,V+1/2,1-2V)\), and scale the three coordinates by \(1/6\), translating by \(1/4\). The triple sums to \(1\), and each marginal is uniform on \(J\): the first two unscaled slots in mixture supply the two half intervals with density \(2/3\), and the last slot is uniform with density \(1/3\). Thus the mean of \(K(t)\) on \(J\) is at most \(1/3\). Since \(1-K(t)\ge0\) there, the true reflected semiprime negative density satisfies
\[
 \int_J\frac{1-K(t)}{t(1-t)}\,dt
       \ \ge\ 4\int_J(1-K(t))\,dt
       \ \ge\ \frac49.
\tag{4}
\]
The measure is the same genuine smaller-prime calculation as in §1, with coefficient \(1-K(t)\), so after the actual dyadic additive constraint its cost is at least \((4/9)I_i\) in units of \(\sum M_{2x}\). This is \(>.022\) for \(\mathcal Q_1\) and \(>.014\) for \(\mathcal Q_2\) using only the rigorous lower bounds for \(I_i\).

In particular, if a kernel with (3) also makes all other \(\Omega(m)\le R_0\) positive parts at most \(\xi M_N\) uniformly, its matched whole zero mean forces the signed complement to have dyadic mean at least \((4/9)I_i-\xi\). That statement rules out seeking a small **independent** high-rank cap and then throwing away all the low-rank negatives for this class. It does not rule out a coupled estimate preserving those negatives, an aggregate rather than pointwise low-rank argument, a parity-sensitive coefficient using additional arithmetic, or a different route to Goldbach. The pairing needed by the problem remains genuinely signed.

## 3. Averaged calibration with a bounded absolutely continuous coupling

The pointwise sign conditions (3) can be replaced by a quantitative **genuine averaged** positive allowance. On the plane \(u_1+u_2+u_3=0\) with all \(u_i\in[-1/2,1/2]\), use the density
\[
       h_0(u_1,u_2)=2(|u_1|+|u_2|+|u_3|)
\]
relative to projected \(du_1\,du_2\). It has **exact uniform marginals** on \([-1/2,1/2]\): for \(u_1=v\ge0\), integrate over \(-1/2\le u_2\le 1/2-v\); the integral before the factor \(2\) is
\[
 v(1-v)+2\int_{-1/2}^{1/2-v}|u_2|\,du_2
       =v(1-v)+1/4+(1/2-v)^2=1/2 .
\]
Reflection handles \(v<0\), and symmetry gives all three marginals. At most one sign forms a singleton of total absolute value \(\le1/2\), so \(\sum|u_i|\le1\) and \(h_0\le2\). After scaling \(t_i=1/3+u_i/6\), the density \(h\) on \(t_i\in J,\ \sum t_i=1\) has uniform marginals on \(J\) and is bounded by \(72\) relative to \(dt_1\,dt_2\). This is absolutely continuous on the entire two-dimensional simplex region, not the singular curve used for purely pointwise calibration.

Let \(\xi_3\) be an upper bound on the actual dyadic limsup of the **positive** mass on just those reflected triprimes with exponents in \(J\), in units of \(\sum M_{2x}\). No pointwise condition on \(K(t)\) for semiprimes or triprimes is needed here. By the actual three-prime product PNT computation,
\[
  \frac{I_i}{6}\!
       \int_{\substack{t_1,t_2,t_3\in J\\t_1+t_2+t_3=1}}
         \frac{(K(t_1)+K(t_2)+K(t_3)-1)_+}{t_1t_2t_3}
                      \,dt_1\,dt_2
                  \ \le\ \xi_3 .
\]
The \(1/6\) is the genuine unlabeled-factor normalization; the additive dyadic area and even lattice are the same as above. The weights are bounded continuous on this interval; exponent walls have zero measure. Since \(t_1t_2t_3\le1/27\), the \(h\)-expectation of this positive defect is at most \(72(6/27)\xi_3/I_i=16\xi_3/I_i\). Exact uniform marginals then give
\[
             \frac{1}{|J|}\int_J K(t)\,dt
                 \ \le\ \frac{1+16\xi_3/I_i}{3}.
\]
The actual reflected semiprime negative mass, allowing any sign on its other side, is consequently at least
\[
 I_i\int_J\frac{(1-K(t))_+}{t(1-t)}\,dt
       \ \ge\ 4I_i\int_J(1-K(t))\,dt
       \ \ge\ \frac49 I_i-\frac{32}{9}\xi_3
\]
in the same normalized dyadic limit. Thus if the whole paid signed mean of \(E_K\) is zero and the actual bounded-rank positive mass is at most \(\xi M_N\) uniformly (or its normalized dyadic limsup is at most \(\xi\)), the signed complement has normalized dyadic liminf at least
\[
                         \frac49 I_i-\frac{32}{9}\xi_3-\xi .
\tag{5}
\]
In particular the pointwise hypotheses of §2 are not required when the true positive low-rank allowances can be made negligible. This is a quantitative averaged sign-balance restriction for the size-only class, not a bound on the final fixed-target signed sum.

## Comparison

Constant-sum couplings of fixed marginals are studied in the [complete mixability literature](https://sas.uwaterloo.ca/~wang/papers/2011Wang-Wang-JMVA.pdf); only the displayed elementary uniform coupling is used here. The [Arneth September compensation paper](https://zenodo.org/records/23016346) formulates a different conditional signed-capacity approach. The repository’s [singly marked calibration obstruction](marked_calibration_barrier/Proof.md) is likewise different: it concerns actual opposite prime-pair legs, not these two adjusted quotient supports and reflected size-only kernels. The November 21 comparison makes no priority claim.
