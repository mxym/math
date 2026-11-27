# Effective finiteness of the equal-shift binomial collisions

Let \(d\ge1\) be an integer. We consider positive entries in the ordinary finite part of Pascal's triangle and ask when
\[
             \binom{n}{k}=\binom{n-d}{k+d},
             \qquad k\ge1,\quad n-d\ge k+d.                 \tag{1}
\]
We do not assume that either entry lies on the left half of its row.

**Theorem.** If \(d\ge2\), every solution of (1) has
\[
 u:=n-k < 
 \begin{cases}
 128d^2+d,&d\equiv1,5\pmod6,\\
 11d^2+d,&\text{otherwise}.
 \end{cases}                                                \tag{2}
\]
Also \(k<u\), so this bounds the entire row. Consequently \(d=1\) is the only **fixed equal shift** that admits infinitely many collisions. Moreover, \(d=2\) is ruled out by a direct square-gap argument, and the companion exact certificate rules out every \(2\le d\le128\), with no upper bound on the row in this last assertion.

This addresses the equal-shift subfamily of the *fixed-offset* question considered by [Hugo Jenkins](https://arxiv.org/abs/1411.4111). His general finiteness theorem is for unequal shifts; his separate quartic computation establishes the finiteness of the \(d=2\) case. The infinite \(d=1\) case is the [Lind–Singmaster family](https://www.fq.math.ca/Scanned/13-4/singmaster.pdf), not a claim of this note. Bounds (2) are effective and uniform. They are not a bound on the total number of binomial representations, and do not restrict arbitrary unequal shifts.

## 1. Factoring and centering

With \(w=n(k+1)\), cancellation of factorials in (1) gives
\[
 \prod_{i=0}^{d-1}\bigl(w+i(u-1)-i^2\bigr)
       =\prod_{r=0}^{2d-1}(u-r).                            \tag{3}
\]
Indeed pair \(n-i\) with \(k+1+i\). All factors are positive at a solution, and \(u\ge2d\). Since every summand \(i(u-1)-i^2\) is nonnegative there, (3) gives \(w^d<u^{2d}\). As \(w=(u+k)(k+1)\), it follows that \(k<u\).

Set \(a=(d-1)/2,\ v=u-(2d-1)/2,\ W=w+a(u-1)-a^2\). Define \(J=\{-a,-a+1,\ldots,a\}\). Pair the factors on the right of (3) across their midpoint; then (3) becomes
\[
 \prod_{j\in J}\bigl(W+(v-\tfrac12)j-j^2\bigr)
     =\prod_{\ell=0}^{d-1}\bigl(v^2-(\ell+\tfrac12)^2\bigr). \tag{4}
\]
On the domain where all its left factors are positive, the product is strictly increasing in \(W\). This is the branch relevant to integer binomial coefficients.

The quadratic approximation and its signed first correction are
\[
 \begin{aligned}
 E&=-\frac{5d^2+1}{24}, & D&=-\frac{d^2-1}{24},\\
 Q&=v^2+E+D/v, &
 q_0&=u^2-\frac{5d-3}{2}u+\frac{(d-1)(25d+1)}{24}.
 \end{aligned}
\]
Uncentering \(v^2+E\) gives \(q_0\). We prove the explicit estimate, whenever \(d\ge2,\ v\ge2d\),
\[
                  \left|w-q_0-\frac{D}{v}\right|
                          <\frac{4d^4}{v^2}.                \tag{5}
\]

## 2. Uniform error in the root

Let \(F(W)\) be the average logarithm of the left factors of (4) divided by \(v^2\), minus the corresponding average on the right. The logarithms are real on the positive branch. To calculate \(F(Q)\), use symmetry under \(j\mapsto-j\), writing \(z=j^2\) and expressing each paired average on the left as half the logarithm of a normalized product. The product is \(1+X_j\), where
\[
 X_j=\frac{2E-3z}{v^2}
          +\frac{2D+z}{v^3}
          +\frac{(E-z+D/v)^2-z/4}{v^4}.
\]
The right terms are \(\log(1-(\ell+\tfrac12)^2/v^2)\). The moments
\[
 \frac{1}{d}\sum_{j\in J}j^2=\frac{d^2-1}{12},\qquad
 \frac{1}{d}\sum_{\ell=0}^{d-1}(\ell+\tfrac12)^2
                       =\frac{4d^2-1}{12}
\]
show exact cancellation of the \(v^{-2}\) and \(v^{-3}\) terms of \(F(Q)\).

Here are explicit remainder bounds. We have \(z\le d^2/4,\ |E|\le7d^2/32,\ |D|\le d^2/24\), and \(v\ge2d\ge4\). Thus \(|E-z+D/v|\le d^2/2\), and both its square and \(z/4\) are at most \(d^4/4\). It follows that \(|X_j|\le 3d^2/(2v^2)\le3/8\). For \(|x|<1\) we use
\[
              |\log(1+x)-x|\le \frac{x^2}{2(1-|x|)} .
\]
The log error in the left average is at most \(\tfrac9{10}d^4/v^4\), plus \(\tfrac18 d^4/v^4\) from the displayed \(v^{-4}\) term. On the right \((\ell+\tfrac12)^2/v^2\le1/4\), so the log error is at most \(\tfrac23 d^4/v^4\). Hence \(|F(Q)|<2d^4/v^4\).

On \(|W-Q|\le4d^4/v^2\), all the left factors of (4) lie strictly between 0 and \(2v^2\): \(Q/v^2\in[7/8,1]\), the normalized shift is at most \(1/4\), and the normalized \(j\)-offset is bounded by \(d/(2v)+d^2/(4v^2)\le5/16\). Therefore \(F'(W)>1/(2v^2)\). The endpoints of this interval have \(F\) of opposite signs, and monotonicity identifies the unique positive-branch root. This proves (5), without an asymptotic assumption holding \(d\) fixed.

## 3. The lattice test

In all cases \(q_0\in\frac1{24}\mathbb Z\). For odd \(d\) its linear coefficient in \(u\) is integral, and the constant term is integral exactly when \(d\not\equiv0\pmod3\), using divisibility of \((d-1)(25d+1)\) by 8. For even \(d\) that numerator is odd and the linear term cannot cancel its denominator's odd numerator over 24. Thus \(q_0\) is integral exactly at \(d\equiv1,5\pmod6\).

If \(q_0\) is not integral and \(v\ge11d^2\), then (5) gives
\[
 |w-q_0|<\frac1{24\cdot11}+\frac4{11^2}<\frac1{24}.
\]
This excludes an integer \(w\). If \(q_0\) is integral, use \(-D=(d^2-1)/24\ge d^2/32\). For \(v\ge128d^2\), the \(4d^4/v^2\) error is no larger than \(-D/v\). In fact (5) is strict and the lower error plus \(-D/v\) has magnitude less than \(1/24\). Thus \(q_0-1/24<w<q_0\), again excluding the integer \(w\). The definition of \(v\) now implies (2).

The cancellation of the first two moments is essential here: a bounded error alone would not distinguish the \(q_0\)-integral residue classes. Their first signed drift puts the root in an interval ending strictly below a lattice point.

## 4. Complete checks of small shifts

At \(d=2\), (3) is \(w(w+u-2)=u(u-1)(u-2)(u-3)\). Its discriminant is
\[
 (2u^2-6u+2)^2+u(u-4).
\]
For \(u>4\) this lies strictly between the indicated square and the next square, since the remaining gap is \(3u^2-8u+5>0\). For \(u=4\) the positive root is \(w=4\), which corresponds only to \(k=0\). This gives exact nonexistence at \(d=2\).

[The companion script](verify_factor_singmaster_balanced_shifts.py) checks every remaining \(u\) allowed by (2) for each \(2\le d\le128\). At \(2d\le u<3d\) it directly bisects the increasing integer left-hand product as a function of \(k\). At \(u\ge3d\) it uses (5) to restrict \(w\) to a rational interval; the candidate \(k\)-interval is then recovered by exact integer square roots for \(w=(u+k)(k+1)\). Every candidate is tested by exact products. The verifier also independently checks the moment identities, the root enclosures at selected integer inputs, and the known \(d=1\) example. The small-shift result is an exact enumeration *after* the analytic cutoff, not a numerical search up to a fixed Pascal row.

[Blokhuis–Brouwer–de Weger](https://arxiv.org/abs/1707.06893) classify collisions in a large finite box (\(n\le10^6\) or common entry \(\le10^{60}\)) and several specific types of index pairs. Their proposed classification in full is much stronger than (2). The global multiplicity directions of [Matomäki–Radziwiłł–Shao–Tao–Teräväinen](https://arxiv.org/abs/2106.03335), [Whitmore](https://hexagonmath.org/pdf/2611.00106v1), and this repository's [sharper projection note](FactorSingmasterSharperProjection.md) are distinct. No general multiplicity improvement or Lean verification is asserted here.
