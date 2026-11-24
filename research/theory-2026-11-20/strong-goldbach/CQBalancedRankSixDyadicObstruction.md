# The remaining balanced rank-six sector already exceeds the fixed reserve on dyadic mean

Use the identical canonical sharp CQ \(H\), true same reflection \(x+y=N,\ (x,N)=1,\ x/N\in J\Subset(1/3,2/3)\), \(M_N=|J|N\mathfrak S(N)\). This is a quantitative specialization of the **method** of [the pinned DyadicExterior proof](cubic_quintic_sharp/DyadicExterior.md): the specific rank-six sector and its exact intersections are new here, not a new formula for averages in general. It is not a fixed-target estimate and says nothing about exceptional/no-pair targets.

Let \(B_6\) be the actual negative magnitude \(-H\) on squarefree rank-six arguments whose true least prime factor is in \((N^{.04},N^{.105}]\) and whose largest own-log angle \(w<.54\), and zero elsewhere. Rank six is strictly negative everywhere on its squarefree simplex as proved in [the asymmetric-plateau proof](CQAsymmetricStripRankSixPlateau.md). Consider the complete signed contribution \(E_6(N)\) on the physical union where at least one arm has \(B_6>0\), **after removing all previously paid rows of the canonical \(+.0378M_N\) decomposition**. The positive supports cannot intersect this union by its actual negative arm. The older negative/tiny one-arm types, \(A,T,W,Z,G\), are each disjoint from the defining support of \(B_6\) and from each other. Here \(A\) is the true high negative floor .105 type, \(T=H1_{P^-\le N^{1/5000}}\) is the signed tiny arm, \(W,Z\) the prior rank-eight-plus negative arms, and \(G\) the dominant rank-six \(w\ge.54\) arm at .04 floor. On an actual row, at most one of those types can be opposite the \(B_6\) arm; every pairwise overlap is exact two oriented crossings, and no triple intersection occurs.

**Claim.**
\[
 \lim_{X\to\infty}\frac{\sum_{X<N\le2X,\ 2\mid N} E_6(N)}
                       {\sum_{X<N\le2X,\ 2\mid N} M_N}
  <-.0459 .
\]
In particular a uniform lower \(E_6(N)\ge-(.0378+o(1))M_N\) at all even targets is false already on this one still unpaid actual sector. Positive help elsewhere, or a restriction to genuine no-pair targets, remains essential. This does not imply the same sign at any prescribed fixed target.

## 1. A simple rigorous ordinary lower on the actual unpaid side

Let \((u_i)_{1}^6\) be the true own-log widths and \(b_6(t)\) the analytic density of the centered sum of their six uniforms. With \(Q=\sum u_i^2\), the variance of that sum is \(Q/12\). The density is symmetric unimodal and has maximum \(b=b_6(0)>0\). Any density capped by \(b\) has centered second moment at least \(1/(12b^2)\): indeed \(\Pr(|X|\le t)\le2bt\), and integrate \(2t(1-2bt)\) from 0 to \(1/(2b)\). Thus \(b_6(0)\ge1/\sqrt Q\). The exact rank-six magnitude divided by \(\prod u_i\) is \(3840b_6(0)-96b_6''(0)\), with \(b_6''(0)\le0\), so it is at least \(3840/\sqrt Q\). This is why the genuine prime harmonic denominator cancels in the estimate without needing any assumption on factor-count pairing.

For the ordinary symmetric sorted simplex with \(u_i\ge d\), put
\[
 V_d=\frac{(1-6d)^5}{6!\,5!},\qquad
 Q_d=6d^2+2d(1-6d)+\frac{2}{7}(1-6d)^2 .
\]
These are its coordinate volume and its average \(\sum u_i^2\): use the affine transform to the uniform 6-coordinate unit simplex, where the sum of coordinate squares has mean \(2/7\), and divide by \(6!\) for actual sorted distinct labels. Thus the actual fixed floor **band** \(a=.04<\min u_i\le h=.105\) has uniform volume \(V_a-V_h\) and mean squared sum \((V_aQ_a-V_hQ_h)/(V_a-V_h)\). Jensen for \(Q\mapsto Q^{-1/2}\) and the true maximal-angle \(w\ge.54\) already-paid ordinary mass upper .000546 imply
\[
 m(B_6)\ \ge\
 \frac{3840(V_a-V_h)}
      {\sqrt{(V_aQ_a-V_hQ_h)/(V_a-V_h)}}-.000546 > .02197.
\]
As in the earlier compact-source proof the physical true least floor \(N^d\) and own-log angular bounds differ only by an \(O_J(1/L)\) collar, removed by ordinary genuine compact angular PNT. The last inequality is rational: the mean squared sum is \(0.2369037594032\ldots<(.48674)^2\); replacing its root by .48674 yields lower \(0.0219728114941\ldots\). Exact rational cross-products checked.

## 2. Signed union and already paid overlaps in one actual dyadic measure

Write \(b=m(B_6)\), \(m_T=m(T)<0\). In every fixed target the full literal union of \(B_6\)-arms has exact signed covariance \(-\langle B_6,H\rangle-\langle H,B_6\rangle-\langle B_6,B_6\rangle\). All these products have dyadic normalized means \(b,b,b^2\) as in DyadicExterior: one genuine factor-product arm is compact, \(H\) has ordinary signed mass 1 on odd integers in full interval normalization, and the old uniform absolute ordinary bound allows signed rectangle approximation. Shared-prime exclusions cost \(o(X^2)\) since one arm is polynomially rough. The old singular-series mean normalizes the wedge area correctly. This averaging is applied only after fixing the genuine same-target expressions and summing over targets. It does not identify a fixed target arm with an independent ordinary draw.

On an actual overlap with old negative types \(A,W,Z,G\) the sign is positive, because both arms have negative true \(H\), one in each disjoint support. In particular the high negative magnitude \(A\) includes its true rank-five component \(A_5\), which has exact ordinary mass
\[
 a_5=m(A_5)=\frac23(1-5(.105))^4=\frac23(.475)^4=.0339377604166\ldots
\]
by the global polynomial rank-five formula \(-1920\prod_{i=1}^5u_i\), which cancels the harmonic denominator. The two \(B_6\)–\(A_5\) crossings therefore have total real dyadic mean \(2ba_5\) and are part of the subtracted positive intersections; other negative overlaps can only make the remaining dyadic mean smaller.

The overlap with the true tiny union is not signed pointwise. Its exact signed expression is \(-\langle B_6,T\rangle-\langle T,B_6\rangle\). Its dyadic mean is \(-2bm_T>0\) by writing \(T=H-H1_{P^->N^{1/5000}}\) first. This avoids using unproved angular compactness of \(T\): the first product \(B_6\times H\) uses the old ordinary absolute bound for unrestricted \(H\), while the second has a genuinely fixed positive angular floor and bounded rank. Its ordinary signed mass is \(1-m_T\) by the same subtraction, with \(m_T<0\) from ExplicitTinyUnion (the precise signed polynomial is not needed). The floors may be tied to the dyadic scale replacing \(N\) by \(X\) exactly as in DyadicExterior, without opening fixed-target rows.

Thus all these pair means exist, every physical overlap is subtracted once, and the limiting mean of the **still unpaid residual rank-six union** is at most \(-2b-b^2-2ba_5\). Using \(b>.02197\) this upper is less than \(-.04591390609<-.0459\). The actual good blocks (including the newly published asymmetric strip) are absent from this mean exactly by signs. This is not a claim against exploiting conditional signed compensation across this sector and other unpaid positive regions; it is a reason to look for such compensation rather than charging this chamber independently against a fixed constant.
