# What the radial comparison gives in dimension two

This is an upper bound, not a solution of the planar conjecture. In the notation of the main proof its angular reduction applies also in dimension two. It yields
\[
 \rho_2\le \max_{0\le x\le 1}F_2(x)<2573/2000.
\]
Here \(F_2(x)=\mathbb E\sqrt{(1+x)(1-x\cos\Theta)}\), with \(\Theta\) uniform on a full turn. Only the displayed rational bound is used.

Since the odd angular moments vanish, the binomial series in the main proof and the even cosine moments give
\[
 F_2(x)\le U(x):=\sqrt{1+x}\,(1-P(x)),\qquad
 P(x)=\sum_{j=1}^{12}\frac{\binom{4j}{2j}\binom{2j}{j}}
             {(4j-1)2^{6j}}x^{2j}.
\]
Indeed omitted terms are subtracted and nonnegative; all coefficients come from \(-[y^{2j}]\sqrt{1-y}\) times \(\binom{2j}j/4^j\). Also \(1-P(x)>0\) on the closed interval: it is at least the strictly positive angular integral \(F_2(x)/\sqrt{1+x}\). Thus \(U\) is concave: in the second derivative of the product the terms from the two concave nonnegative factors are nonpositive, as is the cross term since the factors have opposite monotonicities.

Let \(a=369/400\), and put
\[
 D=\frac{1-P(a)}2-(1+a)P'(a),\qquad
 V=(1+a)(1-P(a))+(1-a)D.
\]
Direct rational substitution gives \(0<D<1/1600\) and \(0<V<17836/10000\). For reproducibility the exact loop requires only the twelve displayed rational coefficients (see the checker). Because \(U'(a)=D/\sqrt{1+a}>0\), the tangent line to \(U\) at \(a\) takes its maximum on \([0,1]\) at 1. Therefore
\[
 U(x)\le\frac{V}{\sqrt{1+a}}
 <\frac{17836/10000}{\sqrt{769/400}}<\frac{2573}{2000},
\]
where the last strict inequality follows by squaring rational numbers. This is below the published 1.3546 upper bound of Ismailescu and Park (2014) and the 4/3 bound announced in Woosung Jung’s Society for Science competition abstract, but the lower bound \(4/\pi\) is smaller and equality is not determined here.
