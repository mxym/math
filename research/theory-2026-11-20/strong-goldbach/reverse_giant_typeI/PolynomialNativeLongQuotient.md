# Completing the actual long quotient in the polynomial native score

Use the exact all-even score, positive cutoffs \(U_i=N^{\eta_i}\), and fixed-gap interval \(I\) of [PolynomialNative.md](PolynomialNative.md). Thus \(x=Af\), \(y=N-x=mCh\), \(f,h\) are genuine primes with their genuine logarithmic weights, and the sum retains both native \(H_{U_i}\)'s, the actual target-unit and \(z\)-roughness gates, \(y/m\in I\), and the strict short-divisor sum \(Q_y(m)\). Fix independent real subintervals of dyads
\[
 f\asymp N^\alpha,\qquad h\asymp N^\theta,\qquad m\asymp N^\nu
\]
with positive fixed exponents on the literal calibrated support; one may also impose an independent interval on the actual product \(mh\). In the first part below no dyadic restriction on \(h\) is needed. This is a companion to [PolynomialNativePrimeInverse.md](PolynomialNativePrimeInverse.md), which keeps the entire polynomial quotient grouped in the modulus. Here instead an exact completion is performed on the integer quotient itself.

**Theorem.** There are two estimates on the same score, both uniform at each even target:

1. If \(\alpha+\eta_x<\nu\) by a fixed margin, the portion with these \(f,m\) intervals has signed total \(O_D(NL^{-D})\) for every fixed \(D>0\), with **all** genuine \(h\)'s on the calibrated support. One may also keep any independent real \(h\)- and \(mh\)-intervals.
2. On a true \(h\)-dyad, the same estimate holds under the fixed strict margins
\[
\begin{split}
 &\eta_x<\min(\alpha,1-\alpha),\qquad
     \nu+\theta+\eta_x+\eta_r<1,\\
 & \tfrac32\alpha+\theta+2\eta_x+\eta_r<1.                           \tag{1}
\end{split}
\]
No radical condition or coverage by banks is used. The estimates on overlapping boxes are not added.

For example choose \(\gamma=.24,\ \eta_x=\eta_r=.0001,\ W_x=N^{.10}, W_r=N^{.20}\) in the polynomial calibration. Then \((\alpha,\theta,\nu)=(.34,.48,.23)\) has effective \(mh\) exponent \(.71\), outside the short-prime condition \(X\ge Q^{1/2}\) of the preceding inverse chart. Its two error exponents in (1) are \(.7102\) and \(.9903\). Part 1 covers the entire genuine \(h\)-range at \(f\asymp N^{.15}, m\asymp N^{.23}\), including \((.15,.76,.23)\) with effective \(mh\) exponent \(.99\) and part 2 errors \(.9902\), \(.9853\). The actual right prime-product leg has scale \(Ch\asymp N^{.77}\) in both examples and fits the fixed-gap calibration. These are examples of allowed scales, not lower bounds on the number of physical rows.

## 1. Whole \(h\)-range when \(m\) is longer than the left prime and short label combined

Open the two actual \(H\)-divisor labels \(d\le U_x,e\le U_r\) and the two positive-error factorial roughness labels \(e_1,e_2\) as in [PolynomialNativePrimeInverse.md, §1](PolynomialNativePrimeInverse.md). For fixed \(f,h,d,e,e_1,e_2\), fix also the integer \(c=C/(e e_2)\), and leave the true \(m\) and the other free integer in \(x=f d e_1 a\) unpinned. Open \(b<T_y,\ b\mid m\) from \(Q_y(m)\) and write \(m=b n\). The exact two-free equation is now
\[
  (f d e_1)a+(b h e e_2 c)n=N .
\]
For unit compatible outer products, count the exact progression in \(x\); its density is
\[
    \frac{\varphi(N)}{N(f d e_1)(b h e e_2 c)}
\]
and its unit floor is \(O(\tau(N))\). All arithmetic variables and divisor products here are literal. The actual cofactor cutoff \(C>U_r\) is a test on the fixed \(e e_2 c\); \(A>U_x\) is an interval endpoint in \(x\). At fixed outer parameters every original \(m\)-, \(mh\)-, and \(y/m=Ch\)-constraint is either an empty condition or a real interval condition in \(x\). The strict \(b<T_y\) is also an actual real endpoint \(y>Bb\); no smoothing is needed for it in this calculation.

At the actual \(m\)-scale \(M\asymp N^\nu\) there is the necessary whole-product bound
\[
    h c\ll N/(M e e_2).
\]
Even dropping primality in the **count of outer choices**, pairs \((h,c)\) are \(O((N/(M e e_2))L)\), by the true divisor count, uniformly even when that ratio is below one (then the set is empty after a fixed constant adjustment). Thus the total floor with fixed log weights and all short labels is
\[
  N^{1+\alpha-\nu+\eta_x+o(1)};
\]
\(d\le U_x\) costs \(N^{\eta_x}\), but \(e\le U_r\) is summed with \(1/e\) from the actual count, not by its cardinality. The \(b<T_y\ll S\) and roughness labels cost only a subpower count. This is power-small under part 1. The same floor estimate applies to positive omitted roughness labels; their main reciprocal mass is arbitrarily log-small by the factorial bound, also directly payable by physical multiples.

In the real main fix \(x\) and \(f,h,d,e,e_1,e_2,c\). The physical \(m=y/(C h)\) is independent of \(b\); this is a real integration variable even though integer rows had \(b\mid m\). The only \(b\)-dependent compatibility is \((b,N f d e_1)=1\), since sharing primes with another factor on the same right leg does not change a product modulus. The true \(b<T_y\) sum is therefore the uniform masked \(\mu(b)/b\) harmonic at \(T_y\asymp S\), of size \(O_D(L^{-D})\) to every prescribed precision. All other sums can now be bounded reciprocally with fixed log powers. This proves part 1 with the actual \(Q_y\) and the entire genuine \(h\)-support; no replacement of \(h\) by an integer model is made.

## 2. Long-quotient completion when the previous floor does not suffice

Take the exact contour, label openings and zero mode from [PolynomialNativePrimeInverse.md, §1](PolynomialNativePrimeInverse.md). The contours involving \(m\), and the strict \(d<T_y\) inside \(Q_y(m)\), are frozen on the same positive-error log mesh, paid by true multiples of \(m\) or \(d\) in \(y\). On each cell \(T\asymp S\) in the resulting \(Q_T(m)\) is fixed, along with the real \(m\)-interval. The two short native divisor labels are \(d\le U_x,e\le U_r\), each \(z\)-rough, and the actual free-roughness labels are \(e_1,e_2=N^{o(1)}\). Sizes and cardinalities of the latter labels are subpower at every requested log precision. Their positive omitted-degree tails are paid by actual multiples in \(x,y\) before comparison. In these boxes the physical native cofactors satisfy \(A\asymp N^{1-\alpha},C\asymp N^{1-\nu-\theta}\), exceeding \(U_x,U_r\) by fixed powers, so no cofactor \(>1\) gate moves upon opening.

Put
\[
 F=fF_0,\quad F_0=d e_1,\qquad H=m H_0,\quad H_0=h e e_2 .
\]
Retain \((FH,N)=1\) and \((F,H)=1\). In particular a nonunit comparison between a fixed factor of \(H_0\) and \(F\) produces no terms. Use the same unit expansion \(u\mid N\), truncating \(u\le\exp(L^{3/4})\) by the global physical Rankin and Cauchy bound; this step constrains both free integer variables in \(F a+H c=N\) to multiples of \(u\). The zero mode in the \(x\)-variable has density \(\varphi(N)/(N F H)\). At fixed physical \(x,m,f,h,e,e_1,e_2\), the original full \(d\)-sum is the \(z\)-rough harmonic \(\mu(d)/d\) up to \(U_x\) with \((d,NH)=1\), and cancels to arbitrary log accuracy. This uses the same standard masked rough Mertens harmonic as that comparison, irrespective of how the nonzero terms below are estimated. The positive reciprocal \(m\)-harmonic may use \(|Q_T(m)|\le\tau(m)\), also when \(m\) is polynomial. Every additional real interval in the theorem is independent of these \(d\)-labels.

For nonzero \(j\) write \(a_j=jN/u\). The exact reciprocal identity gives the Poisson term in the form
\[
 \frac{N}{uF H}\widehat\Psi\left(\frac{jN}{uF H}\right)
     e\left(\frac{a_j}{F H}\right)e_F(-a_j\overline H).              \tag{2}
\]
This uses \((F,H)=1\). On the fixed dyads let \(F_s,H_s\) denote the outer product scales and \(J_*=u F_s H_s/N\). The smooth factor before the last reciprocal phase in (2) has supremum plus total variation in the **free actual \(m\)** at most
\[
 W_j\ll L^{O(1)}J_*^{-1}(1+|j|/J_*)^{-2}.
\]
In fact differentiation of the extra \(e(a_j/(F H))\) in \(m\) costs at most \(O(|j|/(J_* m))\), absorbed by one additional decay in the smooth transform. The true \(m\)- and \(mh\)-intervals at fixed \(h\) are each interval restrictions; apply ordinary partial summation with this same variation bound. The summed \(W_j\) over \(j\ne0\) is \(O(L^{O(1)})\) uniformly, including \(J_*<1\). As before one may restrict \(|j|\le N^\varepsilon\max(1,J_*)\) with a power-small error by using sufficiently many fixed derivatives on the central cells. The untruncated count of individual outer choices is at most \(N^{O(1)}\), so these additional derivatives can be chosen to absorb it. By the first line in (1) and sufficiently small fixed \(\varepsilon>0\), every retained nonzero \(j\) has \(|j|<f\); indeed \(J_*/f\ll N^{\nu+\theta+\eta_x+\eta_r-1+o(1)}\). Since \(f\nmid N\), the modulus-large part \(f\) is coprime to \(a_j\). No restriction on \((j,F_0)\) is needed.

Now fix \(u,f,h,d,e,e_1,e_2,j\). Open the literal \(Q_T(m)\) into \(\mu(b)\) for \(b\mid m\), \(b<T\), writing \(m=b n\). Nonzero support requires \((b,NF)=1\) and true \((n,NF)=1\). Open the \(N\)-units of \(n\) with \(t\mid\operatorname{rad}(N)\), \(n=t v\) and coefficient \(\mu(t)\). Every \(t\) is a unit modulo \(F\), since \((N,F)=1\). Thus \(v\) lies in a real interval at scale \(O(N^\nu/(b t))\), with \((v,F)=1\), and the last phase of (2) becomes
\[
       e_F\big(-a_j\,\overline{b t H_0}\,\bar v\big).
\]
All factors in the first inverse are units modulo \(F\). The fixed datum \(b<T\asymp S\) has only subpower size and count; \(\tau(N)=N^{o(1)}\) handles the \(t\)-sum in this power-saving estimate.

Because \(\eta_x<\alpha\), one has \((F_0,f)=1\). In the complete-period sum the prime modulus \(f\) gives a unit Ramanujan sum of absolute value 1 and the \(F_0\)-factor is at most \(F_0\), even if the numerator shares its primes. Incomplete periods are bounded by Fourier completion and the prime Weil bound at \(f\), uniformly with all additive completion modes; their total is \(O(F_0 f^{1/2}N^{o(1)})\). In particular this treats gcd-bearing \(j\)'s without falsely requiring a unit at \(F_0\) or reducing away a period. After summing \(b,t\), the true \(m\)-sum with the smooth factor in (2) has absolute bound
\[
 W_j N^{o(1)}
  \left(\frac{N^\nu}{f}+F_0 f^{1/2}\right),                        \tag{3}
\]
since one complete period costs \(F_0\) and \(F=F_0 f\). It is essential that (3) sums the polynomial \(m\)-coordinate before taking absolute values outside it.

Finally sum the true \(f,h\) choices using the trivial cardinalities \(O(N^\alpha),O(N^\theta)\); the prime logs cost only fixed log powers. The polynomial short \(d,e\) choices cost \(N^{\eta_x+\eta_r}\), and \(F_0\le N^{\eta_x+o(1)}\). Using the uniform frequency bound after (2) and the subpower \(u,e_1,e_2\) choices, the two exponents from (3) are exactly
\(\nu+\theta+\eta_x+\eta_r\) and \(3\alpha/2+\theta+2\eta_x+\eta_r\), plus \(o(1)\). They are below one by (1). This makes the actual nonzero sum power-small. Together with the exact zero-mode and cutoff payments it proves the theorem, without any inference about prime pairs in the complementary chart.
