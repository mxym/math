# The actual signed .09 notch is Type I after splitting the carrier suffix

The original signed \(\mu(d)\log p\) sum on the whole fixed exponent box (66) for the **marked carrier** \(C_\sharp\) is unconditionally \(O_{s,B}(x(\log x)^{-B})\) for every \(B\), uniformly at each even target. This estimates the pre-Cauchy signed sum and its matched reference, not the Cauchy-enlarged covariance in which the carrier was dropped. It uses a grouping of the *actual* independent suffix factors to extend the carrier's broad modulus level across a gap. It neither proves Goldbach nor estimates the remaining Type II terms outside this box.

## 1. Actual factors and new exponent windows

Use [MixedCarrierTypeISeparation.md](MixedCarrierTypeISeparation.md) and [MacroShiftBurgessMajorArcs.md](MacroShiftBurgessMajorArcs.md). Let \(x=N/2\), \(I=(x/2,x]\), \(J=\{m:N-m\in I\}\), and distinguish the two macro primes \(A_M,B_M\) from the suffix marker \(A_0\). Their exponents lie within \(10^{-8}\) of .24 and .25 respectively. The nine actual prime labels \(q_i\) have exponents within \(10^{-9}\) of \(.054+(i-5)10^{-7}\). For \(C(n)\) the full suffix \(v\) has \(|\log_x v-.024|\le10^{-6}\), and is \(y\)-rough with \(y=x^\varepsilon\), at fixed sufficiently large sieve \(s\) so that \(\varepsilon<.0088\).

For \(C_\sharp(n)\),
\[
       n=A_M B_M q_1\cdots q_9\,A_0 w\in I,
\]
where \(A_0\) is an actual prime in \([x^{.0149},x^{.0151}]\), and \(w\) is independently \(y\)-rough in \([x^{.0088},x^{.0092}]\). The product condition in \(I\) already implies \(|\log_x(A_0w)-.024|\le 10^{-6}\) for large \(x\), by the eleven other exponent restrictions; the indicated interval on \(w\) likewise follows from the \(I\)-condition and the \(A_0\) band. Thus the split variables can be put in **different independent convolution slots**, or grouped as the exact single suffix \(v=A_0w\) when it is useful to have its much narrower total exponent window. In the grouped case the coefficient of \(v\) tests this factorization independently of the other groups. It is \(0,1\): \(w<A_0\), so \(A_0\) is unique. All label bands are disjoint, and no \(w\)-factor can meet one. Hence every group coefficient in either implementation is \(0,1\) by unique factorization. In particular the allocation of \(q_i\)'s to the factor groups below uses disjoint actual labels even though their limiting central exponents are all .054.

We apply [Jain, *Sums of Integers with Small Prime Factors*, arXiv:2611.21136v1, Proposition 3, equation (3.1)](https://arxiv.org/html/2611.21136v1#S3.SS1), **not** its result for all smooth numbers. Write \((m,u,v')\) for the exponents of its lengths \((M,N,L)\), \(R\) is one modulus dyad, \(r_*=\log_x R\), and let \(Q_i\) denote the product of any of three disjoint groups of three of the \(q_j\)'s. Take its residue \(a_1=N,a_2=1\), in this paragraph \(N\) meaning the fixed even target as usual outside its factor-length notation. The scale \(X'=MNL\asymp x\) on each contributing box implies \(|a_1|\le (X')^{1+\delta}\) for any fixed allowed \(\delta>0\) eventually, and the other residue assumptions hold. For \(\theta=7/32\), the limiting length inequalities with strictly positive slack are
\[
\begin{gathered}
 u>0,\quad u+v'<2/3,\quad v'<m,\quad m<r_*<u+v',\\
 r_*>2u+3v'-1,\qquad
 r_*>\frac{(7-4\theta)u+(4-\theta)v'-2+2\theta}{2+\theta},
 \qquad r_*>\frac{7u+4v'+\theta-2}{2}.
\end{gathered}
\tag{1}
\]
These inequalities use \(\log_x |a_1|=1+O(1/\log x)\); fixed margins below absorb all \(O(1/\log x)\) length-normalization effects and \(X'\)-powers, as well as dyadic endpoint crossing.

The missed seam is filled by two more exact assignments:
\[
\begin{array}{c|c|c|c|c}
 M\text{-group}&N\text{-group}&L\text{-group}&
 (m,u,v')\ \text{central}&\text{modulus window proposed}\\ \hline
 B_M Q_1 w&Q_2 A_0&A_M Q_3&(.421,.177,.402)&[.5725,.5785]\\
 B_M Q_1 & Q_2 v & A_M Q_3&(.412,.186,.402)&[.5783,.586]
\end{array}
\tag{2}
\]
Here in the last row \(v\) is the whole suffix (either original rough or marked, depending on the carrier). In the split row take errors \(<.000205,.000105,.000005\) respectively in its three exponent coordinates, generously covering the suffix widths, prime widths, and dyadic/scale errors for all sufficiently large \(x\). In the whole row take each error \(<.000005\).

For the split row, the central lower thresholds in (1), including \(m\), are respectively \(.421,.560,.4694929\ldots,.532875\), and the upper threshold is .579. Conservative lower bounds on actual margins at the endpoints of its modulus range are respectively \(.1512,.0122,.1026,.0392\) and \(.00039\) for the upper inequality. Indeed its \(2u+3v'-1\) grows by at most .000225, the next lower threshold grows by \(<.00031\), and the last by \(<.00038\); \(u+v'\) drops by at most .000110. The remaining \(m-v'\) margin exceeds .0187, \(u\) exceeds .1768, and \(2/3-u-v'>.0875\).

For the whole row the central lower thresholds are \(.412,.578,.4943380\ldots,.564375\), and the upper is .588. The smallest lower margin is at \(r_*=.5783\) against \(.578+5(.000005)=.578025\), giving \(>.00027\). The upper margin at .586 is \(\ge .00199\). The other lower conditions each have margin \(>.0138\), and \(m-v'>.00998\), \(u>.1859\), \(2/3-u-v'>.0786\). Thus the actual (3.1) with its \(\varepsilon_{\rm Jain}\)-losses holds, for example for \(\varepsilon_{\rm Jain}=10^{-5}\) in these two new windows. The old estimate through .573 overlaps the first window, and the two new windows overlap by .0002. Assign seam-crossing dyads inside an overlap, for which \(\log_x2=o(1)\) is harmless.

## 2. Unweighted maximal distribution and reference

For all fixed \(s,B>0\) as above, the conclusion on \(C_\sharp\) is
\[
 \sum_{r\le x^{.586}}\sup_t
 \left|\sum_{\substack{m\in J\\m\le t,\,r\mid m}}C_\sharp(N-m)-
 \frac{1_{(r,N)=1}}{\varphi(r)}
       \sum_{\substack{m\in J\\m\le t}}C_\sharp(N-m)\right|
                 \ll_{s,B} x(\log x)^{-B}.
 \tag{3}
\]
Here the positive outer modulus summation does not assume any factorability of its weights. The low-conductor, product, and endpoint steps are as in the proof of (58) in the mixed-carrier note. To check their scope in the two new windows:

* For dyadic factor groups, the theorem removes conductors up to \(D_0=x^\eta\), for a positive fixed \(\eta<\min(\delta,\varepsilon_{\rm Jain},\varepsilon/10)\), reduced residues \(a_1=N,a_2=1\), for a power saving (shrink \(\eta\) as needed). The choice of independent grouping does not affect the low-conductor removal. A primitive \(\chi\) of nonprincipal conductor \(\le D_0\) is tested by fixing every factor but one actual \(q_i\) of exponent \(.054+O(10^{-6})\). The fixed product includes the grouped or separately labelled suffix and no dependence on the last prime. Apply standard maximal primitive prime-character mean bounds via Vaughan/Bombieri–Vinogradov at its actual scale and sum the reciprocal weights of the fixed factors, exactly as for (58); \(D_0\) is a small fixed power of that prime length. The sum of progression weights for induced characters is \(O((\log x)/\varphi(\operatorname{cond}\chi))\).
* The possible imprimitive and missing-unit masses are \(O(xD_0^2(\log x)^C/y)\) and \(O(x(\log x)^C/y)\), respectively, by the same divisor/harmonic argument; every carrier factor has all prime divisors at least \(y\). For nonreduced target classes, a common prime \(< y\) gives literal zero; a common \(p\mid N\) with \(p\ge y\) costs at most \(O(x(\log x)^C/y+x^{.586}(\log x)^C/y)\) by summing \(x/r+1\) over its moduli. This handles the full ordinary \(\varphi(r)\)-normalization separately from the reduced high-conductor theorem.
* The arbitrary product prefix constraint is introduced by the earlier smooth logarithmic/Mellin endpoint cutoff and logarithmic prefix mesh. Since \(C_\sharp\le1\), the raw transition discrepancy costs \(O(x(\log x)^{-A}/r+1)\) on each actual class and \(O((x(\log x)^{-A}+1)/\varphi(r))\) in the main model. Summing through .586 still leaves ample power room for constants and arbitrary log reserves. Use a mesh of a fixed power of the log, increasing the error exponent before summing. No short-interval prime asymptotic is assumed.
* In the old windows the marked suffix is merely an extra independent \(0,1\) suffix condition in its original slot. For the initial classical BV range, one treats \(A_0\) as one additional distinct labelled interval prime and \(w\) by its bounded rank, or uses the unchanged convolution BV argument with an independent prime slot \(q_i\). Thus the earlier old-window margin is not silently changed by the split.

For the unmarked \(C\), the whole-suffix last row alone also proves the modulus estimate (3) restricted to \([x^{.5781},x^{.586}]\). Indeed even the smaller bottom margin .000075 against \(2u+3v'-1\) suffices for \(\varepsilon_{\rm Jain}=10^{-5}\). The split row is not an identity for the whole \(C\) (for example \(v\) can itself be prime), so this argument does not give continuous distribution through the former gap on unmarked \(C\).

Let \(c_N(m)\) be the original signed sequence on \(J\) for \(C_\sharp(N-m)\) minus its [mesh-matched reference](MixedCarrierTypeISeparation.md#2-what-58-removes-in-actual-prime-detection). The reference CRT/fundamental-lemma calculation and unconditional prefix balancing are unchanged: exponent .586 is below 1, and all Bonferroni modulus-product floor costs are \(x^{.586+o(1)}\) before summing fixed log-power meshes. For reduced moduli its literal rough density is \(r^{-1}\prod_{p\mid r,\ p<Z}(1-1/p)^{-1}\); replacing it by \(1/\varphi(r)\) costs a relative \(O((\log x)/Z)\). Nonreduced moduli with a common prime below \(Z\) contribute zero, and those with a larger common prime are disposed of by the same harmonic bound with \(Z\) in place of \(y\), allowing the log-power rough weight. Equivalently (3) proves (59) with .586 replacing .573. The same restricted upgrade works on the specified high modulus interval for the unmarked carrier using its own matched reference. For any previously chosen bounded step multiplier where the direct rough-reference cancellation of (66) was proved, the true \(C_\sharp\) sum below also cancels: use the newly matched reference for it, then the established cancellation for either reference.

## 3. Signed Vaughan consequence and residual

On the original actual box (66), with both \(d,p\) in the stated dyadic or exponent intervals and \(h\) in any specified interval of its dyad, throughout
\[
              x^{.578}\le dp\le x^{.582}.
\]
For each modulus \(r=dp\), absorb the \(h\)-window as a difference of two prefixes in \(m=rh\), then use partial summation for smooth bounded-variation product or free-coordinate cutoffs (log-power derivative bounds suffice). Sticking to the genuine prime variable, the sum of the absolute \(\log p\) coefficient bounds for each \(r\) is at most
\(\sum_{p\mid r}\log p\le\log r\); this remains true if the \(h\)-window varies with \(d,p\), taking the maximum prefix for every term. Hence (59) at .586 gives
\[
   \sum_{\substack{(d,p,h)\text{ in }(66)\\p\ {\rm prime}}}
       \mu(d)\log p\, c_N(dph)
            \ll_{s,B}x(\log x)^{-B},
 \tag{4}
\]
with its original moving endpoints and arbitrary fixed log-power reserves. This is \(o_s(M_N)\). The separate reference bound in the original notch proof implies the analogous true-carrier sum with \(C_\sharp(N-dph)\) alone is also log-power small. Bound (4) keeps the shift \(N\) and primes fixed as actual arithmetic objects; it does not average targets or replace a prime weight in the decomposition by an ordinary integer weight.

More generally the same Type I regrouping removes any terms of (61) with \(dp\le x^{.586}\) on \(C_\sharp\), using the collected prime-log coefficient bound. Equivalently the extraction step may use \(Q=x^{.586}\) in place of .573, leaving \(dp>x^{.586}\) for \(d\le D_1=x^{.560}\), and retaining the former upper-\(d\) quotient-weighted block. For the unmarked \(C\), the isolated high-window result removes the part of (66) with \(dp\ge x^{.5781}\), but this note does not assert its total cancellation at the bottom edge. Neither conclusion applies as written to the entire polynomial-marker-weighted low remainder, or to the Cauchy-enlarged covariance with the \(F\)-constraint dropped. No strong Goldbach positivity is claimed.

### Related parallel work

[Jain, *Smooth Numbers in Arithmetic Progressions with Uniformity in the Residue Class*, Hexagon 2611.00530v1](https://hexagonmath.org/pdf/2611.00530v1), states a broader 5/8 level for smooth numbers and a separate coefficient-uniform triple-convolution Proposition 2, using a complementary-divisor loss. Neither the all-smooth conclusion nor the flexible regrouping used for that conclusion is applied to the marked support here. The calculation above uses arXiv 2611.21136v1 Proposition 3 with the two explicit assignments in (2).
