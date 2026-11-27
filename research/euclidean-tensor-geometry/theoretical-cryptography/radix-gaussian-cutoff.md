# A total-variation cutoff for geometric sums of discrete Gaussians

For a fixed integer radix \(b\ge3\), sum \(k+1\) independent integer discrete Gaussians with weights \(1,b,\ldots,b^k\). At what width is the output close in total variation to the single discrete Gaussian predicted by continuous covariance? The answer has a nontrivial curve, and the critical width is a factor \(1/\sqrt2\) below the width that makes every kernel fiber have nearly the same mass.

This is a mathematical comparison of two generated probability laws. It is not a preimage sampler, a decoding method, or a claim on a deployed or proposed scheme.

## 1. Statement

Write \(D_{\mathbb Z,t}(x)\propto e^{-\pi x^2/t^2}\), and put
\[
 S=\sum_{j=0}^{k}b^{2j},\quad
 P_{k,t}=\mathcal L\Big(\sum_{j=0}^k b^j X_j\Big),\quad
 Q_{k,t}=D_{\mathbb Z,t\sqrt S},\quad
 T=\frac{2\pi t^2}{b^2-1},\quad
 \tau_k=k e^{-T},
\]
where \(X_0,\ldots,X_k\) are independent \(D_{\mathbb Z,t}\). If \(\tau_k\to\tau\in(0,\infty)\), then
\[
 \boxed{\ \|P_{k,t}-Q_{k,t}\|_{\rm TV}
                \ \longrightarrow\ 2\Phi(\sqrt{\tau/2})-1\ } .          \tag{1}
\]
The same limiting distance is obtained using only the output residue modulo \(b^k\). If \(\tau_k\to0\), the distance tends to zero. If \(\tau_k\to\infty\) and \(t\) is bounded below by any fixed positive constant, the distance tends to one. The lower bound on \(t\) in the last assertion prevents a separate collapse of both distributions to zero at extremely small widths. No result is asserted for \(b=2\).

In contrast, the pointwise smoothing parameter of the kernel of the row \((1,b,\ldots,b^k)\) in \(\mathbb Z^{k+1}\), for fixed \(\epsilon>0\), satisfies
\[
 \frac{\pi\eta_\epsilon^2}{b^2-1}
                =\log\!\left(\frac{2k}{\log(1+\epsilon)}\right)+o(1).
                                                                    \tag{2}
\]
At the critical widths in (1), the likelihood ratio at the single output zero actually diverges. Thus (1) concerns the average under \(Q_{k,t}\), not the largest relative error.

[Genise–Micciancio–Peikert–Walter, Theorem 4.6](https://web.eecs.umich.edu/~cpeikert/pubs/gaussians.pdf) gives a general max-log sufficient condition for integer combinations of lattice Gaussians based on smoothing the kernel. [Aggarwal–Regev, Theorem 3.2](https://arxiv.org/abs/1308.2405) gives sufficient conditions for fixed linear combinations. We study the actual total-variation threshold for one growing weighted row, with the same reference covariance. The [companion equal-weight convolution note](discrete-gaussian-convolution-residues.md) treats a fixed number of equal weights followed by independent repetitions. Here there is one growing radix sum, no repeated outputs, and the output residue enters as dependent nested phases. The cluster step is related to the [bounded-anisotropy theta cutoff](anisotropic-dyadic-theta-cutoff.md); we prove the needed version including boundary diagonals and the radix-three pair gap.

## 2. Kernel, inverse Gram, and an exact likelihood

Let \(a=(1,b,\ldots,b^k)\), \(K=a^\perp\), \(\Lambda=K\cap\mathbb Z^{k+1}\). The vectors \(v_i=b e_{i-1}-e_i\), \(1\le i\le k\), are an integral basis of \(\Lambda\): eliminate the last coordinate by subtracting an integer multiple of \(v_k\), and repeat until the first coordinate alone must vanish. Let \(w_i\) be the dual basis in \(K\) and use \(w(z)=\sum_i z_i w_i\) for \(z\in\mathbb Z^k\). If \(H\) is the Gram matrix of \(v_i\), its diagonal is \(b^2+1\), its neighboring entries are \(-b\), and its other entries are zero. With \(l=(b^2-1)^{-1}\), define \(C=H^{-1}/l\); then
\[
 C_{ij}
   = b^{-|i-j|}
      \frac{(1-b^{-2\min(i,j)})(1-b^{-2(k+1-\max(i,j))})}
           {1-b^{-2(k+1)}} .                                    \tag{3}
\]
For example, the matrix in (3), as a function of \(i\) for fixed \(j\), obeys the homogeneous second-order recurrence of \(H\) on both sides of \(j\), vanishes at the extrapolated endpoints \(0,k+1\), and the jump at \(j\) is \(b^2-1\), which verifies \(HC=(b^2-1)I\). The spectral bounds for \(H\) between \((b-1)^2 I\) and \((b+1)^2 I\), by its quadratic form, give
\[
 \eta I\preceq C\preceq\eta^{-1}I,\qquad \eta=(b-1)/(b+1)\ge1/2 .
\]
The symbol \(\eta\) in this bound is just a scalar eigenvalue bound, not the smoothing parameter in (2). Also
\[
 (w_i)_0=b^{-i}\left(1-\frac{\sum_{j=0}^{i-1}b^{2j}}{S}\right).
                                                                    \tag{4}
\]
Indeed \(b(w_i)_{j-1}-(w_i)_j=\mathbf 1_{j=i}\), so
\((w_i)_j=b^j(w_i)_0-\mathbf 1_{j\ge i}b^{j-i}\); orthogonality to \(a\) gives (4).

An integer preimage of output \(y\) is \(y e_0\). Its real projection to \(K^\perp\) has squared norm \(y^2/S\). Splitting the fiber orthogonally and applying Poisson summation on \(\Lambda\) shows
\[
 \frac{dP}{dQ}(y)=\frac{F(y)}{\mathbb E_Q F},
 \qquad F(y)=\sum_{w\in\Lambda^*} A_w e^{2\pi i y w_0},
 \qquad A_w=e^{-\pi t^2\|w\|^2}.                                \tag{5}
\]
Let \(g(w)=\mathbb E_Q e^{2\pi i y w_0}\). One-dimensional Poisson gives the nonnegative expression
\[
 g(w)=\frac{\sum_{h\in\mathbb Z}e^{-\pi t^2 S(h-w_0)^2}}
              {\sum_{h\in\mathbb Z}e^{-\pi t^2 S h^2}} .          \tag{6}
\]
There is a bijection
\[
 (w,h)\in\Lambda^*\times\mathbb Z
       \longmapsto x=w+(h-w_0)a\in\mathbb Z^{k+1}.
\]
For any integer \(x\), \(w=\operatorname{proj}_K(x)\in\Lambda^*\) since it pairs integrally with each \(v_i\), and \(h=x_0\). Conversely, for \(w\in\Lambda^*\), the relation \(b w_{j-1}-w_j\in\mathbb Z\) makes \(w_j-b^j w_0\) integral for every \(j\), verifying the reverse map. The squared norm is \(\|w\|^2+S(h-w_0)^2\). For a real lattice \(L\), write \(\Theta_L(u)=\sum_{x\in L}e^{-\pi u\|x\|^2}\). The bijection yields
\[
 \mathbb E_Q F=\frac{\Theta_{\mathbb Z^{k+1}}(t^2)}
                      {\sum_{h\in\mathbb Z}e^{-\pi t^2 S h^2}},
 \qquad
 \sum_{w\ne0} e^{-\pi c t^2\|w\|^2}g(w)
       \le \Theta_{\mathbb Z^{k+1}}(c t^2)-1
              \quad (0<c\le1).                                 \tag{7}
\]
For the inequality compare the exponent of the complementary component in (6) at \(c t^2\), drop the denominator, and use the same bijection. At critical widths, \(\pi t^2=(b^2-1)(\log k+O(1))/2\), so \(\mathbb E_Q F=1+o(1)\). More generally \(\Theta_{\mathbb Z^{k+1}}(c t^2)-1=o(1)\) for every fixed \(c\) with \(c(b^2-1)/2>1\), by the elementary one-dimensional estimate \(1+O(e^{-\pi c t^2})\).

## 3. The doubled-temperature theta approximation

It is enough here that \(T=\log k+O(1)\). Fix \(M=\lceil 10\log k\rceil\) and call positions \(M\le i\le k+1-M\) interior. We claim
\[
 \sum_{z\in\mathbb Z^k}
 \left|e^{-T z^{\mathsf T}Cz}
       -e^{-T\|z\|^2}\mathbf1_{\{z_i\in\{-1,0,1\},\ z_i=0
                                      \text{ off the interior}\}}\right|
                          =o(1).                               \tag{8}
\]
The proof also applies with any temperature \(\log k+O(1)\) in place of \(T\).

Order the support of \(z\) and split it into clusters whose successive gaps are at most \(M\), with different clusters separated by larger gaps. From (3), deleting the cross-cluster entries changes the quadratic form by at most \(\delta_k\|z\|^2\), where \(\delta_k=O(b^{-M})\): sum the absolute off-diagonal entries at gaps larger than \(M\) in each row and use \(2|z_i z_j|\le z_i^2+z_j^2\). At a singleton \(i\) use the energy lower bound \((C_{ii}-\delta_k) z_i^2\). For any two-site cluster use a uniform lower bound \(\mu_2 \sum_{i\text{ in cluster}}z_i^2\) with a constant \(\mu_2>1/2\) for all large \(k\). In fact for \(k\ge2\), (3) gives \(C_{ii}\ge (1-b^{-2})(1-b^{-4})\ge640/729\) and \(|C_{ij}|\le b^{-1}/(1-b^{-6})\le243/728\) for \(i\ne j\), whose difference exceeds \(1/2\) by a fixed margin. For cluster size at least three use \((1/2-\delta_k)\sum z_i^2\). The two-site estimate is useful even at \(b=3\), where the global spectral bound alone is just \(1/2\).

Put \(h(x)=2\sum_{j\ge1}e^{-xj^2}\le C_0 e^{-x}\) for \(x\ge1\). The total singleton weight using the energy lower bounds remains \(O(1)\): interior diagonals equal \(1+O(b^{-2M})\), and the \(O(M)\) boundary locations have diagonal bounded below by a fixed \(c_0>1/2\). Boundary singleton weight is \(o(1)\); the total weight of singletons with \(|z_i|\ge2\) is also \(o(1)\) using \(k\,O(e^{-4c_0 T})\), with \(c_0\) reduced slightly for \(\delta_k\). There are at most \(k M^{s-1}\) connected supports of cluster size \(s\), by recording the first position and the successive gaps. The total weight of size two clusters is \(O(k M e^{-2\mu_2 T})=o(1)\). With \(h((1/2-\delta_k)T)=O(k^{-1/2})\), the sum of weights for sizes \(s\ge3\) is \(O(k M^2 k^{-3/2})=o(1)\), by a geometric series.

If we ignore compatibility between clusters, the sum over cluster selections is bounded by the product of \(1+\) their weights, hence by the exponential of the sum of all weights. A union bound over a marked bad cluster multiplies this bound by the sum of its bad weights. Thus vectors with a boundary location, a charge of magnitude at least two, or a nonsingleton cluster have total Gaussian weight \(o(1)\). The same conclusion for the diagonal reference in (8) follows by the identical estimate with diagonals one and zero off-diagonals (or the pair union bound). On the remaining supports the form differs from \(\|z\|^2\) by at most \(O(\delta_k)\|z\|^2\). The total difference of the weights there is at most a constant times
\(T\delta_k\sum_z|\operatorname{supp}z| e^{-T(1-O(\delta_k))|\operatorname{supp}z|}\),
over all sites with charges \(0,\pm1\), and the latter sum is \(O(1)\), by the binomial formula and \(k e^{-T}=O(1)\). This proves (8).

As a consequence,
\(\Theta_{\Lambda^*}(2t^2)= (1+2 e^{-T})^{k-O(M)}+o(1)\to e^{2\tau}\).
Applying the same result at temperature \(\pi t^2/(b^2-1)\) and using strict monotonicity of the dual theta as a function of \(t\) proves (2), by bracketing its asserted temperature with any fixed additive slack.

## 4. From coefficient mass to an actual \(L^2(Q)\) approximation

Set \(\varepsilon=e^{-T/2}\) and put
\[
 B_{w(z)}=\varepsilon^{\|z\|^2}\mathbf1_{\{z_i\in\{-1,0,1\},\
                                          z_i=0\text{ off the interior}\}},
 \qquad F_B(y)=\sum_w B_w e^{2\pi i y w_0}.
\]
The inequality \((\sqrt{u}-\sqrt{v})^2\le |u-v|\) and (8) give
\(\sum_w |A_w-B_w|^2=o(1)\). This is not yet \(L^2(Q)\): the phases are not orthogonal under \(Q\). For each pair the inner product is \(g(w-w')\) from (6). The diagonal was just bounded; we bound the off-diagonal terms using \(|A_w-B_w|\le A_w+B_w\).

*Two \(A\)'s.* For a displacement \(p=w-w'\ne0\), complete the square:
\[
       \sum_w A_w A_{w-p}
          \le e^{-\pi t^2\|p\|^2/2}\Theta_{\Lambda^*}(2t^2).
\]
Here a Gaussian sum over a shifted lattice is at most the sum centered at the lattice, by Poisson and the triangle inequality. The theta factor is \(O(1)\) by (8). Multiplying by \(g(p)\) and summing uses (7) with \(c=1/2\), which is \(o(1)\) since \(b\ge3\).

*Mixed terms.* In integer coordinates replace the \(B\)-coefficients by the full Gaussian with energy \(l\|z\|^2\). Write \(p=w(v)\). The two energies as a function of real \(z\) are \(l z^{\mathsf T} C z+l\|z-v\|^2\). On diagonalizing \(C\), their sum's minimum is \(l v^{\mathsf T} C(I+C)^{-1}v\ge [\eta/(1+\eta)]\|p\|^2\). The centered Gaussian sum of the residual quadratic form \(l(C+I)\) is at most the geometric mean of the sums of the two doubled forms, by Cauchy–Schwarz, so is \(O(1)\) by (8) and the scalar product bound. Poisson again allows the shift from completing the square. Thus (7) with \(c=\eta/(1+\eta)=(b-1)/(2b)\) bounds the mixed off-diagonal sum by \(o(1)\), since \(c(b^2-1)/2\ge4/3\) for \(b\ge3\).

*Two \(B\)'s.* Only differences \(p=w(v)\) with interior coefficients \(|v_i|\le2\) occur. If \(v\ne0\), the rational sum \(\sum_i v_i b^{-i}\) is nonzero: the first nonzero digit dominates the absolute sum of the later digits, as \(2\le b-1\) and there are only finitely many terms. Its magnitude is at least \(b^{-k-1+M}\), its smallest possible denominator scale; its magnitude is also \(O(b^{-M})\). By (4) the error between that sum and \(p_0\) is \(O(b^{-k-1-M})\). Therefore \(\|p_0\|_{\mathbb T}\ge \tfrac12 b^{-k-1+M}\) for large \(k\). Equations (6) and \(S\ge b^{2k}\) give \(g(p)\le C_1\exp(-c_1 t^2 b^{2M})\): on a one-dimensional translate, the nearest term controls the sum up to a universal bounded factor at parameter \(t^2 S\ge1\). Multiplying by \((\sum_w B_w)^2\le (1+2\varepsilon)^{2k}=e^{O(\sqrt k)}\) still gives \(o(1)\).

Absolute convergence follows from the Gaussian coefficients, so the diagonal/off-diagonal splitting is justified. Thus \(\mathbb E_Q |F-F_B|^2=o(1)\). In particular both have bounded second moments, by the same \(A\)-bound and its diagonal estimate. This step uses the ambient integer lattice only to bound the nonorthogonality of the phases; it does not suppose that \(Q\) is close to uniform on the entire discriminant group.

## 5. A low-digit martingale

The polynomial in the phases factors:
\[
              F_B(y)=\prod_{i\ {\rm interior}}
                           \big(1+2\varepsilon\cos(2\pi y (w_i)_0)\big).
\]
Replace \((w_i)_0\) by \(b^{-i}\) and call the resulting product \(F_{\rm dig}(y)\). For large \(k\) all factors are positive. By (4), the absolute difference of their logarithms, summed over \(i\), is at most \(C_2\varepsilon |y| b^{-k-M}\). Under \(Q\), \(\mathbb E |y|\le C_3 t\sqrt S\), by an elementary scalar Gaussian sum bound; so this logarithm difference tends to zero in probability. The residue \(y\bmod b^k\) under \(Q\) is within a \(1+o(1)\) relative pointwise factor of uniform. To see this, use one-dimensional Poisson on each coset \(b^k\mathbb Z+a\) and the full ring normalizer; its effective width is \(t\sqrt S/b^k\ge t\to\infty\).

Under uniform residue let \(C_i=\cos(2\pi y/b^i)\), and expose the base-\(b\) digits from low to high. A new digit is uniform independent of earlier ones. As \(b\ge3\), its first and second nontrivial complex characters average to zero, so
\[
             \mathbb E[C_i\mid\text{previous digits}]=0,\qquad
             \mathbb E[C_i^2\mid\text{previous digits}]=1/2 .
\]
Consequently the second moment of \(F_{\rm dig}\) under uniform residue is
\((1+2\varepsilon^2)^{k-O(M)}=O(1)\), by iterated conditioning, and the same bound holds under \(Q\). The products \(F_B,F_{\rm dig}\) differ by \(o_{\mathbb P}(1)\) (their logarithms differ by \(o_{\mathbb P}(1)\) and the products are tight) and then by \(o(1)\) in \(L^1(Q)\) by the bounded second moments.

Taylor expansion gives, with an \(o(1)\) remainder since \(k\varepsilon^3=o(1)\),
\[
  \log F_{\rm dig}
       =2\varepsilon\sum_{i\ {\rm interior}} C_i
           -2\varepsilon^2\sum_{i\ {\rm interior}} C_i^2+o(1).
\]
The second term tends to \(-\tau\) in probability because the centered squares are bounded martingale differences. The first tends to \(N(0,2\tau)\): for each fixed real \(s\), the conditional characteristic factor of \(2s\varepsilon C_i\) is
\(1-s^2\varepsilon^2+O_s(\varepsilon^3)\) uniformly in the previous digits. Iterate this bound, with total error \(O_s(k\varepsilon^3)\), to get characteristic limit \(e^{-s^2\tau}\). The same conclusions hold under \(Q\) by its asymptotically uniform residue law.

Equations (5), (7) and the two approximations show that the true likelihood is within \(o(1)\) in \(L^1(Q)\) of \(F_{\rm dig}\). Evaluating the bounded continuous function \(x\mapsto(1-x)_+\) gives the limiting TV as \(\mathbb E(1-e^Z)_+\) for \(Z\sim N(-\tau,2\tau)\). A Gaussian exponential tilt evaluates this to \(2\Phi(\sqrt{\tau/2})-1\). Moreover \(F_{\rm dig}\) depends only on \(y\bmod b^k\). The likelihood for the residue is the conditional expectation of the full likelihood. Conditional expectation contracts \(L^1\), so the residue gives the same limiting distance. Finally \(F(0)\ge1+2\sum_{i\ {\rm interior}} A_{w_i}\), and (3) gives \(A_{w_i}=(1+o(1))\varepsilon\) uniformly there. At critical widths \(k\varepsilon\to\infty\), proving the pointwise divergence claimed after (2). In fact at any fixed fraction \(a\in(1/2,1)\) of the **squared** pointwise scale, \(\pi t^2/(b^2-1)=a\log k\), the same lower bound has order \(k^{1-a}\) and the normalizer still tends to one. The broad-side conclusion below gives vanishing TV in that whole range.

## 6. Outside the critical window

**Broad side \(\tau_k\to0\).** From (5) it suffices to show \(\mathbb E_Q|F-1|^2=o(1)\). Use its positive double sum over \(w,w'\ne0\), with \(g(w-w')\) given by (6). Dropping the denominator in (6) makes each term nonincreasing in \(t\). For any fixed \(c_2>0\), compare to the width with \(T=\log k+c_2\), which is eventually smaller. At that comparison width the diagonal sum tends to \(e^{2e^{-c_2}}-1\) by (8), and the off-diagonal \(A\)-bound in §4 gives \(o(1)\). The dropped denominator is \(1+o(1)\) there. Sending \(c_2\to\infty\) gives the result.

**Narrow side \(\tau_k\to\infty\) along \(t\to\infty\).** Fix any \(\tau>0\) and choose \(k'=\lfloor \tau e^T\rfloor\), so \(k'\to\infty\), \(k'/k\to0\), and the shorter row is at its critical width with \(\tau_{k'}\to\tau\). Upon reducing output modulo \(b^{k'}\), its source law is exactly that for the shorter row (all inputs at powers \(b^{k'}\) and higher disappear). Both reference distributions on the residue are \(o(1)\)-close to uniform by Poisson, since their effective widths are at least \(t\). The critical result together with the sufficiency of the residue gives a lower bound \(2\Phi(\sqrt{\tau/2})-1\) on the limiting distance for the original row. Let \(\tau\to\infty\).

**Narrow side with \(t\) bounded and bounded away from zero.** Observe the average of \(\cos(2\pi y/b^i)\) for \(1\le i\le\lfloor k/2\rfloor\). Under \(Q\) the relevant residue is asymptotically uniform because \(t\sqrt S/b^{\lfloor k/2\rfloor}\to\infty\); the average then tends to zero in probability by the martingale-difference property. Under \(P\), for each \(i\) the mean of this cosine is
\(\prod_{j=1}^i\phi_t(b^{-j})\) with \(\phi_t\) the one-dimensional characteristic function. This product is uniformly bounded below by a positive constant for \(t\) in a fixed compact positive interval. Every factor is strictly positive by Poisson, continuous in the parameters, and \(1-\phi_t(b^{-j})=O(b^{-2j})\) with a common constant by the bounded scalar second moments. If \(i<i'\), the unwrapped lower prefix divided by \(b^{i'}\) has expected magnitude \(O(b^{-(i'-i)})\). Deleting just this prefix from the \(i'\)-th cosine changes it by that amount in mean, and leaves a function independent of the \(i\)-th cosine. Hence the covariance is \(O(b^{-(i'-i)})\), so the average concentrates at its positive mean. This separates the distributions with probability tending to one. Together with the previous argument (or by passing to subsequences) this covers \(t\) bounded below and \(\tau_k\to\infty\).

## Reproduction

Run `python3 verify-radix-gaussian-cutoff.py` with Python 3 and NumPy. It verifies exact dual Gram and integer orthogonal decomposition identities and tests finite probability-law identities and the limiting digit statistic on generated examples. These tests do not prove the asymptotic statement.
