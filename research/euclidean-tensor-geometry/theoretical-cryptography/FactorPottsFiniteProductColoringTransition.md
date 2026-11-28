# Exact finite product allocation near the coloring-channel endpoint

Research note, 28 November 2026. Consider \(n\) uses of the same \(q\)-ary symmetric channel, \(q\ge3\):
\[
 T_\lambda p=\lambda p+(1-\lambda)u,\quad
 -1/(q-1)\le\lambda\le1,\quad u=(1/q,\ldots,1/q).
\]
We restrict the input to a product of independent laws; the coordinate laws need not be identical. The total entropy deficit is \(B=n\log q-H(X^n)\). We determine the exact finite-dimensional structure of the largest output deficit among such inputs for every \(B\) and solve the optimizer, to leading order with its constant, as the noise approaches the zero-diagonal coloring endpoint. This does not identify the optimizer over arbitrary correlated inputs.

Write \(k=q-1\), \(L=\log q\), let \(P_t=((1+kt)/q,(1-t)/q,\ldots,(1-t)/q)\), and set \(D(t)=D(P_t\Vert u)\). The input parameter \(t\in[0,1]\) covers \(D(t)\in[0,L]\). Set
\[
 s_\lambda(D(t))=D(\lambda t).
\]
[Gu–Polyanskiy, Proposition 18](https://people.lids.mit.edu/yp/homepage/data/nlsi_potts.pdf) proves the one-letter extremal property: at an input deficit \(d\), \(s_\lambda(d)\) is the largest output deficit and, for \(\lambda\ne0,1\), the unique extremizers up to alphabet permutation are \(P_{D^{-1}(d)}\). Our [envelope note](FactorPottsEntropyEnvelopes.md) established that \(s_\lambda\) has exactly one inflection, strictly convex before it and strictly concave after it, for \(-1/k<\lambda<1,\ \lambda\ne0\), and is strictly convex at the coloring endpoint \(\lambda_0=-1/k\). The [finite-block note](FactorPottsEnvelopeSaturationAndFiniteBlocks.md) gave equality in the tensorized bound, large-\(n\) off-grid asymptotics for products away from endpoint noise, and exact product optimization at \(\lambda_0\). None of those results is claimed again as new.

## 1. An exact finite formula

For interior nonzero \(\lambda\), let \(z_\lambda\in(0,L)\) be the single inflection. Write \(s=s_\lambda\) for this section. For \(0\le B\le nL\), the largest output deficit over product inputs is
\[
\begin{split}
 M_n(B)=\max\Big\{&
     s(B)\quad(0\le B\le z_\lambda),\\
 & j\,s\big((B-y)/j\big)+s(y):
    \ 1\le j\le n,\quad 0\le y\le z_\lambda,\quad
    jz_\lambda\le B-y\le jL,\quad
    y=0\ \text{if }j=n\Big\}.
\end{split}                                                   \tag{1}
\]
Only include the first candidate when its displayed constraint holds. There are at most \(n\) scalar compact-interval optimizations. Every maximal product input, up to permuting coordinates and symbols, has \(j\) equal deficits in \([z_\lambda,L]\), at most one positive deficit in \((0,z_\lambda)\), and the rest zero. The special case without any large coordinate is the first candidate in (1). If \(B<nL\), a maximizing allocation has no deficit equal to \(L\).

Indeed the one-letter theorem and additivity reduce optimization to maximizing \(\sum_i s(d_i)\) on \(0\le d_i\le L,\ \sum_i d_i=B\). A maximum exists by compactness. Two coordinates strictly between zero and \(z_\lambda\) can be varied a small equal amount in opposite directions; strict convexity makes their contribution on the resulting segment strictly convex, so its interior cannot be a maximum. All coordinates in \([z_\lambda,L]\) must be equal, since otherwise replacing them by their common mean strictly increases the sum by strict concavity. This proves that every optimizer has the stated shape. Conversely every candidate in (1) is a feasible allocation, including when \(y\) equals an endpoint. Finally, \(s'(L^-)=0\) in the interior noise regime, whereas \(s'(d)>0\) for \(0<d<L\) and \(s'(0^+)=\lambda^2>0\). If one coordinate equals \(L\) and another is less than \(L\), transferring a small deficit to the latter increases the objective. For completeness, the value at the coloring endpoint is \(m s_{\lambda_0}(L)+s_{\lambda_0}(R)\) when \(B=mL+R,\ 0\le R<L\); strict convexity makes every maximizer use \(m\) full coordinates, with one remainder if \(R>0\). The completely random and identity channels have values respectively \(0\) and \(B\).

## 2. A unique asymmetric product allocation near the coloring endpoint

Fix \(n\ge2\) and \(B=mL+R\) with \(1\le m<n\), \(0\le R<L\). As \(\lambda=(\tau-1)/k\) approaches \(\lambda_0\) through \(\tau\downarrow0\), the following hold for all sufficiently small positive \(\tau\).

* The maximizing allocation is unique up to permutation. It has \(m\) equal deficits \(x_\tau\) just below \(L\), one positive deficit \(y_\tau=R+m(L-x_\tau)\) just above \(R\), and the remaining deficits zero. Both \(x_\tau\) and \(y_\tau\) are interior. In particular, using one common positive deficit strength does not suffice, even for \(n=2\).
* Define \(r_R=s_{\lambda_0}'(R)\), taking the right derivative at \(R=0\), and put
\[
 \alpha=\frac1{k r_R}>1,\qquad C=q(k/q)^\alpha.
\]
With \(D(1-\epsilon_\tau)=x_\tau\),
\[
 \epsilon_\tau\sim C\tau^\alpha,\qquad
 L-x_\tau\sim \frac{k}{q}\epsilon_\tau\log(1/\epsilon_\tau).
 \tag{2}
\]
For a grid budget \(R=0\) this describes a new positive remainder with exponent \(\alpha=k\).
* The improvement over the feasible endpoint-shaped allocation at this same interior \(\lambda\) is
\[
 M_n(B)-\big(m\,s_\lambda(L)+s_\lambda(R)\big)
 \sim \frac{m k}{q}\, r_R\,\epsilon_\tau .
 \tag{3}
\]

We prove all claims including uniqueness. Set
\[
 \ell(t)=\log\frac{1+kt}{1-t},\qquad
 P(t)=(1+kt)(1-t),\qquad
 R_\lambda(t)=\frac{\lambda\ell(\lambda t)}{\ell(t)},\qquad
 J_\lambda(t)=\lambda^2\frac{P(t)}{P(\lambda t)} .
\]
Thus \(s_\lambda'(D(t))=R_\lambda(t)\), \(\ell'(t)=q/P(t)\), and \(D'(t)=(k/q)\ell(t)\). In particular \(s_\lambda'(0^+)=\lambda^2\) and
\[
 s_\lambda''(D(t))
    =\frac{\ell'(t)}{D'(t)\ell(t)}\big[J_\lambda(t)-R_\lambda(t)\big].
 \tag{4}
\]
The curvature at the coloring endpoint is strictly positive at every \(d\in(0,L)\): \(J_{\lambda_0}(t)=k^{-2}(1+kt)/(1+t/k)\) is strictly increasing, and \(R_{\lambda_0}(t)\) is its average on \([0,t]\) with positive weight \(\ell'\). Also \(R_{\lambda_0}(t)\to1/k\) as \(t\uparrow1\) by the logarithm formula, so \(0<r_R<1/k\). By continuity of the curvature at each fixed \(d\in(0,L)\), the unique inflection \(z_\lambda\) tends to \(L\) as \(\lambda\downarrow\lambda_0\).

The functions \(s_\lambda\) converge uniformly on \([0,L]\) to \(s_{\lambda_0}\) because \(D(\lambda t)\) is jointly continuous on the compact parameter rectangle near \(\lambda_0\), including its probability-zero endpoint. Every maximizing allocation must therefore approach, up to permutation, the unique endpoint pattern with \(m\) copies of \(L\), a remainder \(R\) if positive, and the other coordinates zero. Here and below convergence applies uniformly to all maximizing allocations: otherwise a sequence stays away from the asserted limit and compactness yields a contradiction. If \(R>0\), exactly one low coordinate is near \(R\) because of the convex-branch restriction in (1), hence the \(m\) near-\(L\) coordinates must all lie on the concave branch. If \(R=0\), none of the maximizing coordinates can equal \(L\) by §1, so the near-\(L\) coordinates use strictly less than the budget \(mL\). A positive low coordinate is necessary. The same restriction again puts all \(m\) near-\(L\) coordinates on the concave branch. In both cases they must be equal, and stationarity under transfers gives
\[
 r_\tau:=s_\lambda'(y_\tau)
       =s_\lambda'(x_\tau)
       =R_\lambda(1-\epsilon_\tau) .
 \tag{5}
\]
The derivative ratio extends continuously at \(t=0\), so this gives \(r_\tau\to r_R\) also for \(R=0\).

Insert \(\lambda=-(1-\tau)/k\) into (5):
\[
 r_\tau
 =\frac{1-\tau}{k}\,
 \frac{\log(1+(1-\tau)(1-\epsilon_\tau)/k)
       -\log(\tau+(1-\tau)\epsilon_\tau)}
      {\log(q-k\epsilon_\tau)-\log\epsilon_\tau}.           \tag{6}
\]
First \(\epsilon_\tau=o(\tau)\). Otherwise on a sequence \(\epsilon_\tau\ge c\tau\) with \(c>0\), the logarithms diverging in numerator and denominator differ by only \(O(1)\); (6) would give \(r_R=1/k\). With \(\epsilon_\tau=o(\tau)\), the same equation gives
\(\log(1/\epsilon_\tau)/\log(1/\tau)\to\alpha>1\). In particular
\(L-x_\tau=O(\epsilon_\tau\log(1/\epsilon_\tau))\) by the explicit entropy of \(P_{1-\epsilon_\tau}\). For \(R>0\), smoothness on a neighborhood of \(R\) yields \(r_\tau-r_R=O(\tau+L-x_\tau)\); for \(R=0\), the estimate is \(O(\tau+\sqrt{L-x_\tau})\). The latter uses analyticity of \(R_\lambda(t)\) at \(t=0\) locally uniformly in noise and \(D(t)=kt^2/2+O(t^3)\). In either case \((r_\tau-r_R)\log(1/\tau)=o(1)\). Rearranging (6) now gives
\[
 \log(1/\epsilon_\tau)=
 \alpha\log(1/\tau)+\alpha\log(q/k)-\log q+o(1),
\]
which proves the first part of (2); the second follows by expanding \(H(P_{1-\epsilon_\tau})\).

All maximizers are consequently inside the interval of \(x=D(1-\epsilon)\) with \(C\tau^\alpha/2\le\epsilon\le2C\tau^\alpha\) for small enough \(\tau\). On the entire interval,
\(J_\lambda(1-\epsilon)=O(\epsilon/\tau)=o(1)\) and
\(R_\lambda(1-\epsilon)\to r_R>0\) uniformly. By (4),
\[
 s_\lambda''(x)\ \le\ -\frac{c_0}{\epsilon\log^2(1/\epsilon)}
\]
for a fixed \(c_0>0\). Meanwhile \(s_\lambda''(B-mx)\) is bounded if \(R>0\); for \(R=0\) its magnitude is \(O((B-mx)^{-1/2})=O((\epsilon\log(1/\epsilon))^{-1/2})\) by the same analytic derivative expansion at zero. Thus the derivative of
\(s_\lambda'(x)-s_\lambda'(B-mx)\) is strictly negative throughout the interval. It has at most one zero, giving the uniqueness asserted in §2.

Finally put \(\epsilon=\epsilon_\tau\), \(r_\lambda=s_\lambda'(R)\). Then
\[
\begin{aligned}
 s_\lambda(x_\tau)-s_\lambda(L)
    &=-\lambda D'(\lambda)\epsilon+O(\epsilon^2/\tau),\\
 s_\lambda(y_\tau)-s_\lambda(R)
    &=m r_\lambda (L-x_\tau)+o(\epsilon),\\
 L-x_\tau
    &=\frac{k}{q}\epsilon\{\log(1/\epsilon)+\log q+1\}+O(\epsilon^2).
\end{aligned}
\]
The first line uses \(D''=k/P\), of order \(O(1/\tau)\) on the interval from \(\lambda\) to \(\lambda(1-\epsilon)\); the second uses a uniform \(O((L-x_\tau)^2)\) remainder for \(R>0\), or \(O((L-x_\tau)^{3/2})\) at zero. Stationarity (5) implies
\[
 \lambda D'(\lambda)=\frac{k}{q}r_\lambda\{\log(1/\epsilon)+\log q\}+o(1).
\]
Indeed \(D'(\lambda(1-\epsilon))-D'(\lambda)=O(\epsilon/\tau)\), and replacing \(s_\lambda'(y_\tau)\) by \(r_\lambda\) costs \(O((L-x_\tau)^{1/2}\log(1/\epsilon))=o(1)\) also in the grid case. Combining these three expansions and \(r_\lambda\to r_R\) proves (3).

For example, \(q=3,\ n=2,\ B=\log3+(\log2)/3\) has \(D(1/2)=(\log2)/3\), \(r_R=\log(5/2)/(2\log4)\), and \(\alpha=\log4/\log(5/2)>1\). For \(q=3,\ n=2,\ B=\log3\), \(R=0\) instead gives \(\alpha=2\) and \(C=4/3\). These examples and the theorem concern products only; improvement over the globally correlated optimum is not asserted.
