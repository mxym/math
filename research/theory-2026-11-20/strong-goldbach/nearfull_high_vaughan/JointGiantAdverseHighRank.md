# Genuine both-high adverse mass requiring high finite rank

Let \(N\) be even, \(L=\log N\), \(J\Subset(0,1)\) a fixed
central interval of positive length, \(x\in NJ\), \(y=N-x\),
and \(M_N=|J|N\mathfrak S(N)\). Use the genuine composite
mark scores of [the both-high reduction](JointGiantBothHighReduction.md),
including \((x,N)=1\). The two physical high terms on a row
have their actual unique marks \(r,s>N^{.518}\), with
\(x=r m,\ y=s n,\ m,n>1\), and actual cofactor weights
\[
 Q_F(m;x)=\sum_{d\mid m}\mu(d)F\!\left(\frac{\log(dN/x)}{L}\right)
\]
and similarly on the other arm. Their product includes the
true \((\log r)(\log s)\).

This section uses the actual signed identity, not just the
positive count above. Fix an integer \(K\ge1\). There are smooth
flat profiles \(F=G\), \(0\le F\le1\), with support \([0,b]\)
and \(F(0)=1\), for every sufficiently small fixed \(b>0\)
depending on \(K\) (in particular \((K+2)b\le1\)),
with the following consequence. In the literal
\(H_F H_G\) sum of
[the both-high reduction](JointGiantBothHighReduction.md),
take \(\rho=.518\) and \(\lambda_F=\lambda_G=.497\).
At each sufficiently large even \(N\) there is adverse
weight \(\gg_{K,J}M_N/b^2\) on actual squarefree rows
with both high marks \(r,s>N^{.518}\). One cofactor has
negative score and at least \(K+2\) distinct true primes
at most \(N^b\), and **both** cofactors exceed
\(N^{(K+2)b}\). In particular the coordinate with negative
score has at least \(K+4\) distinct prime factors, counting
its high mark. For each fixed \(b\), one may insist that
all prime factors of both coordinates exceed \(N^\eta\)
for a fixed \(\eta=\eta(K,b,J)>0\) chosen last. In this
form there are \(\gg_{K,b,J}M_N/L^2\) such rows, with
finite rank bounds depending on \(\eta\).

The profile changes with \(K,b\); this is not an
unbounded-rank statement for one fixed profile. Adverse
weight means the sum of the **magnitudes** of the negative
terms, not the sign or a lower bound for the full covariance.
These are narrow flat profiles; the conclusion does not
apply to other wider affine profiles with different
endpoint derivatives.

**Profiles and the prime reciprocal envelope.** Put
\(\mu_0=4/\pi\), and for a small \(a>0\) choose a smooth
nonincreasing \(f_{a,K}\) on \([0,\infty)\) as follows.
Its negative derivative is proportional to
\(K(1-t)^{K-1}\) on \(0<t<1\), multiplied by two fixed
smooth cutoff shapes in intervals of width \(a\) near
the lower and upper endpoints, vanishing for \(t\le a\)
or \(t\ge1-a\) and unaltered on \([2a,1-2a]\).
Normalize the negative derivative to have integral one
and set \(f_{a,K}(t)\) equal to its integral from \(t\)
to infinity. Then \(f_{a,K}=1\) near zero, is zero for
\(t\ge1\), takes values in \([0,1]\), and differs from
\(f_{0,K}(t)=(1-t)_+^K\) by \(O_K(a)\) uniformly.
It is Lipschitz with constant \(O_K(1)\).
Extend it to the negative half-line by a fixed compact
smooth function equal to one near zero.
The second derivative has \(L^1\)-norm \(O_K(1)\) and
the third \(O_K(a^{-1})\), by the cutoff widths and
the normalized derivative. Hence
\[
 |\widehat f_{a,K}(\xi)|\ll_K
                \min(1,|\xi|^{-2},a^{-1}|\xi|^{-3}),\qquad
 \int_{\mathbb R}|\widehat f_{a,K}(\xi)|(2+|\xi|)^{\mu_0}\,d\xi
                      \ll_K a^{1-\mu_0}.                           \tag{8}
\]
Use \(F(t)=f_{a,K}(t/b)\), and eventually \(a=b\).

For \(p>2\) put \(c(p)=(p-1)/(p-2)\), set \(c(2)=1\),
and let \(c(m)=\prod_{p\mid m}c(p)\).
Write
\[
 V_\xi(m)=\prod_{p\mid m}|1-e^{i\xi\log p/L}|.
\]
For \(0<u\le1\), its positive harmonic up to \(N^u\)
is bounded by
\[
 \sum_{m\le N^u}\frac{c(m)V_\xi(m)}m
 \le\prod_{p\le N^u}
       \left(1+\frac{c(p)}{p-1}|1-e^{i\xi\log p/L}|\right).          \tag{9}
\]
Indeed the true prime-power harmonic is \(1/(p-1)\).
The difference \(c(p)/(p-1)-1/p\) is absolutely summable
(\(2/(p(p-2))\) for \(p>2\)), independent of the target
and every scale. For each fixed \(\xi,u\), Mertens' prime
reciprocal sum gives
\[
 \sum_{p\le N^u}\frac{|1-e^{i\xi\log p/L}|}{p}
             \longrightarrow I(u|\xi|),\qquad
 I(X)=\int_0^X\frac{|1-e^{it}|}{t}\,dt .
\]
To see the endpoint at zero, the contribution from
\(p\le N^\zeta\) is \(O(\zeta|\xi|)\) by
\(\sum_{p\le Y}\log p/p\ll\log Y\), then let
\(\zeta\downarrow0\). The summable local error in (9)
tends to zero for each fixed \(\xi\) by the same
pointwise limit at each fixed prime. The periodic
function \(|1-e^{it}|\) has mean \(4/\pi\) and its
zero-mean primitive is bounded. Integration by parts
therefore gives
\(I(X)=\mu_0\log(2+X)+O(1)\).
A dominating bound for (9), uniform in \(N,u,\xi\),
is \(O((2+|\xi|)^2)\): split the prime sum at
\(N^{1/(1+|\xi|)}\), use the log-weighted prime harmonic
below and \(|1-e^{it}|\le2\) above. If this split is below
2, \(\log L\le\log(2+|\xi|)+O(1)\) pays the full prime sum.

Fourier inversion, with \(\widehat F(\xi)=b\widehat f_{a,K}(b\xi)\),
bounds \(\sup_v|Q_F(m;v)|\) by the integral of
\(|\widehat F(\xi)|V_\xi(m)\), up to the fixed Fourier
normalization. Here \(v\) ranges over the two actual
central intervals; the spatial phase has modulus one.
Dominated convergence using (9), then (8), proves
\[
 \limsup_{N\to\infty}\sum_{m\le N^u}
       \frac{c(m)}m\sup_v|Q_F(m;v)|
                  \ll_K (1+u/b)^{\mu_0}a^{1-\mu_0}.               \tag{10}
\]
The limit is for fixed \(a,b,u\); its bound has the
explicit dependence displayed, independent of the target.

**Actual prime pair upper and the scale of the signed total.**
For fixed true coefficients \(m,n\) on target units,
\((m,n)=1\); parametrize \(m r+n s=N\) by the integer
line on which \(r,s\) are the two affine forms of steps
\(n,-m\). In the both-high sum its length is
\(O_J(N/(mn))\), with \(N/(mn)\gg N^{2\rho-1}\).
As in the long-parameter portion of
[the joint finite-rank theorem](JointGiantFiniteRank.md),
a positive two-form sieve on the literal primes \(r,s\)
gives a uniform log-weight upper
\[
          \ll_J M_N\frac{c(m)c(n)}{mn}.                             \tag{11}
\]
At \(p\mid mn\) one form is a nonzero constant and the
other has one root. At \(p\mid N\) the two roots coincide;
elsewhere there are two. The log ceiling is absorbed by
the polynomial lower length, with constants independent
of \(a,b\). The same elementary bound applies to either
low-one-prime term with \(n=1\) and \(r>N^{.497}\):
the parameter length \(N/m\gg N^{.497}\) remains
polynomial and both prime arguments exceed the
chosen small polynomial sifting ceiling. The case
\(m=n=1\) bounds \(R_J(N)\ll_J M_N\).

Hence by (10) for \(u=1\), with \(a=b\), each genuine
low-one-prime cross has absolute magnitude at most
\(O_{K,J}(M_N b^{1-2\mu_0})\) for large \(N\).
The exact flat both-high reduction then bounds the
absolute value of the **signed total** \(H_FH_G\)
by \(O_{K,J}(M_N b^{1-2\mu_0})\).
But [the genuine rough positive subset](JointGiantPositiveBothHigh.md)
gives positive weight \(\gg_J M_N/b^2\)
on the same actual score. Since \(2\mu_0-1<2\),
the negative terms have total magnitude
\(\gg_{K,J}M_N/b^2\) for small enough \(b\) first and
then large \(N\).

**Exclusion of low-active-rank adverse terms.** For any
real spatial base \(t_0=\log(N/v)/(bL)\ge0\), the
alternating finite differences of \(f_{0,K}\) of orders
\(0,\ldots,K+1\) are nonnegative. Indeed
\((-1)^j f_{0,K}^{(j)}\) is nonnegative as a distribution
for \(j\le K+1\), including the positive endpoint atom
for \(j=K+1\); integrate over the difference steps, or
first mollify this identity. For \(Q_F\), only primes
\(p\le N^b\) in its cofactor can contribute nonempty
subsets. If the cofactor has \(j\le K+1\) such distinct
prime factors, with positive steps \(u_i=\log p_i/(bL)\),
the negative part of its \(Q_F\) is
\[
                          O_K(\min(a,u_1,\dots,u_j)).
\]
The bound by \(a\) follows from the uniform approximation
to \(f_{0,K}\); the others from the uniform Lipschitz
bound and cancellation across the selected step. For
\(j\le1\) the negative part is exactly zero by monotonicity.

To sum the remaining \(2\le j\le K+1\), group the
cofactor into powers of exactly those \(j\) primes and
a free factor with all primes \(>N^b\). This is valid
also before removing proper powers. Its rough harmonic
with weight \(c\) is \(O(1/b)\) by the positive Euler
product. Each chosen prime has total power harmonic
\(c(p)/(p-1)\). Write the minimum as
\(\int_0^a {\bf1}_{u_1>h,\dots,u_j>h}\,dh\).
Uniformly for \(0<h<a\),
\[
              \sum_{N^{bh}<p\le N^b}\frac{c(p)}{p-1}
                      \ll 1+\log(1/h)
\]
by Mertens (if the lower endpoint is below 2, the same
bound pays the full sum). Thus the whole negative-arm
harmonic with such \(j\) is at most
\(O_K((a/b)(1+\log(1/a))^{K+1})\).
By (10) and (11) the corresponding actual joint adverse
term, with \(a=b\), weighs
\(O_{K,J}(M_N b^{1-2\mu_0}(1+\log(1/b))^{K+1})\);
this is \(o_b(M_N/b^2)\) in the order of limits in use.
Apply it separately to either possible negative arm.

Also discard either cofactor \(\le N^{(K+2)b}\).
Use (10) with \(u=(K+2)b\) on that arm and \(u=1\) on
the other. Its absolute joint cost by (11) is
\(O_{K,J}(M_N b^{2-3\mu_0})=o_b(M_N/b^2)\), since
\(3\mu_0-2<2\). Thus \(\gg_{K,J}M_N/b^2\) actual
adverse mass remains. Its negative arm has at least
\(K+2\) distinct primes \(\le N^b\). If it had altogether
only \(K+2\) factors on a squarefree row, their product
would not exceed \(N^{(K+2)b}\). The larger cofactor
condition excludes that case.

Finally, for fixed \(K,b\) take \(\eta>0\) sufficiently
small. Marking any \(p\le N^\eta\) in (9) costs at most
\(O(\eta|\xi|)\) times its unrestricted product, using
\(\sum_{p\le N^\eta}\log p/p\ll\eta L\).
Fourier integration with the fixed smooth profiles and
(11) thus bounds the actual absolute loss on either arm
by \(O_{K,b,J}(\eta M_N)\), uniformly for large \(N\).
Above that floor the count of integers containing a real
prime square on either arm is \(O(N^{1-\eta})\); the
fixed crossed divisor moments pay the original weights
with a power saving. On the surviving squarefree rows
both ranks are bounded by \(1+(1-\rho)/\eta\).
Each coefficient has magnitude at most \(L^2\) times a
fixed constant depending on that rank bound. This proves
the claimed count and genuine high-rank adverse weight.
