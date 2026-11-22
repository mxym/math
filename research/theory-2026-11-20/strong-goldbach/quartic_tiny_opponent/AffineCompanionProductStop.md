# A true product-stopped sieve for the affine companion

Keep the individual even target, real paired interval, target units,
\(H\), \(Q=R+W_1+W_2\), and
\(\widetilde H=H+Q\) from the
[compensated quartic comparison](../halfzero_detector/CompensatedDebit.md).
Here \(M=|J|N\mathfrak S(N)\) and \(L=\log N\).
Use the literal original \(Q\) throughout. The argument improves the
small-factor treatment in
[the affine companion](AffineCompanionTinySector.md); it does not
replace the pointwise quartic by the companion on an unpriced region.

Fix \(0<\sigma<1/4\), and choose a smooth compact real profile \(f\)
with \(f(t)=1-t\) on \(0\le t\le\sigma\) and \(f(t)=0\) for
\(t\ge c\), where \(\sigma<c<1/2-\sigma\).
Use the same own-log squarefree convention and true prime subtraction
for \(H_f\) as in the affine companion, and write \(S=H_f+Q\).
For fixed \(0<b\le\sigma/8\), set
\[
 D_b(n)=1_{P^-(n)>N^b},\qquad T_b(n)=D_b(n)H_f(n)+Q(n),\qquad
 U=\sigma/b,
\]
and define
\[
 E(U)=\inf_{s\ge0}
 \exp\!\left(-sU+2\int_0^1\frac{e^{sv}-1}{v}\,dv\right).
\]

**Theorem.** In the fixed-\(b\), large-even-target limit,
\[
 \begin{split}
 \langle\widetilde H,\widetilde H\rangle
   &=\langle T_b,\widetilde H\rangle+O_{J,f,\sigma}(E(U)M)+o_b(M),\\
   &=\langle T_b,T_b\rangle+O_{J,f,\sigma}(E(U)M)+o_b(M).
 \end{split}                                                     \tag{1}
\]
The constants in the \(O\)-terms do not depend on \(b\).
In particular
\[
 E(U)\le \exp\{-U\log(U/2)+U-2\}.
\]
Only \(H_f\) is deleted from an arm with an actual prime factor
\(\le N^b\); \(Q\) is kept even there. For \(b<.005\) it vanishes on
those physical rows, so this is the earlier deletion with a stronger
error. For larger \(b\) such rows can still carry the original
nonnegative weight \(Q\). No pointwise or global residual sign
is asserted.

## 1. Exact stopping and the zero marked moments

For the moment fix \(0<a<b\), and let \(\mathcal P\) be the true
primes in \((N^a,N^b]\). Put \(D_{a,b}(n)=1_{(n,\prod_{p\in\mathcal
P}p)=1}\). Expand \(\prod_{p\in\mathcal P}(1-1_{p\mid n})\) in a
fixed decreasing prime order. On a branch, stop as soon as the
product of the selected genuine primes exceeds \(N^\sigma\).
Every subset of product at most \(N^\sigma\) is wholly expanded;
its sign is the literal Möbius sign. A stopped branch has its
selected product times a still-unexpanded product of remaining
absence factors, of magnitude at most one. Each subset has just
one history in the chosen order. Thus
\[
 D_{a,b}(n)=P(n)+E_{a,b}(n),\qquad
 P(n)=\sum_{\substack{h\mid n,\ h\le N^\sigma\\
               h\ {\rm squarefree},\ p\mid h\Rightarrow p\in\mathcal P}}
                \mu(h),\qquad
 |E_{a,b}(n)|\le
   \sum_{\substack{h\mid n,\ N^\sigma<h\le N^{\sigma+b}\\
               h\ {\rm squarefree},\ p\mid h\Rightarrow p\in\mathcal P}}
                1 .                                              \tag{2}
\]
The displayed sum on the right permits extra compatible subsets;
the actual remainder is a sum only over first crossings.

For each nonempty active \(h\le N^\sigma\), the genuine marked
divisor coefficient of \(H_f\) is
\[
              g_h(t)=\sum_{e\mid h}\mu(e)f(t+\log e/L).
\]
Its derivative at zero is zero, since each \(0\le\log e/L\le\sigma\)
lies in the affine interval. The term \(\Pi\) is absent on these
marked central rows. The proof of the marked identities in
[the affine companion, §2](AffineCompanionTinySector.md) works with
these product cuts: the tested \(hd\le N^{\sigma+c}\) is strictly
sub-root, and \(h d d'\) with an unmarked sharp opponent has a
fixed power reserve below \(N\). On two actively marked arms the
joined modulus is at most \(N^{2(\sigma+c)}<N\).
The masks \((d,h)=1\), the target units, and the reduced \(Nh\)
or \(Nhy\) mask are unchanged. At fixed \(a,b\) the number of
named marks in a row or an opened product is bounded independently
of \(N\); grouping at the joined moduli costs fixed divisor weights.
The reciprocal sum over the active \(h\)'s is bounded by
\(\prod_{p\in\mathcal P}(1+1/p)\), bounded at fixed \(a,b\).
Thus, before the crossing errors in (2), all nonempty terms
with a factor \(P-1\) against \(H_f,H\), or the same original
\(Q\), have zero principal. The same holds if the other detector
also carries \(P-1\).

The assumptions \(f(0)=1,f'(0)=-1\) still give the exact total
equality at scale \(M\) of \(S\) paired with \(S\) or \(\widetilde H\)
and \(\widetilde H\) paired with itself, by the proof in
[the affine companion, §1](AffineCompanionTinySector.md).
The general \(\sigma\) range above only uses the stated strict
support inequality, not any sign of a profile.

## 2. The actual prime phases at a first crossing

On a compatible fiber \(h\mid x,h'\mid y\) use actual primitive
quotient forms \(u_0+h'v,v_0-hv\), with \(hu_0+h'v_0=N\).
On target units \((h,h')=(hh',N)=1\); incompatible fibers
are absent. At each prime of \(hh'\) there is one root and
at each non-target prime outside \(hh'\) two distinct roots.
At target primes the coincident root is removed by the literal
unit condition. The interval has length \(\asymp_J N/(hh')\).
This is still polynomially long uniformly for
\(h,h'\le N^{\sigma+b}\), since \(2(\sigma+b)<9/16\);
the single-mark case is obtained by taking \(h'=1\).

Apply the positive multiplicative Fourier envelope of
[the quartic detector, §2](../halfzero_detector/Proof.md)
on these two actual affine forms. Extract
\(A_\xi(p)=|1-e^{i\xi\log p/L}|\) exactly once for each marked
prime \(p\), rather than replacing it by 2. In the remaining
quotient weight reset the positive powers of that named prime
to 1; the change in the local factor is bounded by the leading
prime product \(\prod_{p\mid hh'}(1+O(1/p))=1+o_{a,b}(1)\).
Zero scores on nonsquarefree rows only reduce this positive
bound. For own-log profiles substitute \(\xi\log x/L\) or
\(\xi\log y/L\) in the Fourier transform, using their common
decay envelope at fixed central \(J\); the arithmetic prime
phase remains the displayed \(A_\xi\).
The resulting bound on the fiber is the usual
\(M/(hh')\) times the extracted phase products and the
usual integrable Fourier weights. All constants outside
the extracted products are fixed uniformly in \(a,b\),
after taking \(N\) sufficiently large at these fixed parameters.
A marked detector has no prime subtraction on the fiber;
on the opposite arm \(|Q|\le |H|\) and a genuine prime term
can also be bounded by the usual positive rough weight.

For any fixed \(s\ge0\), the reciprocal sum of the extracted
products over the positive crossing envelope of (2) is at most
\[
 \begin{split}
 &e^{-sU}\prod_{p\le N^b}
             \left(1+\frac{e^{s\log p/(bL)}A_\xi(p)}p\right)\\
 &\quad\ll e^{-sU+2\int_0^1(e^{sv}-1)\,dv/v+o_{b,s}(1)}
                        (2+b|\xi|)^{c_0},
 \end{split}                                                     \tag{3}
\]
with any fixed \(c_0>4/\pi\).
The first step is Rankin with the actual \(\log h/L>\sigma\).
In the exponent of the Euler upper, split off the unweighted
prime phase sum, use the true phase harmonic of the quartic
proof at effective scale \(N^b\) and frequency \(b\xi\),
and bound the tilted difference by \(A_\xi(p)\le2\).
Its genuine prime reciprocal limit is the integral in (3);
the integrand before reciprocal weighting vanishes at zero,
so partial summation from \(\sum_{p\le z}\log p/p=\log z+O(1)\)
suffices. Alternatively convexity gives the upper
\(2(e^s-1)\) in place of the integral. All incompatibilities
may be omitted in the positive harmonic upper, not in the
literal fiber.

The extra power \((2+b|\xi|)^{c_0}\) is on the **smooth
companion arm**. Its Fourier transform absorbs this factor
with uniform constant for \(b\le\sigma/8\). Thus a single
crossing costs \(O_{J,f,\sigma}(E(U)M)\) in limsup, also
against the original \(\widetilde H\).
Two crossings give the square of the same saving: use the
compatible two-mark fiber above and independently upper its
two positive reciprocal sums by (3).
The elementary bound \(|P|\le1+|E_{a,b}|\) from (2) then pays
products of the two stopped expansions by the two single
crossings and their genuine double intersection. No factor
from the number of inactive labels remains.

Finally the replacement of \(D_{a,b}\) by \(D_b\) costs
\(O_{J,f,\sigma}(a^\gamma M)\) in these positive paired
envelopes, since any changed row has a true prime factor
\(\le N^a\). Take the target limit first and then \(a\downarrow0\).
This does not affect (3). Optimize \(s\) after this limit;
choosing \(s=\log(U/2)\) in the convexity upper proves the
stated superexponential estimate. Reassemble both profiles
with exactly the original \(Q\) on each arm. This proves (1);
there is no assumption about the sign of the remaining pair.
