# A zero-mean opposite-leg interaction and its low-rank calibration

Use even $P$, $L=\log P$, $F=n(P-n)$, the fixed central $W,X_P,\mathfrak S(P)$ and the squarefree normalization of the [coupled benchmark](https://github.com/mxym/math/commit/5190f4df). Fix $0<\eta<1/50$ and $\kappa=10^{-4}$. For a fixed smooth function $\phi$ on $[0,\infty)$, equal to 1 near zero and vanishing beyond $\kappa$, put
$$
T_c(n)=\sum_{\substack{P^\eta\leq\ell\leq\sqrt P\\
          \ell\mid n,\ \ell\ {\rm prime}}} c_\ell
          \sum_{d\mid n}\mu(d)\phi(\log d/\log\ell).
$$
The coefficients $|c_\ell|\leq1$ may be arbitrary; a fixed upper bound instead costs the corresponding constant. The other leg can use independent coefficients and a separately fixed shape with the same properties.

**Opposite-leg theorem.** For every $A>0$,
$$
 \sum_n W(n/P)\mu^2(F) T_c(n)T_e(P-n)=O_{A,W,\phi,\eta}(P L^{-A}).
\tag{1}
$$
Finite separable combinations are allowed. This estimates an actual reflected interaction, not just an ordinary product of two separate means. The proof does not cover arbitrary nonseparable coefficient matrices of large rank.

**The CRT charts.** In the original masked sum every tag and divisor label is coprime to $P$. Open the two squarefree indicators as in the [fixed-rank proof](https://github.com/mxym/math/commit/f39f90b2), first keeping the unit condition, with square labels $u,v\leq L^B$ and $(uv,P)=(u,v)=1$. For sufficiently large $B$ the omitted rows cost $O_A(PL^{-A})$ by the same Cauchy divisor-moment estimate, since both entire weighted tag sums are bounded by fixed powers of the ordinary divisor functions. Open the remaining unit mask as $\sum_{g\mid(P,n)}\mu(g)$. For $g>P^{10^{-5}}$ the physical contribution is $O(P^{1-10^{-5}+o(1)})$ by counting its multiples and divisor bounds; its model is similarly small by the absolute reciprocal bounds below. Put $Z=P/g,\ n=gx$.

In a nonempty system assign prime tag $\ell$ and squarefree divisor label $d$ to the first side, and tag $k$ and divisor $b$ to the second. In particular $\ell\nmid d$ and $k\nmid b$ by support. Write $d=d_0d'$, $d_0\mid\operatorname{rad}(u)$, and $b=b_0b'$, $b_0\mid\operatorname{rad}(v)$, with the remaining labels coprime to $Puv$. Systems with $d$ meeting $v$, or $b$ meeting $u$, are incompatible. Tags are larger than $u,v$. The two actual moduli are
$$
          M_1=u^2\ell d'\mid x,\qquad M_2=v^2 k b'\mid Z-x .
$$
They must be coprime (they are both coprime to $Z$). The condition $(M_1,M_2)=1$ itself eliminates shared tags, shared divisor primes and crossed tag/divisor labels. All weights concerning the first factor only, including the shape in $\log(d_0d')/\log\ell$, are packed in its coefficient sequence on $M_1$; likewise on $M_2$. These coefficients are $O(\tau(M_i))$ uniformly and their dyadic square norms are $O(M_i^{1/2}L^{O(1)})$ when $M_i$ in this bound denotes the corresponding dyadic size. No independent Fourier cost in the tag variable is necessary.

For $M_1M_2\leq Z/L^H$, replacing each CRT progression by its integral costs $O_W(1)$, totaling $O(ZL^{O(1)-H})$ for fixed square labels (bound the convolution by $\tau_4$). Use a smooth logarithmic transition: complement low support extends to $2Z/L^H$. Everywhere $M_i\leq P^{(1+\kappa)/2}L^{2B}\leq Z^{.501}$ for large $P$. On the high chart $M_1M_2\geq Z/L^H$ the two sizes are therefore comparable on the exponent scale, each at least $Z^{.498}$ and their product at most $Z^{1.002}$. A tighter bound from the actual tags is $M_1M_2\leq Z^{1.0002}$ for large $P$.

Poisson summation on $x$ leaves the model from $h=0$. The nonzero terms have prefactor $Z/(M_1M_2)$, Fourier amplitude $\widehat W(hZ/(M_1M_2))$ and a phase $e(\pm hZ\overline M_1/M_2)$, optionally times its smooth reciprocity factor. Truncate $|h|\leq Z^{.001}$; all later frequencies have arbitrary fixed power savings by repeated integrations by parts. The separated dyadic normalized amplitude and its fixed log derivatives are uniformly bounded (integrate by parts also after introducing reciprocal phase). A smooth function of the log product on these dyads, including the transition at $Z/L^H$, separates by Mellin inversion with $O(1)$ cost in transform $L^1$. For each $h\ne0$ the [Bettin–Chandee Theorem 1](https://arxiv.org/pdf/1502.00769) with singleton auxiliary sequence bounds the bilinear sum, writing $M,N$ for dyadic sizes, by
$$
 (MN)^{1/2+o(1)}\left(1+\frac{|h|Z}{MN}\right)^{1/2}
 \left((MN)^{7/20}(M+N)^{1/4}+(MN)^{3/8}(M+N)^{1/8}\right).
$$
The first exponent is at most $.85(1.0002)+.501/4+.0005+o(1)$ and the second at most $.875(1.0002)+.501/8+.0005+o(1)$. Including $Z^{.001}$ heights and the at-most-logarithmic prefactor still saves a fixed power. Dyads and finitely many polylogarithmic square-label choices do not affect it. Arbitrary-log errors in the low chart are proportional to $Z$, so summing $1/g\ll$ harmonically over the target divisors costs $O(\log L)$. This proves the comparison with the full CRT model.

**Bivariate residue.** Restore $u,v$ to infinity in the model: for fixed compatible tags and labels its density is bounded by
$$
  \frac{(d,u)(b,v)}{g u^2 v^2 db}\,
                  \frac{(\ell,u)(k,v)}{\ell k}.
$$
This applies to compatible assignments, where no tag meets a divisor on the opposite side. Summing each tag multiplier costs $O(\log L+\omega(u)+\omega(v))$, even when a restored square label contains a tag. Summing $d,b$ reciprocally costs $O(L^2 2^{\omega(u)+\omega(v)})$. The absolute square-label tails are thus $O_A(PL^{-A})$ after increasing $B$. For restoring $g>P^{10^{-5}}$ use the same bounds and $\sum_{g\mid P,\ g>P^{10^{-5}}}1/g\leq P^{-10^{-5}+o(1)}$.

The bivariate Mellin density at two distinct prescribed tags leaves the external factor $(1/\ell-1/\ell^2)(1/k-1/k^2)$. The remaining series $\mathcal D(s,t)$ omits both tag primes. Its local factors at generic primes and target primes, respectively, are
$$
1-2/p^2-(1/p-1/p^2)(p^{-s}+p^{-t}),\qquad 1-1/p.
$$
Indeed on untagged residues each leg has valuation exactly 1 with probability $1/p-1/p^2$ at a generic prime, and these two cases are disjoint. Thus $\mathcal D(s,t)=\zeta(1+s)^{-1}\zeta(1+t)^{-1}\mathcal H(s,t)$ where $\mathcal H$ is holomorphic and $(\log L)^{O(1)}$ in $\Re(s),\Re(t)\geq-c/\log L$. After division by $(1-p^{-1-s})(1-p^{-1-t})$, generic absolute tails converge uniformly. At $p\mid P$ split at $L$ as in the one-variable proof; omitting the two polynomial tags costs a bounded factor.

For $\mathcal D(s,t)=\sum a_{db}d^{-s}b^{-t}$, double inversion against $Y^s/s^2$ and $U^t/t^2$ gives
$$
 \sum_{d,b}a_{db}\log_+(Y/d)\log_+(U/b)
       =\mathcal H(0,0)+O_A(L^{-A})
$$
uniformly when $Y=\ell^w,U=k^z$ with $w,z$ in the compact supports of the second derivatives of the two shapes, bounded away from zero by flatness. Both radii are consequently fixed positive powers of $P$. Truncate each variable at $\exp(c_1\sqrt L)$, shift both to $-c_2/\sqrt L$ inside the zeta zero-free region, and bound mixed shifted integrals and residues first at one variable then the other. Only the double residue survives; each left line and horizontal segment gives $O(L^{O(1)}e^{-c_3\sqrt L})$. Now integrate the respective $\phi''$ weights using $\phi(w)=\int_w^\infty(z-w)\phi''(z)\,dz$ and divide by $\log\ell\log k$. Since $\int\phi''=-\phi'(0)=0$, the double residue cancels. The reciprocal external factors are summable over the allowed tags at $O_\eta(1)$ cost. This proves (1).

**Actual scope and a quantitative failure of a direct repair.** In the previous single-mark detector take both shapes zero beyond $\kappa$, both lower tag cuts below $1/50$, and write $c(t)$ for the active amplitude. To suppress actual rank three on $1/50<t<.49$ one must have $c(t)\geq 8t(1-t)-4\delta^2$ almost everywhere (allowing a common fixed-smooth base of width $\delta\leq10^{-5}$). This is the earlier independent PNT calibration. Adding an opposite-leg pair mark of amplitude $c(t)+c(u)$ is now a zero-mean correction by (1), and restores a balanced semi×semi row exactly to zero at leading scale while leaving prime×semi unaltered.

It does *not* repair prime×triprime rows. In the domain of three exponent shares $x,y,z\in[1/50,.49]$ with $x+y+z=1$, all three tags count and every relevant flat divisor sum is exactly 1 for large $P$ because every nontrivial divisor exponent exceeds $\kappa$ times every tag exponent. On such a reflected prime×triprime row no possible opposite-leg interaction contributes; the base is zero at total rank four, leaving the negative debit $\sum c(x)$ in units $L^2$. On two such triprime legs the base is zero at total rank six. Each of the three marks on each side occurs three times in the additive-amplitude cross correction, hence the final score is **positive** with coefficient $2\sum c(x)$ over all six factors. In contrast to the rank-four obstruction this last conclusion uses the *specified* additive-amplitude repair.

For exact normalized average bounds put
$$
 d\mu=\frac{dx\,dy}{6xyz},\quad Z=\int d\mu,\quad
 A=\int\sum_{s\in\{x,y,z\}}(8s(1-s)-4\delta^2)\,d\mu
$$
over the displayed polygon ($z=1-x-y$; equal exponent lines have measure zero and the factor 6 removes label ordering). By the same genuine independent-prime PNT/Jacobian over dyadic even targets as in the balanced-semiprime obstruction, the doubled prime×triprime negative submass averages at least $2A X_P\mathfrak S(P)$ in the normalized dyadic sense; the triprime×triprime positive submass for the additive correction averages at least $4ZA X_P\mathfrak S(P)$. The enclosed rational inner-rectangle calculation gives $2A>6.4$, $4ZA>8.3$. In particular, every opposite-leg-only repair still has large negative rank-four contributions, and the specific additive repair already exceeds the prospective positive threshold on one actual rank-six population *on average*. These are not estimates on every target, and neither proves nor precludes a signed compensation comparison.

## Related work and exact replay

The [earlier singly marked calibration](../marked_calibration_barrier/Proof.md) does not cover this genuine two-leg term. [Chan’s November preprint](https://aixiv.science/pdf/aixiv.261111.000001v1.0.pdf) uses paired marked families to bound different sieve sums in its prime-or-semiprime theorem; [Pham’s October preprint](https://www.preprints.org/manuscript/202610.3061) treats other actual signed reflected comparisons. Neither is invoked for the two-tag null or the rank-six calibration here. The companion [exact replay](replay.py) checks the finite local and numerical lower estimates, not the cited dispersion theorem.
