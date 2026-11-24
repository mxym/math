# Total budget ceiling for every standard BV pair credit in a Richert family

Written research note. This is an optimistic upper ceiling on what the **ordinary conditional BV-linear lower main terms** can book as a signed pair credit. It is not an upper estimate for the true aggregate credit counts. It covers all nonnegative deductive pair functions of two distinct angles in the box of parameters below, not only the [explicitly paid .055 tranche](PrimeOppositeP3SignedTwoMarkCredit.md).

Use the genuine square-root prime population for \(N\), with \(B=2XS_N/\log N\) and the rough cutoff \(z=N^\mu\). Let
\[
 .03\le\mu\le.062,\qquad .385\le\beta\le.45,\qquad \eta=4-1/\beta.
\]
Keep the standard **positive one-mark** Richert penalty \(W_\beta=\sum_{q\mid N-p}(1-t/\beta)_+\). Allow subtracting any nonnegative unordered pair credit \(V(t,u)\), independently at each angular pair, wherever the standard conditional prime-source BV linear sieve has a positive lower, and no unproved credits elsewhere. We impose only the necessary universal rank-four angular condition for the score \(1-(W_\beta-\sum V)/\eta\) to be nonpositive; any true additional rank constraints can only make the permissible credits smaller. The one-mark debits are paid by the old conditional linear upper and the exact ordinary asymmetric affine Selberg upper (and by no new joint upper estimate). In the .05-and-above middle range one can also include the previously analyzed optimized squares where the existing true-LCM support obstruction forbids a lower cap than affine.

## Universal ceiling on each possible individual credit

Maximal arithmetic BV level on the square-root source is \(N^{.249}\) as used in the project. After two known true prime marks of sum \(m=t+u\), a positive standard linear lower needs \(m<.249-2\mu\). For such a pair, \(m\le.189\); in particular both marked factors are below \(\beta\). Test on rank four with the two other angles arbitrarily close, but distinct, around \((1-m)/2\). They exceed .4 and do not occur in any other supported credit pair. For the standard Richert penalty and total angle 1,
\[
 W_\beta-\eta=\sum_{t_i>\beta}(t_i/\beta-1).
\]
The two other angles can therefore be chosen to have total excess as close as desired to \(((1-m)/\beta-2)_+\). It follows that a legal universal angular credit must satisfy
\[
 0\le V(t,u)\le ((1-m)/\beta-2)_+ .
 \tag{1}
\]
A sum smaller than 1 by a shrinking collar has the same necessary limit, with a vanishing error. This is just a test profile enforcing the specified size-only certificate, not a claim about actual realization of its angles on a fixed \(N\).

The available **lower** main term in units \(B/(qr)\), for any conditional residual level \(d\le .249-m\), is \(g(d/\mu)/d = e^{-\gamma} f_{\rm lin}(d/\mu)/(2\mu)\le.281/\mu\). Here \(f_{\rm lin}\le1\), and the elementary \(e^{-\gamma}/2<.281\) certificate is in the arbitrary single-mark note. Ignoring all global competition between different pair credits, granting each legal individual credit its pointwise maximum in (1), and also granting this optimistic lower coefficient everywhere therefore gives total booking coefficient at most
\[
 C^+(\mu,\beta)=\frac{.281}{\mu}
 \int_{2\mu}^{\min(.249-2\mu,\,1-2\beta)}
   \frac{(1-m)/\beta-2}{m}
       \log\!\left(\frac{m-\mu}{\mu}\right)\,dm .
 \tag{2}
\]
An empty integral is zero. We integrate once over unordered \(t<u\) with harmonic measure \(dt\,du/(tu)\); the factor \(\log((m-\mu)/\mu)/m\) is exactly \(\int_\mu^{m/2}dt/[t(m-t)]\). No factor of two may be inserted. The numerical expression is decreasing in both \(\mu\) and \(\beta\) (alternatively compare the nonnegative integral on the original \((t,u)\) domain).

Equation (2) is **not** a restriction on the true number of marked rows or on a joint, analytic lower estimate for their signed weighted sum. It only bounds the amount certified by summing this family of individual lower linear main terms. The proof can benefit by a larger credit if that actual new lower information is established.

## Strict uniform budget gap

Even with optimistic classical upper coefficients the positive one-mark charge cannot be below
\[
 P^-(\mu,\beta)=\int_\mu^\beta \frac{1-t/\beta}{t}
 \min\left\{\frac1{.25-t}\ (t<.25),\
                  \frac2{(.5-t)^2}\right\}\,dt .
 \tag{3}
\]
The first entry is omitted at \(t\ge.25\). This is the floor on the BV upper and exact affine upper proved in the one-mark note, allowing optimistic .25 source test level. Exact asymmetric kernel \(J\) does not beat the two-root denominator used for the floor. The available base cost in these undivided units is at most \(\eta(.281/\mu)\).

A directed rational enclosure yields, uniformly on the entire parameter rectangle above,
\[
  P^-(\mu,\beta)-C^+(\mu,\beta)-\eta(.281/\mu)
     \ \ge\ .192728275\ >.19 .
 \tag{4}
\]
Thus even a penalty receiving every allowed individually maximal lower credit simultaneously cannot pay the standard Richert budget, before imposing any competition among credits. As concrete instances at \(\beta=.4\), the optimistic credit ceiling is \(1.688024 B\) at \(\mu=.03\), \(0.562163 B\) at \(\mu=.04\), and \(0.047714 B\) at \(\mu=.055\); at the latter point (3) alone is at least \(14.75978 B\), against the optimistic undivided base \(7.66364 B\). These are generous ceilings: they count all admissible signed pair lower main terms rather than merely the paid \(>.00051 B\) tranche.

**Replay.** In [the exact checker](check_p3_all_bv_pair_credits_ceiling.js), use parameter boxes of size .001 and integration mesh .0005. For a box \([\mu_0,\mu_1]\times[\beta_0,\beta_1]\), take the lower penalty at \((\mu_1,\beta_0)\) since (3) decreases with \(\mu\) and increases with \(\beta\); take the upper credit at \((\mu_0,\beta_0)\); and upper-bound the base at \((\mu_0,\beta_1)\). In (3), the minimum of the two increasing inverse denominators is increasing on its whole domain, while \((1-t/\beta)/t\) decreases, so the product of the lower endpoint factors separately gives a lower rectangle. In (2) its positive rational prefactor in \(m\) decreases, while its positive logarithm increases; use the left and right endpoint upper factors respectively. The logarithm at \(x\ge1\) is bounded upward by the first 14 positive terms of the atanh series at \(u=(x-1)/(x+1)\), plus \(2u^{29}/(29(1-u^2))\). Round each term in the prescribed direction into integer \(10^{-9}\) ticks. Replay returned minimum 192728275 ticks, attained at the first grid box. The special .4 example outputs use the same actual code functions at exact corners. Scope excludes arbitrary alternative positive one-mark penalties when used in combination with signed pairs, more general angular nonlinear terms, analytically improved one- or two-mark caps, and cutoff/penalty ranges outside the stated box.

The checker also overgrants the conditional pair lower a total exponent \(.25\) by replacing \(.249\) by \(.25\) in the pair-support condition and in the upper endpoint of (2), leaving the very same base and penalty allowances. Then \(m\le.19\) and the separate rank-four argument still applies. The directed uniform deficit remains \(0.183967137>0.18\). So the obstruction is not caused by the use of a \(.001\) safety margin in the existing square-root BV arithmetic. It is still a budget obstruction for the particular functions and caps in (1)–(3), not an arithmetic lower bound on the actual mark penalty.
