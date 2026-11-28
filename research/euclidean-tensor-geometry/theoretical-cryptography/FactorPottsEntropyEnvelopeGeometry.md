# Exact entropy envelope geometry for the nonbinary Potts channel

Research note, 28 November 2026. On a \(q\)-letter alphabet, \(q\ge3\), write \(\pi\) for the uniform law and let
\[
T_\lambda p=\lambda p+(1-\lambda)\pi,\qquad
-1/(q-1)\le\lambda\le1.
\]
All logarithms are natural. Exclude the degenerate \(\lambda=0,1\) until the end. At fixed input entropy, the output entropy has both a sharp pointwise range and a sharp conditional range. The lower pointwise extremum is known. Here the new calculations explicitly resolve the shape of its previously implicit time-sharing envelope, give the opposite pointwise boundary and its exact polygonal envelope, and determine all finite-block equality cases for the known tensorized lower bound. None of the finite-block statements asserts the unrestricted optimizer at a nonattaining entropy.

**Prior-art distinction.** [Gu–Polyanskiy, Proposition 18 and Theorem 4](https://people.lids.mit.edu/yp/homepage/data/nlsi_potts.pdf) give the sharp pointwise minimum, the abstract least concave majorant in entropy deficit, and the optimal asymptotic product-channel bound. Their Proposition 26 proves a linear piece near zero deficit is necessary. Proposition 33 computes the coloring-channel relative-entropy contraction coefficient, which is the slope of the chord in that case below. We start from their pointwise characterization. The general convexification and product-channel chain rule go back to [Ahlswede–Körner, Theorem 1](https://noah.nrw/ubbihs/download/pdf/5110167). Our claims are the explicit geometry, reverse boundary, and finite equality and approximation refinements, not the original general tensorization or the scalar minimum.

## 1. The sole tangent on the lower boundary

Set \(a=q-1\), \(B=\log q\), and define
\[
\Psi(u)=\frac{(1+u)\log(1+u)+(a-u)\log(1-u/a)}{a+1},
\qquad -1\le u\le a .
\]
Use the continuous convention at the endpoints. For \(u\ge0\), \(\Psi(u)\) is the deficit \(B-H\) of the probability vector with one entry \((1+u)/q\) and all the other entries \((1-u/a)/q\). It increases strictly from \(0\) to \(B\). By Gu–Polyanskiy the largest output deficit at fixed input deficit \(x\) is
\[
s_\lambda(\Psi(u))=\Psi(\lambda u),\qquad 0\le u\le a,
\]
with equality only at permutations of this one-spike vector (including the uniform and pure endpoints).

For \(-1/a<\lambda<1\), \(\lambda\ne0\), the profile \(s_\lambda\) is strictly convex up to a unique interior inflection \(x_{\rm bend}\) and strictly concave thereafter. There is a unique \(\tau\in(x_{\rm bend},B)\) solving
\[
\tau s_\lambda'(\tau)=s_\lambda(\tau).
\]
Writing \(\eta=s_\lambda(\tau)/\tau\), the least concave majorant \(\widehat{s}_\lambda\) is
\[
\widehat s_\lambda(x)=
\begin{cases}
\eta x,&0\le x\le\tau,\\
s_\lambda(x),&\tau\le x\le B .
\end{cases}
\tag{1}
\]
The first segment has no other points of contact with \(s_\lambda\). For the coloring endpoint \(\lambda=-1/a\), \(s_\lambda\) is strictly convex throughout the interior, and (1) holds with \(\tau=B\) and \(\eta=(B-\log(q-1))/B\).

**Proof.** Put \(P(u)=(1+u)(a-u)\). Then \(\Psi''(u)=1/P(u)\) and \(\Psi'(0)=0\). With derivatives in the deficit coordinate,
\[
s_\lambda'(\Psi(u))=\frac{\lambda\Psi'(\lambda u)}{\Psi'(u)},\qquad
R(u)=\frac{\lambda^2\Psi''(\lambda u)}{\Psi''(u)}
     =\lambda^2\frac{P(u)}{P(\lambda u)} .
\]
The sign of \(R'\) in the interior is the sign of
\[
Q(u)=a(a-1)-2a(1+\lambda)u-(a-1)\lambda u^2 .
\tag{2}
\]
Indeed the derivative numerator of \(P(u)/P(\lambda u)\) is \((1-\lambda)Q(u)\). For interior \(\lambda\), \(Q\) is strictly decreasing on \([0,a]\): for negative \(\lambda\), \(a(1+\lambda)+(a-1)\lambda u\ge a(1+a\lambda)>0\), and for positive \(\lambda\) the inequality is immediate. We have \(Q(0)>0\) and \(Q(a)=-a(a+1)(1+a\lambda)<0\). Let
\[
J(u)=R(u)\Psi'(u)-\lambda\Psi'(\lambda u).
\]
Then \(J(0)=0\), \(J'=R'\Psi'\), and \(J(a^-)=-\lambda\Psi'(\lambda a)<0\), because \(R(u)\Psi'(u)\to0\). Thus \(J\) changes sign once, from positive to negative. The derivative of \(s_\lambda'(\Psi(u))\) has the sign of \(J\), giving the unique inflection. Also \(s_\lambda'(0^+)=\lambda^2\) and \(s_\lambda'(B^-)=0\).

Now \(W(x)=x s_\lambda'(x)-s_\lambda(x)\) has \(W(0)=0\) and \(W'=x s_\lambda''(x)\). It first increases, then decreases to \(-s_\lambda(B)<0\). Its unique interior zero is \(\tau\). Accordingly \(s_\lambda(x)/x\) increases and then decreases, peaking only at \(\tau\), with \(\eta>\lambda^2\). The right side of (1) is a concave majorant, and any concave majorant must cover the straight chord between \(0\) and \(\tau\) as well as the graph thereafter. This proves (1). At the coloring endpoint, \(R(u)=(1+u)/(a^2+u)\) is strictly increasing. Since \(\lambda\Psi'(\lambda u)/\Psi'(u)\) is the weighted average of \(R(v)\) over \(0<v<u\) with weight \(\Psi''(v)>0\), the profile is strictly convex, which gives the entire chord. \(\square\)

## 2. The opposite boundary is supported on as few letters as entropy allows

Let \(V_k\) be the probability vector uniform on \(k\) letters and zero elsewhere. At input entropy \(h=\log k\), the largest output entropy is \(H(T_\lambda V_k)\), attained only at permutations of \(V_k\). For \(\log k<h<\log(k+1)\), the largest output entropy is attained uniquely up to permutation at
\[
p=\left(t,\underbrace{\frac{1-t}{k},\ldots,\frac{1-t}{k}}_{k},0,\ldots,0\right),
\qquad 0<t<1/(k+1),\qquad H(p)=h .
\tag{3}
\]
The defining entropy is strictly increasing in \(t\). Hence these formulas specify the upper pointwise boundary \(G_\lambda(h)\) for every \(h\). Together with the known lower scalar boundary, these give the entire range at fixed \(h\): on the sorted simplex the entropy level is path connected. To see this, mix two sorted vectors on the level, then along the segment from each mixture toward the first pure vertex take the unique point of entropy \(h\). Entropy decreases strictly toward that vertex by majorization, and the chosen point varies continuously by uniqueness and compactness. The endpoint levels themselves are trivial.

**Extremum proof.** Let \(c=(1-\lambda)/q>0\), \(\phi(t)=-t\log t\), \(g(t)=\phi(c+\lambda t)\). The output entropy objective is \(\sum_i g(p_i)\). For a maximizer of nontrivial entropy on its own support, if all the positive coordinates are equal, it is \(V_k\) at a knot. Otherwise, the mass and input entropy gradients are linearly independent on this open face. Lagrange multipliers imply that every positive coordinate solves \(g'(t)-\gamma\phi'(t)=\mathrm{constant}\). The ratio
\[
r(t)=g''(t)/\phi''(t)=\frac{\lambda^2t}{c+\lambda t}
\]
is strictly increasing for \(0<t<1\), including at the coloring endpoint. Thus the derivative of \(g'-\gamma\phi'\) can change sign only once and the equation has at most two roots. If the roots on the support are \(t<T\), then \(\gamma\) is the strictly intermediate weighted average of \(r\) on \([t,T]\) with weight \(-\phi''>0\). If \(t\) were repeated, the difference of two such coordinates is a tangent vector to both constraints. The Lagrangian has strictly positive second derivative along that tangent, since \(\phi''(t)(r(t)-\gamma)>0\). This contradicts the necessary second-order condition for a local maximum on the smooth constraint surface. Hence there is exactly one small coordinate. A nonuniform extremizer on a support of \(k+1\) then has entropy strictly between \(\log k\) and \(\log(k+1)\), and (3) is forced. Existence follows from compactness. The cases \(h=0,B\) follow directly from the entropy endpoints. \(\square\)

### The exact upper conditional polygon

For each \(k=1,\ldots,q-1\), \(G_\lambda\) is strictly convex within the interval \((\log k,\log(k+1))\), except that it is affine on the first interval for the coloring channel. Indeed, restrict (3) to its \(k+1\) possible letters. They carry total output probability \(M=(k+1)c+\lambda>0\), and after renormalization their output is the \(k+1\)-letter Potts transform with parameter \(\ell=\lambda/M\in[-1/k,1)\). The other output masses are constant. The input in this interval is a *one-dip* profile in the \(k+1\)-letter alphabet: the corresponding \(\Psi\) has \(a=k\) and argument \(u\in(-1,0)\). Formula (2) for this alphabet gives \(Q_\ell(u)>0\): the constant and the quadratic term together are positive if \(k>1\) and \(\ell\ge0\), because \(k>\ell u^2\), while all nonzero terms are nonnegative for negative \(\ell\). The linear term is strictly positive unless \(\ell=-1\). If \(k=1\) and \(\ell>-1\), it alone gives strictness. Therefore \(R(u)\) is strictly increasing in \(u<0\), or strictly decreasing as the deviation \(-u>0\) grows. The weighted-average argument for the derivative now gives a strictly concave deficit profile on that one-dip ray. Reversing the input deficit coordinate and subtracting it from the constant output entropy makes \(G_\lambda\) strictly convex. If \(k=1,\ell=-1\), the effective binary transform swaps its two inputs and gives the asserted affine exception.

The chords of the knots \((\log k,H(T_\lambda V_k))\) form a strictly cornered concave polygon. To see the ordering of its slopes, allow \(k=e^x\) in the formula for the knots, and put \(z=\lambda/(c e^x)>-1\). Up to a constant independent of \(x\) the ordinate is \(-(c e^x+\lambda)\log(1+z)\), whose second derivative is
\[
c e^x\left(\frac z{1+z}-\log(1+z)\right)<0
\]
for \(x>0,\lambda\ne0\). The strict sign follows by differentiating \(\log(1+z)-z/(1+z)\), which has its unique minimum zero at \(z=0\). Continuity handles the coloring endpoint \(x=0\). The polygon majorizes the convex interval arcs, and any concave majorant must cover each chord, so it is the least concave majorant \(G_\lambda^{\rm conc}\).

For a single letter observed through \(T_\lambda\) after arbitrary side information \(U\), the exact region at \(h=H(X\mid U)\) is
\[
 B-\widehat s_\lambda(B-h)
 \ \le\ H(Y\mid U)\ \le\
 G_\lambda^{\rm conc}(h).
\tag{4}
\]
Both are attained even when the unconditional marginal of \(X\) is required to be uniform: use convex combinations of the extremizing posteriors with symbol permutations averaged uniformly, then time-share. The entire vertical interval is obtained by mixing the two sharp constructions at the same \(h\).

For the lower boundary in (4), in deficit coordinates above \(\tau\) all posteriors must be one-spike with that same deficit; below \(\tau\), they must be uniform or one-spike of deficit \(\tau\), in the indicated proportions. At \(\tau\) all have that deficit. For the upper boundary between adjacent knots, all posteriors must be uniform on \(k\) or \(k+1\) letters, in the associated proportions, except that on the first interval of the coloring channel any posteriors supported on at most two letters are allowed. At a knot all posteriors must have that knot's entropy and support type. These statements follow from the pointwise equality cases and the exact contact sets and affine portions of the envelopes; any additional unconditional marginal constraint also requires the posteriors to average to that marginal.

## 3. Finite blocks: all equalities and a convergence refinement

Let \(Y^n\) be the output under \(T_\lambda^{\otimes n}\) from an arbitrary input \(X^n\). Put \(x=B-H(X^n)/n\). The known sharp asymptotic lower bound on output entropy reads
\[
B-H(Y^n)/n\le\widehat s_\lambda(x).
\tag{5}
\]
For every finite \(n\), equality in (5) forces independence of *all* input coordinates. In fact the chain rule proof first uses \(H(Y_i\mid Y^{i-1})\ge H(Y_i\mid X^{i-1})\), by the memoryless Markov relation. If equality holds, strict concavity of entropy forces \(T_\lambda P_{X_i\mid X^{i-1}=v}\) to be identical for all prefix values \(v\) that can produce a common \(Y^{i-1}\) value. Any two supported prefixes have a common such output: for an interior channel all entries are positive, and at the coloring endpoint at most two letters are excluded at each coordinate, leaving at least one. Invertibility of \(T_\lambda\) on the probability simplex (\(\lambda\ne0\)) gives equality of the input conditional distributions at all prefixes. Applied to each coordinate, this is independence. Subsequent steps of the chain bound use only the pointwise optimum and concavity of \(\widehat{s}_\lambda\).

Consequently, for \(x\ge\tau\), every equality law is a product of one-spike extremizers all of deficit \(x\), with arbitrary spike positions. For \(x<\tau\), the equality laws are exactly products with \(nx/\tau\) factors of deficit \(\tau\) and the rest uniform. If \(nx/\tau\) is not an integer, (5) is strictly unattainable at that fixed \(n,x\); compactness gives a positive gap to the optimum. For the coloring channel the active factors in this statement are point masses. As a simple strict check, take \(q=3,\lambda=-1/2,n=2\) and \(X_1=X_2\) uniform. Then \(H(X^2)=\log3\), the output law has three diagonal probabilities \(1/6\) and six off-diagonal probabilities \(1/12\), and its entropy \(\log(6\sqrt2)\) is greater than the achievable \(\log6\) from an independent pure/uniform pair.

There is a sharper approximation in the linear segment for an interior channel. Write \(S_n(x)\) for the maximal output deficit per letter at exactly the input deficit \(x\) per letter. Fix \(0<x<\tau<B\). Choose an integer \(r\) closest to \(nx/\tau\); for all large \(n\), \(1\le r\le n\). Use \(r\) equal active scalar deficits \(d=nx/r\), and \(n-r\) uniform factors. Put \(\gamma(t)=\eta t-s_\lambda(t)\). This function is nonnegative, with \(\gamma(\tau)=\gamma'(\tau)=0\), so if \(C\) bounds \(\gamma''\) near \(\tau\), Taylor's theorem gives
\[
0\le\widehat s_\lambda(x)-S_n(x)
   \le \frac{r}{n}\gamma(d)
   \le \frac{C\tau^2\,{\rm dist}(nx/\tau,\mathbb Z)^2}{2nr}.
\tag{6}
\]
Thus the gap is \(O(n^{-2})\) for fixed \(x\) in the interior of the affine segment. At the coloring endpoint, using pure and uniform factors plus at most one residual scalar deficit gives \(O(n^{-1})\). These are achievable approximations, not claimed optimal convergence rates.

Within the **product-input subclass**, for interior \(\lambda\) and fixed \(0<x<\tau\), every optimizer for all sufficiently large \(n\) uses \(r\) equal nonzero scalar deficits and otherwise zero deficits, with \(r\in\{\lfloor nx/\tau\rfloor,\lceil nx/\tau\rceil\}\); choose whichever gives the larger objective (or both if tied). To prove this, minimize \(\sum_i\gamma(x_i)\) subject to \(\sum_i x_i=nx\). By (6) its minimum is \(O(n^{-1})\). Every \(\gamma(x_i)\) is nonnegative and the only zeros of \(\gamma\) are \(0,\tau\), so all coordinates are within any prescribed small neighborhoods of these zeros for large \(n\). Choose the neighborhoods so that \(\gamma'\) on the first is strictly larger than every \(\gamma'\) on the second (using \(\gamma'(0^+)=\eta-\lambda^2>0=\gamma'(\tau)\)) and \(\gamma''>0\) in the second. Some coordinate belongs to the second neighborhood, since \(x>0\) is fixed. Moving any positive small deficit toward an active one decreases the objective, so the small deficits are zero. Strict convexity near \(\tau\) and averaging make the active deficits equal. For real \(r\), the derivative of \(r\gamma(nx/r)\) is \(W(nx/r)\), which is negative below \(nx/\tau\) in the \(r\) coordinate and positive above; this leaves only the two stated integers. For the coloring channel, \(s_\lambda\) is strictly convex, so within products a perturbation between any two strictly interior deficits can improve the objective. Consequently for every \(n\) the optimum among products uses as many pure factors as the deficit budget permits, at most one residual factor, and the rest uniform. None of these product-only assertions proves that an unrestricted nonattaining finite-block optimizer is a product.

For \(\lambda=0\) the output is uniform, and for \(\lambda=1\) it equals the input; both give equality at their respective trivial bounds without the nontrivial equality restrictions.

## Exact examples

The [Python checker](verify_factor_potts_entropy_envelopes.py) checks the algebra at rational specializations and encloses logarithms using a positive power series with a rational remainder. In units of \(10^{-9}\), the certified brackets below list consecutive lower/upper numerators for the bend, the tangency deficit, and its slope.

| \(q,\lambda\) | Bend | Tangency | Slope |
|---|---|---|---|
| \(3,1/2\) | 57745682–57745683 | 102854836–102854837 | 256493476–256493477 |
| \(3,-1/4\) | 250870415–250870416 | 420828230–420828231 | 71809561–71809562 |
| \(4,1/2\) | 137093790–137093791 | 244987566–244987567 | 265671889–265671890 |
| \(4,-1/4\) | 702929577–702929578 | 1042072294–1042072295 | 91693197–91693198 |

Reproduce with normal Python 3: `python3 verify_factor_potts_entropy_envelopes.py`. No numerical grid establishes any general optimality or equality assertion.
