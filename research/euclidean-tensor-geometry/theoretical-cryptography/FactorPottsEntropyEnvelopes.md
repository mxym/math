# Both conditional-entropy envelopes of a q-ary symmetric channel

For \(q\ge3\), let \(u_q\) be uniform on \(q\) symbols and consider the
channel
\[
                 T_\lambda p=\lambda p+(1-\lambda)u_q,
       \qquad -1/(q-1)\le\lambda\le1 .
\]
All entropies use natural logarithms. Write \(a=q-1\) and
\[
 P_t=\left(\frac{1+at}{q},\frac{1-t}{q},\ldots,\frac{1-t}{q}\right),
 \qquad D_q(t)=D(P_t\Vert u_q),\qquad -1/a\le t\le1 .
\]
We describe the sharp minimum and maximum of \(H(Y|U)\) at every
\(h=H(X|U)\) for \(U-X-Y\) and \(X\to Y=T_\lambda\), with no extra
restriction on \(U\). Both are attainable even with \(X\) uniform.

**Lower envelope.** Gu–Polyanskiy identify the one-letter minimum
by the profile \(s_\lambda(D_q(t))=D_q(\lambda t)\), \(0\le t\le1\),
and characterize the entropy lower bound by the concave envelope
\(\widehat s_\lambda\).
For all \(-1/a<\lambda<1\), \(\lambda\ne0\), we give the explicit shape:
\(s_\lambda\) has exactly one inflection, and its concave envelope
is the line from zero to its unique positive tangency point, followed
by \(s_\lambda\) itself. At \(\lambda=-1/a\), the whole envelope is
the chord from zero to the endpoint. The sharp entropy minimum is
\[
               \log q-\widehat s_\lambda(\log q-h).
\]

**Upper envelope.** For pointwise input entropy
\(\log(k-1)<h<\log k\), the maximum output entropy is attained
exactly, up to permutation in the nontrivial noise cases, at an input
with \(k-1\) equal larger positive masses, one smaller positive mass,
and all other coordinates zero. At \(h=\log k\) it is attained by the
uniform law on \(k\) symbols. The sharp conditional entropy maximum
is obtained by linear interpolation between the \(q\) values at
\(h=\log k\) of those uniform laws, with no further envelope search.

The pointwise minimum and the concavification principle are prior
results of [Gu–Polyanskiy, Theorem 3 and Proposition 17](https://arxiv.org/abs/2005.05444);
their Proposition 25 also proves a linear piece near the origin.
See [Witsenhausen](https://doi.org/10.1109/TIT.1974.1055285) for
convexification in discrete-channel entropy inequalities.
We do not count those results as new. The refinements here are the
complete shape of the lower envelope, its extreme-negative-noise
asymptotic, and the explicit reverse pointwise and conditional curves.
We do not assert a reverse tensorization statement for correlated
multi-symbol inputs, or treat general nonsymmetric noises.

## 1. A rational derivative ratio

For an alphabet size \(a+1\), put
\[
 \ell(t)=\log\frac{1+at}{1-t},\qquad
 F(t)=(1+at)(1-t)=1+(a-1)t-at^2 .
\]
Then \(D_q'(t)=a\ell(t)/q\) and \(\ell'(t)=q/F(t)\).
For \(t\ne0\) in the interior, the derivative of \(D_q(\lambda t)\)
as a function of \(D_q(t)\) is
\[
 R(t)=\frac{\lambda\ell(\lambda t)}{\ell(t)},\qquad
 J(t)=\frac{\lambda^2\ell'(\lambda t)}{\ell'(t)}
     =\lambda^2\frac{F(t)}{F(\lambda t)}.
\]
Both ratio formulas extend continuously to \(t=0\) with value
\(\lambda^2\). On \(t>0\), \(R(t)\) is the weighted average of \(J\)
on \([0,t]\) with weight \(\ell'\); on \(t<0\) it is the same average
on \([t,0]\). Direct differentiation gives
\[
 J'(t)=\frac{\lambda^2(1-\lambda)}{F(\lambda t)^2}
 \left[(a-1)-2a(1+\lambda)t-a(a-1)\lambda t^2\right].       \tag{1}
\]

## 2. The unique tangent on the lower side

Let \(a\ge2\). For \(-1/a<\lambda<1,\lambda\ne0\), the polynomial
in brackets in (1) is strictly decreasing on \([0,1]\).
For \(\lambda\ge0\) this follows termwise. For \(\lambda<0\)
its derivative is at most \(-2a(1+a\lambda)<0\).
Its endpoint values are \(a-1>0\) and
\(-(a+1)(1+a\lambda)<0\). Thus \(J\) has exactly one maximum there.
The sign of \(R'(t)\) is the sign of
\[
       J(t)\ell(t)-\int_0^t J(v)\ell'(v)\,dv .
\]
The derivative of this difference is \(J'(t)\ell(t)\).
It starts at zero, first increases and then decreases. Near \(t=1\),
\(J(t)\ell(t)\to0\) because \(F(1)=0\) and \(F(\lambda)>0\),
whereas the integral tends to \(\lambda\ell(\lambda)>0\).
Thus \(R'\) switches sign once, from positive to negative. Since
\(D_q\) increases on \([0,1]\), \(s_\lambda\) is strictly convex
and then strictly concave, with one inflection.

Let \(L_q=\log q\). The derivative of \(x s'_\lambda(x)-s_\lambda(x)\)
is \(x s''_\lambda(x)\); again it starts at zero, first increases
and then decreases. As \(x\uparrow L_q\), \(s'_\lambda(x)\to0\),
so the difference ends at \(-s_\lambda(L_q)<0\).
It has a unique zero \(x_*\in(0,L_q)\), strictly past the inflection.
Equivalently the unique \(t_*\in(0,1)\) satisfies
\[
   x_*=D_q(t_*),\qquad
   R(t_*)=\frac{D_q(\lambda t_*)}{D_q(t_*)}=:\eta_\lambda .  \tag{2}
\]
The line \(\eta_\lambda x\) dominates \(s_\lambda(x)\) up to
\(x_*\), since \(s_\lambda(x)/x\) increases to that point.
Joining this line to \(s_\lambda\) at \(x_*\) gives a concave
majorant, and any concave majorant must dominate that chord and
dominate \(s_\lambda\) beyond it. This proves the exact envelope.

At \(\lambda=-1/a\), the bracket in (1) equals
\((a-1)(1-t)^2\); \(J\) is strictly increasing on \(0<t<1\).
So \(R\) is strictly increasing too, and \(s_\lambda\) is
strictly convex all the way to \(L_q\).
Its concave envelope is the full chord of slope
\[
                         \eta_-=\frac{\log(q/(q-1))}{\log q}.
\]
The cases \(\lambda=0,1\) give \(s_0=0\) and \(s_1(x)=x\).

The tangency point approaches the endpoint at a power-law scale
as \(\lambda=-1/a+\epsilon\downarrow-1/a\), with \(q\) fixed:
\[
 \gamma=\frac{1}{a\eta_-}>1,\qquad
                 1-t_*\ \sim\ q\left(\frac{a^2}{q}\right)^\gamma
                                    \epsilon^\gamma .       \tag{3}
\]
To prove this, the ratios \(D_q(\lambda t)/D_q(t)\), extended at
zero by \(\lambda^2\), converge uniformly on \([0,1]\) to their
endpoint-\(\lambda\) counterpart. This follows from continuity
away from zero and the uniform quadratic expansion near zero.
At the endpoint noise their ratio strictly increases, so its
unique maximizer is \(t=1\); hence \(t_*\to1\).
From the bound \(D_q(\lambda t)-D_q(-t/a)=
O_q(\epsilon\log(1/\epsilon))\) uniformly in \(t\), and \(t_*\)
bounded away from zero, we get
\(\eta_\lambda=\eta_-+O_q(\epsilon\log(1/\epsilon))\),
by comparing the two maxima and the value at \(t=1\).
The displayed bound on \(D_q\) follows termwise from the modulus
of \(x\log x\) on a fixed bounded nonnegative interval.

Now put \(z=1-t_*\) and \(r=-\lambda=1/a-\epsilon\).
Equation (2) reads
\[
     \log\frac{1+at_*}{z}
      =\frac{r}{\eta_\lambda}
         \log\frac{1-\lambda t_*}{a\epsilon+(1-a\epsilon)z}.
\]
Here \(r/\eta_\lambda=\gamma+O_q(\epsilon\log(1/\epsilon))\).
Also \(a\log(1+1/a)<1<\log q\), giving \(\gamma>1\).
If \(z\) were bounded below by a positive multiple of \(\epsilon\)
along some sequence, both logarithms apart from the factor
\(r/\eta_\lambda\) would equal \(\log(1/z)+O_q(1)\), a contradiction.
Thus \(z=o(\epsilon)\), and the equation becomes
\(\log(q/z)=\gamma\log(q/(a^2\epsilon))+o(1)\).
Exponentiating proves (3).

## 3. The reverse pointwise optimum

Write \(c=(1-\lambda)/q\). Consider \(\lambda\ne0,1\).
Fix \(0<h<\log q\) and maximize \(\sum_i -(\lambda p_i+c)
\log(\lambda p_i+c)\) subject to \(\sum_i p_i=1\) and \(H(p)=h\).
A maximum exists by compactness. Work inside its positive support,
a relative face; the objective is smooth there. This remains true
at \(\lambda=-1/(q-1)\) because \(h>0\) implies every \(p_i<1\).

If the positive masses are not all equal, the two constraints
are regular on this face. Lagrange multipliers give a common
value for
\[
                 \lambda\log(\lambda p_i+c)-\theta\log p_i.
\]
Its derivative with respect to \(\log p_i\) is
\(\lambda^2 p_i/(\lambda p_i+c)-\theta\), strictly increasing
in \(p_i\). There can be at most two positive levels \(x<y\).
Comparing the two equations shows that
\(\theta\) is strictly between
\(\lambda^2x/(\lambda x+c)\) and \(\lambda^2y/(\lambda y+c)\)
(by the mean value theorem in \(\log p\)).
The diagonal entries of the Hessian of the constrained objective
at a mass \(p_i\) are
\(\theta/p_i-\lambda^2/(\lambda p_i+c)\); they are strictly
positive at the smaller level \(x\).
If two smaller entries occurred, perturbing these entries in
opposite directions is a tangent vector to both constraints,
with strictly positive second variation. This contradicts a
maximum by the second-order necessary condition on a regular
constraint manifold. So there is exactly one smaller positive
mass; the other positive masses are equal.

On support size \(k\ge2\) with one smaller entry, its entropy
ranges strictly between \(\log(k-1)\) and \(\log k\).
Indeed, with smaller entry \(v\in(0,1/k)\), increasing \(v\)
strictly increases entropy between those limits
(the \(k-1\) other entries are \((1-v)/(k-1)\)).
Thus \(h\) determines the support size and the mass parameter
uniquely. If \(h=\log k\), a different support cannot be uniform
at that entropy, and the two-level shape on any support has
entropy strictly between successive logarithms.
The maximizing input must be uniform on exactly \(k\) symbols.
The endpoints \(h=0,\log q\) are immediate.
This proves the stated complete reverse pointwise formula.

## 4. The exact upper conditional polygon

Take the pointwise maximizing family from §3 with support size \(k\).
Its active coordinates can be written as the \(k\)-symbol
\(P_t\) with singled-out smaller entry and \(-1/(k-1)\le t\le0\),
and other coordinates zero.
The total output mass on the same support is \(m=\lambda+kc>0\)
for \(k\ge2\), including at the extreme negative noise.
The normalized distribution on that support goes through
the \(k\)-symbol symmetric channel with parameter
\(\rho=\lambda/m\) in \([-1/(k-1),1)\).
The other \(q-k\) output masses are constants \(c\).
Consequently input entropy and output entropy on this arc are
\[
                    \log k-D_k(t),\qquad C-m D_k(\rho t),
\]
where \(C\) is constant on the arc.

Apply (1) now with \(a=k-1\) and \(\lambda=\rho\) to \(t<0\).
The bracket is nonnegative, strictly positive except for
\(k=2,\rho=-1\). To check this, for \(\rho\ge0\) bound
\(a\rho t^2\le\rho/a\le1\) in the first and last terms;
the middle term is positive. For \(\rho<0\), all three terms
are nonnegative, and the middle is positive unless \(\rho=-1\);
that case forces \(k=2\).
When the derivative is strict, \(J(t)\) is increasing and
its weighted average \(R(t)\) on \([t,0]\) also increases in
\(t\) (differentiate the ratio, or remove an initial part
of the interval). The slope of output versus input entropy
is \(mR(t)\), and input entropy increases in \(t\).
Thus each arc is convex, strictly apart from the stated
permutation case where the arc is affine.
In the global channel this exception is exactly \(k=2\) and
\(\lambda=-1/(q-1)\).

It remains to see that none of the vertices need to be dropped.
For real \(k\ge1\), the continuous interpolation of the
uniform-support vertex expression is
\[
 \psi(\log k)=-\log c-(kc+\lambda)\log(1+\lambda/(kc)).
\]
At a zero weight use the continuous boundary value.
Writing \(x=\lambda/(kc)\), its second derivative with respect
to \(\log k\) is
\[
                    -kc\,\big[\log(1+x)-x/(1+x)\big]<0 .
\]
The bracket has derivative \(x/(1+x)^2\) and unique minimum zero
at \(x=0\), so it is positive wherever needed.
At the negative endpoint with \(k=1\) the continuous extension
still gives concavity and strictly decreasing secant slopes.
Hence the secants between the integer \(k\)'s make a concave
polygon. It dominates each convex arc; every concave majorant
must dominate the secants between these exact vertices.
It is therefore the upper concave envelope.

## 5. Passing to conditional laws

Conditioning on \(U\) mixes the one-letter entropy pairs.
The convex lower and concave upper envelopes give the two
bounds by Jensen's inequality, and the scalar chords specify
the necessary mixtures of at most two types of input laws.
In the lower case use the known pointwise extremizers \(P_t\);
in the upper case use uniform laws on successive supports.
To impose a uniform \(X\)-marginal if desired, also choose a
uniform independent permutation of the alphabet and include
it in \(U\); entropy is unchanged and the channel commutes
with the permutation. Each mixture is thus attainable with
uniform \(X\), and mixing the two constructions at the same
\(h\) gives all intermediate output conditional entropies.
The identity and completely randomizing channels are
immediate, with output entropy \(h\) and \(\log q\) respectively.
The lower multiletter implication can be read using the
existing tensorization of Gu–Polyanskiy; no reverse
multiletter assertion is used here.

The [companion check](verify_factor_potts_entropy_envelopes.py)
uses exact rational calculations for (1), and rigorous
rational enclosures of logarithms for selected chord and
tangency tests. The single-switch proofs and compactness
argument above, not these samples, prove the envelopes.
