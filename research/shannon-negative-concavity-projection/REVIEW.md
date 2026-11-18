# Independent checks

An independent internal AI reviewer re-derived the scale density, projection-entropy limit and truncation step. This is not external peer review. The following separate argument addresses the passage to the entropy limit, which does **not** follow from convergence in distribution alone.

Use the notation of [the proof](PROOF.md) and fix $u\ne0$. The joint density of the rescaled scale logarithm $z$ and the angular logarithm $b$ is
$$
J_\varepsilon(z,b)=q_\varepsilon(z)k_{A_\varepsilon(z)}(b).
$$
It converges a.e. to $J_0(z,b)=q(z)k_{A(z)}(b)$; values at $z=0,C$ and at endpoints of uniform marginal densities do not affect the integrals. All are dominated by $K e^{-z+b}\mathbf1_{z\ge0,\ b\le\log B}$ for constants depending on $D,u$. In particular the convergence is in $L^1$, also after multiplication by $1+|b|$.

Shear by $(z,b)\mapsto(z+\varepsilon b,b)$, a determinant-one linear map. The distance from the sheared $J_\varepsilon$ to $J_0$ in $L^1$ is at most
$$
\|J_\varepsilon-J_0\|_1+\int \|J_0(\cdot-\varepsilon b,b)-J_0(\cdot,b)\|_1\,db=o(1).
$$
The second term tends to zero by continuity of translations in $L^1$ for a.e. $b$ and domination by $2\|J_0(\cdot,b)\|_1$. Marginalizing gives $F_\varepsilon\to q$ in $L^1$. The exponential envelope $F_\varepsilon(w)\le K'e^{-|w|}$ in the main proof then yields entropy convergence: every sequence admits an a.e.-convergent subsequence along which $|F_\varepsilon\log F_\varepsilon|$ is dominated by an integrable constant times $e^{-|w|/2}$. This applies separately to each direction, including the coordinate axes.

Other checks:

* The layer weights include the rectangle's area. There is no missing atom at $r=1$ because the layer integral from one upwards has value one on the set where $P=1$. The density parameter is $-1/(2+\varepsilon)$ and the *measure* parameter is $-1/\varepsilon$.
* The common divergent term $E[Z]/\varepsilon$ uses the scale distribution at the actual $\varepsilon$. Cancel it before comparing directions. For an independent angular check, averaging the power series for $\operatorname{arctanh}$ gives, for $0<t<1$,
  $$
  E\log|U+tV|=-1+\sum_{j\ge1}\frac{t^{2j}}{(2j-1)2j(2j+1)}.
  $$
  Indeed the derivative of $E\log|U+z|$ is $\operatorname{arctanh} z$ for $|z|<1$; integrate the series and use $E[V^{2j}]=1/(2j+1)$. Exchanging the two uniforms shows that the wide and narrow diagonal angular means differ by $\log D$ exactly. This confirms the claimed lower bound on the limiting ratio without numerical quadrature.
* Conditional restriction is to convex rectangles of probability tending to one. Each projected density is eventually at most twice its original density; the latter has finite absolute entropy and is bounded. Splitting at $1/(2e)$ supplies a dominating integrable function. One sufficiently large rectangle works for the three directions in the strict inequality, and boundedness and compact support give finite entropies in every nonzero direction.
* [verify.py](verify.py) checks rational identities for the limiting angular weights and the sign of the angular correction. Run `python3 verify.py` and `sha256sum -c SHA256SUMS` in this directory. These checks do not supply a numerical error bound in $\varepsilon$ and are not a formal verification of a limit theorem.
