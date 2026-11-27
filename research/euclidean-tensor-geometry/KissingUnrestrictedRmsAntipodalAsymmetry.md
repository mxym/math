# Unrestricted RMS antipodal asymmetry above 72 and 126 kissing points

Take **any** kissing code of the indicated size on the unit sphere and pair its points in any fashion, leaving just one point unpaired when the size is odd. For every pair put $h_i=\|x_i+y_i\|/2$: this is zero at an exact antipode. Even for the *best* pairing the root-mean-square value $h=(p^{-1}\sum_i h_i^2)^{1/2}$, $p=\lfloor N/2\rfloor$, satisfies these strict lower bounds.

| Dimension | Points $N$ | RMS $h$ strictly exceeds |
|---:|---:|---:|
| 6 | 73, 74, 75, 76 | .0360, .0512, .0540, .0681, respectively |
| 7 | 127, 128, 129, 130, 131, 132 | .0215, .0306, .0339, .0420, .0429, .0500, respectively |

For example, the RMS angular departure from $180^\circ$ exceeds $0.072$ radians (about $4.13^\circ$) with 73 points, and $0.043$ radians (about $2.46^\circ$) with 127. For 76 and 132 points the respective angular lower bounds are $0.1362$ and $0.1000$ radians. Indeed the angular departure is $2\arcsin h_i\ge2h_i$. There is **no** point-group, equator, root system, assumed matching quality, or exact-antipode hypothesis. This constrains hypothetical codes; it does not prove they exist or lower the unrestricted maximum cardinalities.

The [earlier tail estimates](KissingNearAntipodalTail.md) exclude specified *numbers* of pairs all meeting a uniform tolerance. Here one very bad pair cannot simply be discarded: the conclusion controls the **sum of squared defects** of every pairing. Even its maximum-defect corollary strengthens the earlier full-pairing tolerances .0307 and .0184 at the two first-excess sizes. For broader interval methods see [Musin](https://arxiv.org/abs/2309.13854). The proof uses the classical [spherical addition formula](https://doi.org/10.1007/BF03187604); its special step is to retain the common vector sum of the pair midpoints, which couples two error terms instead of treating every error as independently worst possible.

## 1. Homogeneous energy without a near-pair assumption

Let $P=36$ in dimension six and $63$ in dimension seven, and $c=3/(4P)$. For $f(t)=t^4-t^2/4$, the constant spherical coefficient is $c$ and all positive-degree coefficients are nonnegative: the degree-two coefficient has the sign of $6/(d+4)-1/4$, and the degree-four coefficient is positive. Homogenize:
$$
 F(v,w)=(v\cdot w)^4-\tfrac14\|v\|^2\|w\|^2(v\cdot w)^2.
$$
For nonnegative weights $s_i$, the addition formula on the normalized nonzero vectors, with weights $s_i\|v_i\|^4$, gives
$$
 \sum_{ij}s_is_jF(v_i,v_j)\ge c\left(\sum_i s_i\|v_i\|^4\right)^2 .
$$
Zero vectors contribute nothing. Write each original pair as $m_i\pm a_i$ with $h_i=\|m_i\|$, $\|a_i\|^2=1-h_i^2$, and put $E=\sum_i h_i^2=p h^2$, $M=\sum_i m_i$. Apply the homogeneous inequality to the $a_i$ with unit weight, and to the optional unpaired unit vector $z$ with a weight $b>0$ (put $b=0$ when $N$ is even). Jensen's inequality gives the lower bound $c[p(1-h^2)^2+b]^2$. The diagonal is at most
$$
 \tfrac34[p-4E+6E^2+b^2],
$$
since $(1-h_i^2)^4\le1-4h_i^2+6h_i^4$ and $\sum h_i^4\le E^2$.

## 2. Interactions between pairs

Fix $i\ne j$. Let $u=h_i h_j$, $v=m_i\cdot m_j$ and $S_i=h_i^2$. The four original kissing inequalities imply $|a_i\cdot a_j|\le1/2-v$ by averaging same and opposite signs separately. Hence
$$
 F(a_i,a_j)\le(1/2+u)^2 D_{ij},\qquad
 D_{ij}=(S_i+S_j)/4+u/4-3v/4+3u^2/4.
$$
Indeed the positive part of the quadratic bracket before multiplying by $(a_i\cdot a_j)^2$ is at most $[-v+(S_i+S_j)/4+3u^2/4]_+$. For $-u\le v\le u$, convexity gives $[u/2-v]_+\le3(u-v)/4$, and $S_i+S_j\ge2u$. This yields the displayed nonnegative upper bound.

In the constant $1/4$ part of $(1/2+u)^2$, sum $D_{ij}$ over ordered distinct pairs. Use $\sum_{i\ne j}u\le(p-1)E$ and, crucially, $\sum_{i\ne j}v=\|M\|^2-E$. For the remaining $u+u^2$ part use $u\le E/2$ and $D_{ij}\le (S_i+S_j)/4+u+3u^2/4$. Here
$$
 \sum_{i\ne j}u(S_i+S_j)\le 2(\sum h_i^3)(\sum h_i)\le2\sqrt p E^2,\qquad
 \sum_{i\ne j}u^2\le E^2.
$$
It follows, with $K=\lceil\sqrt p\rceil$, that the total ordered off-diagonal pair–pair contribution is at most
$$
 \frac3{16}(pE+E^2-\|M\|^2)
 +(1+E/2)(1+K/2+3E/8)E^2. \tag{1}
$$

## 3. Interaction with the optional singleton

Put $v_i=m_i\cdot z$. From $|a_i\cdot z|\le1/2-v_i$ one gets
$$
 F(a_i,z)\le (1/2+h_i)^2\bigl[(-v_i)_++5h_i^2/4\bigr]
 \le (h_i-v_i)/8+(21/16)h_i^2+(9/4)h_i^3+(5/4)h_i^4.
$$
For the second inequality use $(-v_i)_+\le(h_i-v_i)/2$, and bound $(h_i-v_i)/2\le h_i$ in its higher-order terms. To keep the scalar sum sharp, consider $g(s)=\sqrt{s}/8+(9/4)s^{3/2}+(5/4)s^2$. Its tangent at $s=h^2$ dominates it throughout $0\le s\le E$ whenever
$$
 \frac1{16h}\ge\frac94(K+1/2)h+\frac54(K+1)^2h^2. \tag{2}
$$
Indeed, dividing tangent minus function by $(\sqrt s-h)^2$ gives $1/(16h)-(9/4)(\sqrt s+h/2)-(5/4)(\sqrt s+h)^2$, with the ratio interpreted by continuity at $s=h^2$. Summing tangents at the average cancels the linear terms; $h=0$ follows directly. Thus the singleton sum is at most
$$
 -\langle M,z\rangle/8+p h/8+21E/16+9p h^3/4+5p h^4/4 .
$$
After multiplying by $2b$, the linear term is bounded by $b\|M\|/4$. Completing the square against the **negative** $-3\|M\|^2/16$ in (1) costs at most $b^2/12$ in total. This step needs no control of the directions of the midpoints.

## 4. Rational certificate

Combining the displayed estimates yields the necessary inequality
$$
\begin{aligned}
 c[p(1-h^2)^2+b]^2\le{}&
 \tfrac34(p-4E+6E^2+b^2)+\tfrac3{16}(pE+E^2)\\
 &+(1+E/2)(1+K/2+3E/8)E^2\\
 &+2b(ph/8+21E/16+9p h^3/4+5p h^4/4)+b^2/12 .
\end{aligned}
$$
For the odd rows in increasing dimension/cardinality use $b=.64,.43,.66,.47,.31$ for $N=73,75,127,129,131$ respectively. For the others set $b=0$ and omit (2). The [standalone rational verifier](verify-kissing-rms-antipodal-asymmetry.py) first tests (2), where needed, at the stated endpoint; it then holds everywhere below it. Substitute $E=p h^2$ and subtract the right side from the left. On each entire interval from zero to the tabulated threshold, all Bernstein coefficients of this univariate polynomial are strictly positive. The program forms the power coefficients by convolution and converts them with the exact binomial formula. This contradicts the necessary inequality throughout every interval.
